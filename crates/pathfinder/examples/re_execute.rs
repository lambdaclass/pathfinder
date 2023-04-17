use anyhow::Context;
use mimalloc::MiMalloc;
use pathfinder_common::{BlockNumber, ChainId, StorageCommitment};
use pathfinder_storage::{
    JournalMode, StarknetBlocksBlockId, StarknetBlocksTable, StarknetTransactionsTable, Storage,
};
use primitive_types::U256;
use starknet_gateway_types::reply::transaction::Transaction;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

/// Re-execute transactions in a range of blocks.
///
/// Iterates over specified blocks in the database and re-executes all transactions within
/// those blocks
///
/// Usage:
/// `cargo run --release -p pathfinder --example re_execute ./mainnet.sqlite 50000 51000`
fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .compact()
        .init();

    let database_path = std::env::args().nth(1).unwrap();
    let storage = Storage::migrate(database_path.into(), JournalMode::WAL)?;
    let mut db = storage
        .connection()
        .context("Opening database connection")?;

    let first_block = std::env::args().nth(2).unwrap();
    let first_block: u64 = first_block.parse().unwrap();

    let (latest_block, chain_id) = {
        let tx = db.transaction().unwrap();
        let latest_block = StarknetBlocksTable::get_latest_number(&tx)?.unwrap().get();
        let chain_id = get_chain_id(&tx).unwrap();
        (latest_block, chain_id)
    };

    let last_block = std::env::args()
        .nth(3)
        .map(|s| str::parse(&s).unwrap())
        .unwrap_or(latest_block);

    let (tx, rx) = crossbeam_channel::bounded::<Work>(10);

    let executors = (0..24)
        .map(|_| {
            let storage = storage.clone();
            let rx = rx.clone();
            std::thread::spawn(move || execute(storage, chain_id, rx))
        })
        .collect::<Vec<_>>();

    tracing::info!(%first_block, %last_block, "Re-executing blocks");

    for block_number in first_block..=last_block {
        let transaction = db.transaction().unwrap();
        let block_id = StarknetBlocksBlockId::Number(BlockNumber::new_or_panic(block_number));
        let block = StarknetBlocksTable::get(&transaction, block_id)?.unwrap();
        let previous_block_id =
            StarknetBlocksBlockId::Number(BlockNumber::new_or_panic(block_number - 1));
        let previous_block = StarknetBlocksTable::get(&transaction, previous_block_id)?.unwrap();
        let transactions_and_receipts =
            StarknetTransactionsTable::get_transaction_data_for_block(&transaction, block_id)?;
        drop(transaction);

        let (transactions, _): (Vec<_>, Vec<_>) = transactions_and_receipts.into_iter().unzip();

        tracing::debug!(%block_number, num_transactions=%transactions.len(), "Submitting block");

        tx.send(Work {
            block_number,
            storage_commitment: previous_block.storage_commitment,
            gas_price: block.gas_price.0.into(),
            transactions,
        })
        .unwrap();
    }

    drop(tx);

    for executor in executors {
        executor.join().expect("Executor expected to shut down");
    }

    Ok(())
}

fn get_chain_id(tx: &rusqlite::Transaction<'_>) -> anyhow::Result<ChainId> {
    use pathfinder_common::consts::{
        INTEGRATION_GENESIS_HASH, MAINNET_GENESIS_HASH, TESTNET2_GENESIS_HASH, TESTNET_GENESIS_HASH,
    };

    let genesis_hash = StarknetBlocksTable::get_hash(tx, BlockNumber::GENESIS.into())
        .unwrap()
        .context("Getting genesis hash")?;

    let chain = match genesis_hash {
        MAINNET_GENESIS_HASH => ChainId::MAINNET,
        TESTNET_GENESIS_HASH => ChainId::TESTNET,
        TESTNET2_GENESIS_HASH => ChainId::TESTNET2,
        INTEGRATION_GENESIS_HASH => ChainId::INTEGRATION,
        _ => anyhow::bail!("Unknown chain"),
    };

    Ok(chain)
}

#[derive(Debug)]
struct Work {
    block_number: u64,
    storage_commitment: StorageCommitment,
    gas_price: U256,
    transactions: Vec<Transaction>,
}

fn execute(storage: Storage, chain_id: ChainId, rx: crossbeam_channel::Receiver<Work>) {
    while let Ok(work) = rx.recv() {
        match pathfinder_rpc::cairo::starknet_rs::estimate_fee_for_gateway_transactions(
            storage.clone(),
            work.storage_commitment,
            work.transactions,
            chain_id,
            work.gas_price,
        ) {
            Ok(_) => {}
            Err(error) => {
                tracing::error!(block_number=%work.block_number, %error, "Transaction re-execution failed");
            }
        }

        tracing::debug!(block_number=%work.block_number, "Re-executed block");
    }
}
