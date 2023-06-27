use std::borrow::Cow;
use std::collections::HashMap;

use anyhow::Context;
use pathfinder_common::{
    BlockNumber, BlockTimestamp, CallParam, CallResultValue, ChainId, ClassHash, ContractAddress,
    EntryPoint, SequencerAddress, StorageAddress, StorageCommitment, StorageValue, TransactionHash,
};
use pathfinder_merkle_tree::{ContractsStorageTree, StorageCommitmentTree};
use pathfinder_storage::{CasmClassTable, ClassDefinitionsTable, ContractsStateTable};
use primitive_types::U256;
use stark_hash::Felt;
use starknet_rs::core::errors::state_errors::StateError;
use starknet_rs::definitions::block_context::{BlockContext, StarknetOsConfig};
use starknet_rs::execution::execution_entry_point::ExecutionEntryPoint;
use starknet_rs::execution::{TransactionExecutionContext, TransactionExecutionInfo};
use starknet_rs::services::api::contract_classes::compiled_class::CompiledClass;
use starknet_rs::services::api::contract_classes::deprecated_contract_class::ContractClass;
use starknet_rs::state::cached_state::CachedState;
use starknet_rs::state::state_api::{State, StateReader};
use starknet_rs::state::ExecutionResourcesManager;
use starknet_rs::storage::errors::storage_errors::StorageError;
use starknet_rs::transaction::error::TransactionError;
use starknet_rs::transaction::{
    Declare, DeclareV2, Deploy, DeployAccount, InvokeFunction, L1Handler,
};
use starknet_rs::{CasmContractClass, EntryPointType, Felt252, SierraContractClass};

use crate::v02::types::request::BroadcastedTransaction;

#[derive(Debug)]
pub enum CallError {
    ContractNotFound,
    InvalidMessageSelector,
    Internal(anyhow::Error),
}

impl From<TransactionError> for CallError {
    fn from(value: starknet_rs::transaction::error::TransactionError) -> Self {
        match value {
            TransactionError::EntryPointNotFound => Self::InvalidMessageSelector,
            TransactionError::FailToReadClassHash => Self::ContractNotFound,
            e => Self::Internal(anyhow::anyhow!("Internal error: {}", e)),
        }
    }
}

impl From<anyhow::Error> for CallError {
    fn from(value: anyhow::Error) -> Self {
        Self::Internal(value)
    }
}

pub(crate) fn call(
    storage: pathfinder_storage::Storage,
    chain_id: ChainId,
    block_number: BlockNumber,
    block_timestamp: BlockTimestamp,
    sequencer_address: SequencerAddress,
    storage_commitment: StorageCommitment,
    contract_address: ContractAddress,
    entry_point_selector: EntryPoint,
    calldata: Vec<CallParam>,
) -> Result<Vec<CallResultValue>, CallError> {
    let state_reader = SqliteReader {
        storage,
        storage_commitment,
    };

    let contract_class_cache = HashMap::new();
    let casm_class_cache = HashMap::new();
    let mut state = CachedState::new(
        state_reader,
        Some(contract_class_cache),
        Some(casm_class_cache),
    );

    let contract_address =
        starknet_rs::utils::Address(Felt252::from_bytes_be(contract_address.get().as_be_bytes()));
    let calldata = calldata
        .iter()
        .map(|p| Felt252::from_bytes_be(p.0.as_be_bytes()))
        .collect();
    let entry_point_selector = Felt252::from_bytes_be(entry_point_selector.0.as_be_bytes());
    let caller_address = starknet_rs::utils::Address(0.into());
    let exec_entry_point = ExecutionEntryPoint::new(
        contract_address,
        calldata,
        entry_point_selector,
        caller_address.clone(),
        EntryPointType::External,
        None,
        None,
        0,
    );

    let general_config = construct_general_config(
        chain_id,
        block_number,
        block_timestamp,
        sequencer_address,
        1.into(),
    )?;

    let mut execution_context = TransactionExecutionContext::new(
        caller_address,
        0.into(),
        Vec::new(),
        0,
        1.into(),
        general_config.invoke_tx_max_n_steps(),
        1.into(),
    );
    let mut resources_manager = ExecutionResourcesManager::default();

    let call_info = exec_entry_point.execute(
        &mut state,
        &general_config,
        &mut resources_manager,
        &mut execution_context,
        false,
    )?;

    let result = call_info
        .retdata
        .iter()
        .map(|f| Felt::from_be_slice(&f.to_be_bytes()).map(CallResultValue))
        .collect::<Result<Vec<CallResultValue>, _>>()
        .context("Converting results to felts")?;

    Ok(result)
}

fn construct_general_config(
    chain_id: ChainId,
    block_number: BlockNumber,
    block_timestamp: BlockTimestamp,
    sequencer_address: SequencerAddress,
    gas_price: U256,
) -> anyhow::Result<BlockContext> {
    let chain_id = match chain_id {
        ChainId::MAINNET => starknet_rs::definitions::block_context::StarknetChainId::MainNet,
        ChainId::TESTNET => starknet_rs::definitions::block_context::StarknetChainId::TestNet,
        ChainId::TESTNET2 => starknet_rs::definitions::block_context::StarknetChainId::TestNet2,
        _ => return Err(anyhow::anyhow!("Unsupported chain id")),
    };

    let starknet_os_config = StarknetOsConfig::new(
        chain_id,
        starknet_rs::utils::Address(0.into()),
        gas_price.as_u128(),
    );
    let mut general_config = BlockContext::default();
    *general_config.starknet_os_config_mut() = starknet_os_config;
    let block_info = general_config.block_info_mut();
    block_info.gas_price = gas_price.as_u64();
    block_info.block_number = block_number.get();
    block_info.block_timestamp = block_timestamp.get();
    block_info.sequencer_address =
        starknet_rs::utils::Address(Felt252::from_bytes_be(&sequencer_address.0 .0));
    block_info.starknet_version = "0.11.2".to_owned();

    Ok(general_config)
}

pub struct FeeEstimate {
    pub gas_consumed: U256,
    pub gas_price: U256,
    pub overall_fee: U256,
}

pub(crate) fn estimate_fee(
    storage: pathfinder_storage::Storage,
    chain_id: ChainId,
    block_number: BlockNumber,
    block_timestamp: BlockTimestamp,
    sequencer_address: SequencerAddress,
    storage_commitment: StorageCommitment,
    gas_price: U256,
    transactions: Vec<BroadcastedTransaction>,
) -> Result<Vec<FeeEstimate>, CallError> {
    let transactions = transactions
        .into_iter()
        .map(|tx| map_broadcasted_transaction(tx, chain_id))
        .collect::<Result<Vec<_>, TransactionError>>()?;

    estimate_fee_impl(
        storage,
        chain_id,
        block_number,
        block_timestamp,
        sequencer_address,
        storage_commitment,
        gas_price,
        transactions,
    )
}

pub fn estimate_fee_for_gateway_transactions(
    storage: pathfinder_storage::Storage,
    chain_id: ChainId,
    block_number: BlockNumber,
    block_timestamp: BlockTimestamp,
    sequencer_address: SequencerAddress,
    storage_commitment: StorageCommitment,
    gas_price: U256,
    transactions: Vec<starknet_gateway_types::reply::transaction::Transaction>,
) -> anyhow::Result<Vec<FeeEstimate>> {
    let mut db = storage.connection().map_err(map_anyhow_to_state_err)?;
    let db_tx = db.transaction().map_err(map_sqlite_to_state_err)?;

    let transactions = transactions
        .into_iter()
        .map(|tx| map_gateway_transaction(tx, chain_id, &db_tx))
        .collect::<Result<Vec<_>, _>>()?;

    drop(db_tx);

    let result = estimate_fee_impl(
        storage,
        chain_id,
        block_number,
        block_timestamp,
        sequencer_address,
        storage_commitment,
        gas_price,
        transactions,
    )
    .map_err(|e| anyhow::anyhow!("Estimate fee failed: {:?}", e))?;

    Ok(result)
}

fn estimate_fee_impl(
    storage: pathfinder_storage::Storage,
    chain_id: ChainId,
    block_number: BlockNumber,
    block_timestamp: BlockTimestamp,
    sequencer_address: SequencerAddress,
    storage_commitment: StorageCommitment,
    gas_price: U256,
    transactions: Vec<Transaction>,
) -> Result<Vec<FeeEstimate>, CallError> {
    let state_reader = SqliteReader {
        storage,
        storage_commitment,
    };

    let contract_class_cache = HashMap::new();
    let casm_class_cache = HashMap::new();
    let mut state = CachedState::new(
        state_reader,
        Some(contract_class_cache),
        Some(casm_class_cache),
    );

    let general_config = construct_general_config(
        chain_id,
        block_number,
        block_timestamp,
        sequencer_address,
        gas_price,
    )?;

    let mut fees = Vec::new();

    for (transaction_idx, transaction) in transactions.iter().enumerate() {
        let span =
            tracing::debug_span!("execute", transaction_hash=%transaction.hash(), %block_number);
        let _enter = span.enter();
        tracing::trace!(?transaction, "Estimating transacion");
        let tx_info = transaction.execute(&mut state, &general_config);
        match tx_info {
            Ok(tx_info) => {
                tracing::trace!(actual_fee=%tx_info.actual_fee, "Transaction execution finished");
                fees.push(FeeEstimate {
                    gas_consumed: U256::from(tx_info.actual_fee)
                        / std::cmp::max(1.into(), gas_price),
                    gas_price,
                    overall_fee: tx_info.actual_fee.into(),
                });
            }
            Err(error) => {
                tracing::error!(%error, %transaction_idx, "Transaction execution failed");
                //return Err(error.into());
            }
        }
    }

    Ok(fees)
}

#[derive(Debug)]
enum Transaction {
    Declare(Declare),
    DeclareV2(DeclareV2),
    Deploy(Deploy),
    DeployAccount(DeployAccount),
    Invoke(InvokeFunction),
    L1Handler(L1Handler),
}

impl Transaction {
    pub fn execute<S: State + StateReader>(
        &self,
        state: &mut S,
        block_context: &BlockContext,
    ) -> Result<TransactionExecutionInfo, TransactionError> {
        match self {
            Transaction::Declare(tx) => tx.execute(state, block_context),
            Transaction::DeclareV2(tx) => tx.execute(state, block_context),
            Transaction::Deploy(tx) => tx.execute(state, block_context),
            Transaction::DeployAccount(tx) => tx.execute(state, block_context),
            Transaction::Invoke(tx) => tx.execute(state, block_context, 0),
            Transaction::L1Handler(tx) => tx.execute(state, block_context, 0),
        }
    }

    pub fn hash(&self) -> TransactionHash {
        let hash = match self {
            Transaction::Declare(tx) => &tx.hash_value,
            Transaction::DeclareV2(tx) => &tx.hash_value,
            Transaction::Deploy(tx) => &tx.hash_value,
            Transaction::DeployAccount(tx) => tx.hash_value(),
            Transaction::Invoke(tx) => tx.hash_value(),
            Transaction::L1Handler(tx) => tx.hash_value(),
        };
        let bytes = hash.to_be_bytes();

        let felt = Felt::from_be_bytes(bytes).unwrap();

        TransactionHash(felt)
    }
}

fn map_broadcasted_transaction(
    transaction: BroadcastedTransaction,
    chain_id: ChainId,
) -> Result<Transaction, TransactionError> {
    use starknet_rs::utils::Address;

    match transaction {
        BroadcastedTransaction::Declare(tx) => match tx {
            crate::v02::types::request::BroadcastedDeclareTransaction::V1(tx) => {
                let signature = tx
                    .signature
                    .into_iter()
                    .map(|s| Felt252::from_bytes_be(&s.0 .0))
                    .collect();

                // decode program
                let contract_class_json =
                    tx.contract_class.serialize_to_json().map_err(|error| {
                        tracing::error!(%error, "Failed to serialize Cairo class to JSON");
                        TransactionError::MissingCompiledClass
                    })?;

                let contract_class =
                    ContractClass::try_from(String::from_utf8_lossy(&contract_class_json).as_ref())
                        .map_err(|error| {
                            tracing::error!(%error, "Failed to re-parse Cairo class from JSON");
                            TransactionError::MissingCompiledClass
                        })?;

                let tx = Declare::new(
                    contract_class,
                    Felt252::from_bytes_be(&chain_id.0 .0),
                    Address(Felt252::from_bytes_be(&tx.sender_address.get().0)),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    Felt252::from_bytes_be(tx.version.0.as_bytes()),
                    signature,
                    Felt252::from_bytes_be(&tx.nonce.0 .0),
                    None,
                )?;
                Ok(Transaction::Declare(tx))
            }
            crate::v02::types::request::BroadcastedDeclareTransaction::V2(tx) => {
                let signature = tx
                    .signature
                    .into_iter()
                    .map(|s| Felt252::from_bytes_be(&s.0 .0))
                    .collect();

                let json = serde_json::json!({
                    "abi": [],
                    "sierra_program": tx.contract_class.sierra_program,
                    "contract_class_version": tx.contract_class.contract_class_version,
                    "entry_points_by_type": tx.contract_class.entry_points_by_type,
                });

                let contract_class =
                    serde_json::from_value::<SierraContractClass>(json).map_err(|error| {
                        tracing::error!(%error, "Failed to parse Sierra class");
                        TransactionError::MissingCompiledClass
                    })?;

                let tx = DeclareV2::new(
                    &contract_class,
                    Felt252::from_bytes_be(&tx.compiled_class_hash.0 .0),
                    Felt252::from_bytes_be(&chain_id.0 .0),
                    Address(Felt252::from_bytes_be(&tx.sender_address.get().0)),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    Felt252::from_bytes_be(tx.version.0.as_bytes()),
                    signature,
                    Felt252::from_bytes_be(&tx.nonce.0 .0),
                    None,
                )?;

                Ok(Transaction::DeclareV2(tx))
            }
        },
        BroadcastedTransaction::Invoke(tx) => match tx {
            crate::v02::types::request::BroadcastedInvokeTransaction::V1(tx) => {
                let calldata = tx
                    .calldata
                    .into_iter()
                    .map(|p| Felt252::from_bytes_be(&p.0 .0))
                    .collect();
                let signature = tx
                    .signature
                    .into_iter()
                    .map(|s| Felt252::from_bytes_be(&s.0 .0))
                    .collect();
                let tx = InvokeFunction::new(
                    Address(Felt252::from_bytes_be(&tx.sender_address.get().0)),
                    starknet_rs::definitions::constants::EXECUTE_ENTRY_POINT_SELECTOR.clone(),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    Felt252::from_bytes_be(tx.version.0.as_bytes()),
                    calldata,
                    signature,
                    Felt252::from_bytes_be(&chain_id.0 .0),
                    Some(Felt252::from_bytes_be(&tx.nonce.0 .0)),
                    None,
                )?;
                Ok(Transaction::Invoke(tx))
            }
        },
        BroadcastedTransaction::DeployAccount(tx) => {
            let constructor_calldata = tx
                .constructor_calldata
                .into_iter()
                .map(|p| Felt252::from_bytes_be(&p.0 .0))
                .collect();
            let signature = tx
                .signature
                .into_iter()
                .map(|s| Felt252::from_bytes_be(&s.0 .0))
                .collect();
            let tx = DeployAccount::new(
                tx.class_hash.0.to_be_bytes(),
                u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                Felt252::from_bytes_be(tx.version.0.as_bytes()),
                Felt252::from_bytes_be(&tx.nonce.0 .0),
                constructor_calldata,
                signature,
                Felt252::from_bytes_be(&tx.contract_address_salt.0 .0),
                Felt252::from_bytes_be(&chain_id.0 .0),
                None,
            )?;
            Ok(Transaction::DeployAccount(tx))
        }
    }
}

fn map_gateway_transaction(
    transaction: starknet_gateway_types::reply::transaction::Transaction,
    chain_id: ChainId,
    db_transaction: &rusqlite::Transaction<'_>,
) -> anyhow::Result<Transaction> {
    use starknet_rs::utils::Address;

    match transaction {
        starknet_gateway_types::reply::transaction::Transaction::Declare(tx) => match tx {
            starknet_gateway_types::reply::transaction::DeclareTransaction::V0(tx) => {
                let signature = tx
                    .signature
                    .into_iter()
                    .map(|s| Felt252::from_bytes_be(&s.0 .0))
                    .collect();

                // decode program
                let contract_class =
                    ClassDefinitionsTable::get_class_raw(db_transaction, tx.class_hash)?
                        .context("Fetching class definition")?;
                let contract_class =
                    starknet_rs::services::api::contract_classes::deprecated_contract_class::ContractClass::try_from(
                        String::from_utf8_lossy(&contract_class).as_ref(),
                    )
                    .map_err(|e| anyhow::anyhow!("Failed to parse class definition: {}", e))?;

                let tx = Declare::new(
                    contract_class,
                    Felt252::from_bytes_be(&chain_id.0 .0),
                    Address(Felt252::from_bytes_be(&tx.sender_address.get().0)),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    0.into(),
                    signature,
                    Felt252::from_bytes_be(&tx.nonce.0 .0),
                    None,
                )?;
                Ok(Transaction::Declare(tx))
            }
            starknet_gateway_types::reply::transaction::DeclareTransaction::V1(tx) => {
                let signature = tx
                    .signature
                    .into_iter()
                    .map(|s| Felt252::from_bytes_be(&s.0 .0))
                    .collect();

                // decode program
                let contract_class =
                    ClassDefinitionsTable::get_class_raw(db_transaction, tx.class_hash)?
                        .context("Fetching class definition")?;
                let contract_class =
                    starknet_rs::services::api::contract_classes::deprecated_contract_class::ContractClass::try_from(
                        String::from_utf8_lossy(&contract_class).as_ref(),
                    )
                    .map_err(|e| anyhow::anyhow!("Failed to parse class definition: {}", e))?;

                let tx = Declare::new(
                    contract_class,
                    Felt252::from_bytes_be(&chain_id.0 .0),
                    Address(Felt252::from_bytes_be(&tx.sender_address.get().0)),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    1.into(),
                    signature,
                    Felt252::from_bytes_be(&tx.nonce.0 .0),
                    None,
                )?;
                Ok(Transaction::Declare(tx))
            }
            starknet_gateway_types::reply::transaction::DeclareTransaction::V2(tx) => {
                let signature = tx
                    .signature
                    .into_iter()
                    .map(|s| Felt252::from_bytes_be(&s.0 .0))
                    .collect();

                // fetch program
                let contract_class =
                    ClassDefinitionsTable::get_class_raw(db_transaction, tx.class_hash)?
                        .context("Fetching class definition")?;

                let contract_class = serde_json::from_slice::<FeederGatewayContractClass>(
                    &contract_class,
                )
                .map_err(|e| anyhow::anyhow!("Failed to parse gateway class definition: {}", e))?;

                let compiler_contract_class_json = serde_json::json!({
                    "abi": [],
                    "sierra_program": contract_class.sierra_program,
                    "contract_class_version": contract_class.contract_class_version,
                    "entry_points_by_type": contract_class.entry_points_by_type,
                });

                let contract_class =
                    serde_json::from_value::<SierraContractClass>(compiler_contract_class_json)
                        .map_err(|e| {
                            anyhow::anyhow!("Failed to parse Sierra class definition: {}", e)
                        })?;

                let tx = DeclareV2::new(
                    &contract_class,
                    Felt252::from_bytes_be(&tx.compiled_class_hash.0 .0),
                    Felt252::from_bytes_be(&chain_id.0 .0),
                    Address(Felt252::from_bytes_be(&tx.sender_address.get().0)),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    2.into(),
                    signature,
                    Felt252::from_bytes_be(&tx.nonce.0 .0),
                    None,
                )?;

                Ok(Transaction::DeclareV2(tx))
            }
        },
        starknet_gateway_types::reply::transaction::Transaction::Deploy(tx) => {
            let constructor_calldata = tx
                .constructor_calldata
                .into_iter()
                .map(|p| Felt252::from_bytes_be(&p.0 .0))
                .collect();

            let contract_class =
                ClassDefinitionsTable::get_class_raw(db_transaction, tx.class_hash)?
                    .context("Fetching class definition")?;
            let contract_class =
                starknet_rs::services::api::contract_classes::deprecated_contract_class::ContractClass::try_from(
                    String::from_utf8_lossy(&contract_class).as_ref(),
                )
                .map_err(|_| TransactionError::MissingCompiledClass)?;
            let tx = Deploy::new(
                Felt252::from_bytes_be(&tx.contract_address_salt.0 .0),
                contract_class,
                constructor_calldata,
                Felt252::from_bytes_be(&chain_id.0 .0),
                tx.version.without_query_version().into(),
                None,
            )?;

            Ok(Transaction::Deploy(tx))
        }
        starknet_gateway_types::reply::transaction::Transaction::DeployAccount(tx) => {
            let constructor_calldata = tx
                .constructor_calldata
                .into_iter()
                .map(|p| Felt252::from_bytes_be(&p.0 .0))
                .collect();
            let signature = tx
                .signature
                .into_iter()
                .map(|s| Felt252::from_bytes_be(&s.0 .0))
                .collect();
            let tx = DeployAccount::new(
                tx.class_hash.0.to_be_bytes(),
                u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                Felt252::from_bytes_be(tx.version.0.as_bytes()),
                Felt252::from_bytes_be(&tx.nonce.0 .0),
                constructor_calldata,
                signature,
                Felt252::from_bytes_be(&tx.contract_address_salt.0 .0),
                Felt252::from_bytes_be(&chain_id.0 .0),
                None,
            )?;
            Ok(Transaction::DeployAccount(tx))
        }
        starknet_gateway_types::reply::transaction::Transaction::Invoke(tx) => match tx {
            starknet_gateway_types::reply::transaction::InvokeTransaction::V0(tx) => {
                let calldata = tx
                    .calldata
                    .into_iter()
                    .map(|p| Felt252::from_bytes_be(&p.0 .0))
                    .collect();
                let signature = tx
                    .signature
                    .into_iter()
                    .map(|s| Felt252::from_bytes_be(&s.0 .0))
                    .collect();

                let tx = InvokeFunction::new(
                    Address(Felt252::from_bytes_be(&tx.sender_address.get().0)),
                    Felt252::from_bytes_be(&tx.entry_point_selector.0 .0),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    0.into(),
                    calldata,
                    signature,
                    Felt252::from_bytes_be(&chain_id.0 .0),
                    None,
                    None,
                )?;
                Ok(Transaction::Invoke(tx))
            }
            starknet_gateway_types::reply::transaction::InvokeTransaction::V1(tx) => {
                let calldata = tx
                    .calldata
                    .into_iter()
                    .map(|p| Felt252::from_bytes_be(&p.0 .0))
                    .collect();
                let signature = tx
                    .signature
                    .into_iter()
                    .map(|s| Felt252::from_bytes_be(&s.0 .0))
                    .collect();

                let tx = InvokeFunction::new(
                    Address(Felt252::from_bytes_be(&tx.sender_address.get().0)),
                    starknet_rs::definitions::constants::EXECUTE_ENTRY_POINT_SELECTOR.clone(),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    1.into(),
                    calldata,
                    signature,
                    Felt252::from_bytes_be(&chain_id.0 .0),
                    Some(Felt252::from_bytes_be(&tx.nonce.0 .0)),
                    None,
                )?;
                Ok(Transaction::Invoke(tx))
            }
        },
        starknet_gateway_types::reply::transaction::Transaction::L1Handler(tx) => {
            let calldata = tx
                .calldata
                .into_iter()
                .map(|p| Felt252::from_bytes_be(&p.0 .0))
                .collect();

            let tx = L1Handler::new(
                Address(Felt252::from_bytes_be(&tx.contract_address.get().0)),
                Felt252::from_bytes_be(&tx.entry_point_selector.0 .0),
                calldata,
                Felt252::from_bytes_be(&tx.nonce.0 .0),
                Felt252::from_bytes_be(&chain_id.0 .0),
                None,
            )?;
            Ok(Transaction::L1Handler(tx))
        }
    }
}

#[derive(serde::Deserialize, serde::Serialize)]
#[serde(deny_unknown_fields)]
struct FeederGatewayContractClass<'a> {
    #[serde(borrow)]
    pub abi: Cow<'a, str>,

    #[serde(borrow)]
    pub sierra_program: &'a serde_json::value::RawValue,

    #[serde(borrow)]
    pub contract_class_version: &'a serde_json::value::RawValue,

    #[serde(borrow)]
    pub entry_points_by_type: &'a serde_json::value::RawValue,
}

#[derive(Clone)]
struct SqliteReader {
    pub storage: pathfinder_storage::Storage,
    pub storage_commitment: StorageCommitment,
}

impl StateReader for SqliteReader {
    fn get_class_hash_at(
        &mut self,
        contract_address: &starknet_rs::utils::Address,
    ) -> Result<starknet_rs::utils::ClassHash, starknet_rs::core::errors::state_errors::StateError>
    {
        let pathfinder_contract_address = pathfinder_common::ContractAddress::new_or_panic(
            Felt::from_be_slice(&contract_address.0.to_be_bytes())
                .expect("Overflow in contract address"),
        );

        let _span = tracing::debug_span!("get_class_hash_at", contract_address=%pathfinder_contract_address).entered();

        tracing::trace!("Getting class hash at contract");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_sqlite_to_state_err)?;

        let tree = StorageCommitmentTree::load(&tx, self.storage_commitment);

        let state_hash = tree
            .get(pathfinder_contract_address)
            .map_err(|error| {
                tracing::error!(%error, "Failed to fetch contract state hash");
                StateError::Storage(StorageError::ErrorFetchingData)
            })?
            .ok_or_else(|| StateError::NoneClassHash(contract_address.clone()))?;

        use rusqlite::OptionalExtension;

        let class_hash: Option<ClassHash> = tx
            .query_row(
                "SELECT hash FROM contract_states WHERE state_hash=?",
                [state_hash],
                |row| row.get(0),
            )
            .optional()
            .map_err(|error| {
                tracing::error!(%error, %state_hash, "Failed to look up class hash in database");
                StateError::Storage(StorageError::ErrorFetchingData)
            })?;

        let class_hash =
            class_hash.ok_or_else(|| StateError::NoneClassHash(contract_address.clone()))?;

        Ok(class_hash.0.to_be_bytes())
    }

    fn get_nonce_at(
        &mut self,
        contract_address: &starknet_rs::utils::Address,
    ) -> Result<Felt252, starknet_rs::core::errors::state_errors::StateError> {
        let pathfinder_contract_address = pathfinder_common::ContractAddress::new_or_panic(
            Felt::from_be_slice(&contract_address.0.to_be_bytes())
                .expect("Overflow in contract address"),
        );

        let _span =
            tracing::debug_span!("get_nonce_at", contract_address=%pathfinder_contract_address)
                .entered();

        tracing::trace!("Getting nonce for contract");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_sqlite_to_state_err)?;

        let tree = StorageCommitmentTree::load(&tx, self.storage_commitment);

        let state_hash = tree
            .get(pathfinder_contract_address)
            .map_err(|error| {
                tracing::error!(%error, "Failed to fetch contract state hash");
                StateError::ContractAddressUnavailable(contract_address.clone())
            })?
            .ok_or_else(|| StateError::ContractAddressUnavailable(contract_address.clone()))?;

        let nonce = ContractsStateTable::get_nonce(&tx, state_hash)
            .map_err(|error| {
                tracing::error!(%error, %state_hash, "Failed to look up contract nonce in database");
                StateError::ContractAddressUnavailable(contract_address.clone())
            })?
            .ok_or_else(|| StateError::ContractAddressUnavailable(contract_address.clone()))?;

        Ok(Felt252::from_bytes_be(&nonce.0 .0))
    }

    fn get_storage_at(
        &mut self,
        storage_entry: &starknet_rs::state::state_cache::StorageEntry,
    ) -> Result<Felt252, starknet_rs::core::errors::state_errors::StateError> {
        let (contract_address, storage_key) = storage_entry;
        let storage_key =
            StorageAddress::new(Felt::from_be_slice(storage_key).map_err(|_| {
                StateError::ContractAddressOutOfRangeAddress(contract_address.clone())
            })?)
            .ok_or_else(|| {
                StateError::ContractAddressOutOfRangeAddress(contract_address.clone())
            })?;

        let pathfinder_contract_address = pathfinder_common::ContractAddress::new_or_panic(
            Felt::from_be_slice(&contract_address.0.to_be_bytes())
                .expect("Overflow in contract address"),
        );

        let _span =
            tracing::debug_span!("get_storage_at", contract_address=%pathfinder_contract_address, %storage_key)
                .entered();

        tracing::trace!("Getting storage value");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_sqlite_to_state_err)?;

        let tree = StorageCommitmentTree::load(&tx, self.storage_commitment);

        let state_hash = tree.get(pathfinder_contract_address).map_err(|error| {
            tracing::error!(%error, "Failed to fetch contract state hash");
            StateError::ContractAddressUnavailable(contract_address.clone())
        })?;

        let Some(state_hash) = state_hash else {
            return Ok(0.into());
        };

        let contract_state_root = ContractsStateTable::get_root(&tx, state_hash)
            .map_err(|error| {
                tracing::error!(%error, %state_hash, "Failed to look up storage root in database");
                StateError::NoneContractState(contract_address.clone())
            })?
            .ok_or_else(|| StateError::NoneContractState(contract_address.clone()))?;

        let contract_state_tree = ContractsStorageTree::load(&tx, contract_state_root);

        let storage_val = contract_state_tree
            .get(storage_key)
            .map_err(|error| {
                tracing::error!(%error, %storage_key, "Failed to fetch storage value");
                StateError::Storage(StorageError::ErrorFetchingData)
            })?
            .unwrap_or(StorageValue(Felt::ZERO));

        Ok(Felt252::from_bytes_be(&storage_val.0 .0))
    }

    fn get_contract_class(
        &mut self,
        class_hash: &starknet_rs::utils::ClassHash,
    ) -> Result<CompiledClass, StateError> {
        let class_hash =
            ClassHash(Felt::from_be_slice(class_hash).expect("Overflow in class hash"));

        let _span = tracing::debug_span!("get_compiled_class", %class_hash).entered();

        tracing::trace!("Getting class");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_sqlite_to_state_err)?;

        if let Some(casm_definition) =
            CasmClassTable::get_class_raw(&tx, class_hash).map_err(map_anyhow_to_state_err)?
        {
            let casm_class: CasmContractClass =
                serde_json::from_slice(&casm_definition).map_err(|error| {
                    tracing::error!(%error, "Failed to parse CASM class definition");
                    StateError::Storage(StorageError::ErrorFetchingData)
                })?;
            return Ok(CompiledClass::Casm(casm_class.into()));
        }

        if let Some(definition) = ClassDefinitionsTable::get_class_raw(&tx, class_hash)
            .map_err(map_anyhow_to_state_err)?
        {
            let definition = String::from_utf8(definition).map_err(|error| {
                tracing::error!(%error, "Failed to convert class definition to UTF-8 string");
                StateError::Storage(StorageError::ErrorFetchingData)
            })?;

            let contract_class: ContractClass =
                definition.as_str().try_into().map_err(|error| {
                    tracing::error!(%error, "Failed to parse class definition");
                    StateError::Storage(StorageError::ErrorFetchingData)
                })?;

            return Ok(CompiledClass::Deprecated(contract_class.into()));
        }

        tracing::error!(%class_hash, "Class definition not found");

        Err(StateError::Storage(StorageError::ErrorFetchingData))
    }

    fn get_compiled_class_hash(
        &mut self,
        class_hash: &starknet_rs::utils::ClassHash,
    ) -> Result<starknet_rs::utils::CompiledClassHash, StateError> {
        // should return the compiled class hash for a sierra class hash
        let class_hash =
            ClassHash(Felt::from_be_slice(class_hash).expect("Overflow in class hash"));

        let _span = tracing::debug_span!("get_compiled_class_hash", %class_hash).entered();

        tracing::trace!("Getting compiled class hash");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_sqlite_to_state_err)?;

        let casm_hash = CasmClassTable::get_compiled_class_hash(&tx, class_hash)
            .map_err(map_anyhow_to_state_err)?
            .ok_or(StateError::Storage(StorageError::ErrorFetchingData))?;

        Ok(casm_hash.0.to_be_bytes())
    }
}

// FIXME: we clearly need something more expressive than this
fn map_sqlite_to_state_err(
    error: rusqlite::Error,
) -> starknet_rs::core::errors::state_errors::StateError {
    tracing::error!(%error, "Database error");
    StateError::Storage(StorageError::ErrorFetchingData)
}

// FIXME: we clearly need something more expressive than this
fn map_anyhow_to_state_err(
    error: anyhow::Error,
) -> starknet_rs::core::errors::state_errors::StateError {
    tracing::error!(%error, "Internal error in state reader");
    StateError::Storage(StorageError::ErrorFetchingData)
}
