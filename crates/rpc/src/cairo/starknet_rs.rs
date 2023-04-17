use std::borrow::Cow;
use std::collections::HashMap;

use anyhow::Context;
use pathfinder_common::{
    BlockNumber, BlockTimestamp, CallParam, CallResultValue, ChainId, ClassHash, ContractAddress,
    EntryPoint, SequencerAddress, StorageAddress, StorageValue, TransactionHash,
};
use primitive_types::U256;
use stark_hash::Felt;
use starknet_in_rust::core::errors::state_errors::StateError;
use starknet_in_rust::definitions::block_context::{BlockContext, StarknetOsConfig};
use starknet_in_rust::execution::execution_entry_point::ExecutionEntryPoint;
use starknet_in_rust::execution::TransactionExecutionContext;
use starknet_in_rust::services::api::contract_classes::compiled_class::CompiledClass;
use starknet_in_rust::services::api::contract_classes::deprecated_contract_class::ContractClass;
use starknet_in_rust::state::cached_state::CachedState;
use starknet_in_rust::state::state_api::StateReader;
use starknet_in_rust::state::ExecutionResourcesManager;
use starknet_in_rust::storage::errors::storage_errors::StorageError;
use starknet_in_rust::transaction::error::TransactionError;
use starknet_in_rust::transaction::{
    Declare, DeclareV2, Deploy, DeployAccount, InvokeFunction, L1Handler, Transaction,
};
use starknet_in_rust::{CasmContractClass, EntryPointType, Felt252, SierraContractClass};

use crate::v02::types::request::BroadcastedTransaction;

#[derive(Debug)]
pub enum CallError {
    ContractNotFound,
    InvalidMessageSelector,
    Internal(anyhow::Error),
}

impl From<TransactionError> for CallError {
    fn from(value: starknet_in_rust::transaction::error::TransactionError) -> Self {
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
    contract_address: ContractAddress,
    entry_point_selector: EntryPoint,
    calldata: Vec<CallParam>,
) -> Result<Vec<CallResultValue>, CallError> {
    let state_reader = SqliteReader {
        storage,
        block_number,
    };

    let contract_class_cache = HashMap::new();
    let casm_class_cache = HashMap::new();
    let mut state = CachedState::new(
        state_reader,
        Some(contract_class_cache),
        Some(casm_class_cache),
    );

    let contract_address = starknet_in_rust::utils::Address(Felt252::from_bytes_be(
        contract_address.get().as_be_bytes(),
    ));
    let calldata = calldata
        .iter()
        .map(|p| Felt252::from_bytes_be(p.0.as_be_bytes()))
        .collect();
    let entry_point_selector = Felt252::from_bytes_be(entry_point_selector.0.as_be_bytes());
    let caller_address = starknet_in_rust::utils::Address(0.into());
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

    let general_config = construct_block_context(
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
        .map(|f| Felt::from_be_slice(&f.to_bytes_be()).map(CallResultValue))
        .collect::<Result<Vec<CallResultValue>, _>>()
        .context("Converting results to felts")?;

    Ok(result)
}

fn construct_block_context(
    chain_id: ChainId,
    block_number: BlockNumber,
    block_timestamp: BlockTimestamp,
    sequencer_address: SequencerAddress,
    gas_price: U256,
) -> anyhow::Result<BlockContext> {
    let chain_id = match chain_id {
        ChainId::MAINNET => starknet_in_rust::definitions::block_context::StarknetChainId::MainNet,
        ChainId::TESTNET => starknet_in_rust::definitions::block_context::StarknetChainId::TestNet,
        ChainId::TESTNET2 => {
            starknet_in_rust::definitions::block_context::StarknetChainId::TestNet2
        }
        _ => return Err(anyhow::anyhow!("Unsupported chain id")),
    };

    let starknet_os_config = StarknetOsConfig::new(
        chain_id,
        starknet_in_rust::utils::Address(0.into()),
        gas_price.as_u128(),
    );
    let mut general_config = BlockContext::default();
    *general_config.starknet_os_config_mut() = starknet_os_config;
    let block_info = general_config.block_info_mut();
    block_info.gas_price = gas_price.as_u64();
    block_info.block_number = block_number.get();
    block_info.block_timestamp = block_timestamp.get();
    block_info.sequencer_address = starknet_in_rust::utils::Address(sequencer_address.0.into());
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
    gas_price: U256,
    transactions: Vec<starknet_gateway_types::reply::transaction::Transaction>,
) -> anyhow::Result<Vec<FeeEstimate>> {
    let mut db = storage.connection().map_err(map_anyhow_to_state_err)?;
    let db_tx = db.transaction().map_err(map_anyhow_to_state_err)?;

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
    gas_price: U256,
    transactions: Vec<Transaction>,
) -> Result<Vec<FeeEstimate>, CallError> {
    let state_reader = SqliteReader {
        storage,
        block_number,
    };

    let contract_class_cache = HashMap::new();
    let casm_class_cache = HashMap::new();
    let mut state = CachedState::new(
        state_reader,
        Some(contract_class_cache),
        Some(casm_class_cache),
    );

    let general_config = construct_block_context(
        chain_id,
        block_number,
        block_timestamp,
        sequencer_address,
        gas_price,
    )?;

    let mut fees = Vec::new();

    for (transaction_idx, transaction) in transactions.iter().enumerate() {
        let span = tracing::debug_span!("execute", transaction_hash=%transaction_hash(transaction), %block_number);
        let _enter = span.enter();

        let tx_info = transaction.execute(&mut state, &general_config, 1_000_000);
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

fn transaction_hash(transaction: &Transaction) -> TransactionHash {
    TransactionHash(
        match transaction {
            Transaction::Declare(tx) => &tx.hash_value,
            Transaction::DeclareV2(tx) => &tx.hash_value,
            Transaction::Deploy(tx) => &tx.hash_value,
            Transaction::DeployAccount(tx) => tx.hash_value(),
            Transaction::InvokeFunction(tx) => tx.hash_value(),
            Transaction::L1Handler(tx) => tx.hash_value(),
        }
        .clone()
        .into(),
    )
}

fn map_broadcasted_transaction(
    transaction: BroadcastedTransaction,
    chain_id: ChainId,
) -> Result<Transaction, TransactionError> {
    use starknet_in_rust::utils::Address;

    match transaction {
        BroadcastedTransaction::Declare(tx) => match tx {
            crate::v02::types::request::BroadcastedDeclareTransaction::V1(tx) => {
                let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();

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
                    chain_id.0.into(),
                    Address(tx.sender_address.get().into()),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    Felt252::from_bytes_be(tx.version.0.as_bytes()),
                    signature,
                    tx.nonce.0.into(),
                    None,
                )?;
                Ok(Transaction::Declare(tx))
            }
            crate::v02::types::request::BroadcastedDeclareTransaction::V2(tx) => {
                let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();

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
                    tx.compiled_class_hash.0.into(),
                    chain_id.0.into(),
                    Address(tx.sender_address.get().into()),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    Felt252::from_bytes_be(tx.version.0.as_bytes()),
                    signature,
                    tx.nonce.0.into(),
                    None,
                )?;

                Ok(Transaction::DeclareV2(tx.into()))
            }
        },
        BroadcastedTransaction::Invoke(tx) => match tx {
            crate::v02::types::request::BroadcastedInvokeTransaction::V1(tx) => {
                let calldata = tx.calldata.into_iter().map(|p| p.0.into()).collect();
                let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();
                let tx = InvokeFunction::new(
                    Address(tx.sender_address.get().into()),
                    starknet_in_rust::definitions::constants::EXECUTE_ENTRY_POINT_SELECTOR.clone(),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    Felt252::from_bytes_be(tx.version.0.as_bytes()),
                    calldata,
                    signature,
                    chain_id.0.into(),
                    Some(tx.nonce.0.into()),
                    None,
                )?;
                Ok(Transaction::InvokeFunction(tx.into()))
            }
        },
        BroadcastedTransaction::DeployAccount(tx) => {
            let constructor_calldata = tx
                .constructor_calldata
                .into_iter()
                .map(|p| p.0.into())
                .collect();
            let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();
            let tx = DeployAccount::new(
                tx.class_hash.0.to_be_bytes(),
                u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                Felt252::from_bytes_be(tx.version.0.as_bytes()),
                tx.nonce.0.into(),
                constructor_calldata,
                signature,
                tx.contract_address_salt.0.into(),
                chain_id.0.into(),
                None,
            )?;
            Ok(Transaction::DeployAccount(tx.into()))
        }
    }
}

fn map_gateway_transaction(
    transaction: starknet_gateway_types::reply::transaction::Transaction,
    chain_id: ChainId,
    db_transaction: &pathfinder_storage::Transaction<'_>,
) -> anyhow::Result<Transaction> {
    use starknet_in_rust::utils::Address;

    match transaction {
        starknet_gateway_types::reply::transaction::Transaction::Declare(tx) => match tx {
            starknet_gateway_types::reply::transaction::DeclareTransaction::V0(tx) => {
                let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();

                // decode program
                let contract_class = db_transaction
                    .class_definition(tx.class_hash)?
                    .context("Fetching class definition")?;
                let contract_class =
                    starknet_in_rust::services::api::contract_classes::deprecated_contract_class::ContractClass::try_from(
                        String::from_utf8_lossy(&contract_class).as_ref(),
                    )
                    .map_err(|e| anyhow::anyhow!("Failed to parse class definition: {}", e))?;

                let tx = Declare::new(
                    contract_class,
                    chain_id.0.into(),
                    Address(tx.sender_address.get().into()),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    0.into(),
                    signature,
                    tx.nonce.0.into(),
                    None,
                )?;
                Ok(Transaction::Declare(tx))
            }
            starknet_gateway_types::reply::transaction::DeclareTransaction::V1(tx) => {
                let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();

                // decode program
                let contract_class = db_transaction
                    .class_definition(tx.class_hash)?
                    .context("Fetching class definition")?;
                let contract_class =
                    starknet_in_rust::services::api::contract_classes::deprecated_contract_class::ContractClass::try_from(
                        String::from_utf8_lossy(&contract_class).as_ref(),
                    )
                    .map_err(|e| anyhow::anyhow!("Failed to parse class definition: {}", e))?;

                let tx = Declare::new(
                    contract_class,
                    chain_id.0.into(),
                    Address(tx.sender_address.get().into()),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    1.into(),
                    signature,
                    tx.nonce.0.into(),
                    None,
                )?;
                Ok(Transaction::Declare(tx))
            }
            starknet_gateway_types::reply::transaction::DeclareTransaction::V2(tx) => {
                let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();

                // fetch program
                let contract_class = db_transaction
                    .class_definition(tx.class_hash)?
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
                    tx.compiled_class_hash.0.into(),
                    chain_id.0.into(),
                    Address(tx.sender_address.get().into()),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    2.into(),
                    signature,
                    tx.nonce.0.into(),
                    None,
                )?;

                Ok(Transaction::DeclareV2(tx.into()))
            }
        },
        starknet_gateway_types::reply::transaction::Transaction::Deploy(tx) => {
            let constructor_calldata = tx
                .constructor_calldata
                .into_iter()
                .map(|p| p.0.into())
                .collect();

            let contract_class = db_transaction
                .class_definition(tx.class_hash)?
                .context("Fetching class definition")?;
            let contract_class =
                starknet_in_rust::services::api::contract_classes::deprecated_contract_class::ContractClass::try_from(
                    String::from_utf8_lossy(&contract_class).as_ref(),
                )
                .map_err(|_| TransactionError::MissingCompiledClass)?;
            let tx = Deploy::new(
                tx.contract_address_salt.0.into(),
                contract_class,
                constructor_calldata,
                chain_id.0.into(),
                tx.version.without_query_version().into(),
                None,
            )?;

            Ok(Transaction::Deploy(tx.into()))
        }
        starknet_gateway_types::reply::transaction::Transaction::DeployAccount(tx) => {
            let constructor_calldata = tx
                .constructor_calldata
                .into_iter()
                .map(|p| p.0.into())
                .collect();
            let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();
            let tx = DeployAccount::new(
                tx.class_hash.0.to_be_bytes(),
                u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                Felt252::from_bytes_be(tx.version.0.as_bytes()),
                tx.nonce.0.into(),
                constructor_calldata,
                signature,
                tx.contract_address_salt.0.into(),
                chain_id.0.into(),
                None,
            )?;
            Ok(Transaction::DeployAccount(tx.into()))
        }
        starknet_gateway_types::reply::transaction::Transaction::Invoke(tx) => match tx {
            starknet_gateway_types::reply::transaction::InvokeTransaction::V0(tx) => {
                let calldata = tx.calldata.into_iter().map(|p| p.0.into()).collect();
                let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();

                let tx = InvokeFunction::new(
                    Address(tx.sender_address.get().into()),
                    tx.entry_point_selector.0.into(),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    0.into(),
                    calldata,
                    signature,
                    chain_id.0.into(),
                    None,
                    None,
                )?;
                Ok(Transaction::InvokeFunction(tx.into()))
            }
            starknet_gateway_types::reply::transaction::InvokeTransaction::V1(tx) => {
                let calldata = tx.calldata.into_iter().map(|p| p.0.into()).collect();
                let signature = tx.signature.into_iter().map(|s| s.0.into()).collect();

                let tx = InvokeFunction::new(
                    Address(tx.sender_address.get().into()),
                    starknet_in_rust::definitions::constants::EXECUTE_ENTRY_POINT_SELECTOR.clone(),
                    u128::from_be_bytes(tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap()),
                    1.into(),
                    calldata,
                    signature,
                    chain_id.0.into(),
                    Some(tx.nonce.0.into()),
                    None,
                )?;
                Ok(Transaction::InvokeFunction(tx.into()))
            }
        },
        starknet_gateway_types::reply::transaction::Transaction::L1Handler(tx) => {
            let calldata = tx.calldata.into_iter().map(|p| p.0.into()).collect();

            let tx = L1Handler::new(
                Address(tx.contract_address.get().into()),
                tx.entry_point_selector.0.into(),
                calldata,
                tx.nonce.0.into(),
                chain_id.0.into(),
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
    pub block_number: BlockNumber,
}

impl SqliteReader {
    fn state_block_id(&self) -> Option<pathfinder_storage::BlockId> {
        match self.block_number.get() {
            0 => None,
            n => Some(BlockNumber::new_or_panic(n - 1).into()),
        }
    }
}

impl StateReader for SqliteReader {
    fn get_class_hash_at(
        &mut self,
        contract_address: &starknet_in_rust::utils::Address,
    ) -> Result<
        starknet_in_rust::utils::ClassHash,
        starknet_in_rust::core::errors::state_errors::StateError,
    > {
        let pathfinder_contract_address = pathfinder_common::ContractAddress::new_or_panic(
            Felt::from_be_slice(&contract_address.0.to_bytes_be())
                .expect("Overflow in contract address"),
        );

        let _span = tracing::debug_span!("get_class_hash_at", contract_address=%pathfinder_contract_address).entered();

        tracing::trace!("Getting class hash at contract");

        let block_id = self
            .state_block_id()
            .ok_or_else(|| StateError::NoneClassHash(contract_address.clone()))?;

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let class_hash = tx
            .contract_class_hash(block_id, pathfinder_contract_address)
            .map_err(|error| {
                tracing::error!(%error, "Failed to fetch contract class hash");
                StateError::Storage(StorageError::ErrorFetchingData)
            })?
            .ok_or_else(|| StateError::NoneClassHash(contract_address.clone()))?;

        Ok(class_hash.0.to_be_bytes())
    }

    fn get_nonce_at(
        &mut self,
        contract_address: &starknet_in_rust::utils::Address,
    ) -> Result<Felt252, starknet_in_rust::core::errors::state_errors::StateError> {
        let pathfinder_contract_address = pathfinder_common::ContractAddress::new_or_panic(
            Felt::from_be_slice(&contract_address.0.to_bytes_be())
                .expect("Overflow in contract address"),
        );

        let _span =
            tracing::debug_span!("get_nonce_at", contract_address=%pathfinder_contract_address)
                .entered();

        tracing::trace!("Getting nonce for contract");

        let block_id = self
            .state_block_id()
            .ok_or_else(|| StateError::NoneNonce(contract_address.clone()))?;

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let nonce = tx
            .contract_nonce(pathfinder_contract_address, block_id)
            .map_err(|error| {
                tracing::error!(%error, "Failed to fetch contract nonce");
                StateError::Storage(StorageError::ErrorFetchingData)
            })?
            .ok_or_else(|| StateError::NoneNonce(contract_address.clone()))?;

        Ok(nonce.0.into())
    }

    fn get_storage_at(
        &mut self,
        storage_entry: &starknet_in_rust::state::state_cache::StorageEntry,
    ) -> Result<Felt252, starknet_in_rust::core::errors::state_errors::StateError> {
        let (contract_address, storage_key) = storage_entry;
        let storage_key =
            StorageAddress::new(Felt::from_be_slice(storage_key).map_err(|_| {
                StateError::ContractAddressOutOfRangeAddress(contract_address.clone())
            })?)
            .ok_or_else(|| {
                StateError::ContractAddressOutOfRangeAddress(contract_address.clone())
            })?;

        let pathfinder_contract_address = pathfinder_common::ContractAddress::new_or_panic(
            Felt::from_be_slice(&contract_address.0.to_bytes_be())
                .expect("Overflow in contract address"),
        );

        let _span =
            tracing::debug_span!("get_storage_at", contract_address=%pathfinder_contract_address, %storage_key)
                .entered();

        tracing::trace!("Getting storage value");

        let Some(block_id) = self.state_block_id() else {
            return Ok(Felt::ZERO.into());
        };

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let storage_val = tx
            .storage_value(block_id, pathfinder_contract_address, storage_key)
            .map_err(|error| {
                tracing::error!(%error, %storage_key, "Failed to fetch storage value");
                StateError::Storage(StorageError::ErrorFetchingData)
            })?
            .unwrap_or(StorageValue(Felt::ZERO));

        Ok(storage_val.0.into())
    }

    fn get_contract_class(
        &mut self,
        class_hash: &starknet_in_rust::utils::ClassHash,
    ) -> Result<CompiledClass, StateError> {
        let class_hash =
            ClassHash(Felt::from_be_slice(class_hash).expect("Overflow in class hash"));

        let _span = tracing::debug_span!("get_compiled_class", %class_hash).entered();

        tracing::trace!("Getting class");

        let block_id = self
            .state_block_id()
            .ok_or_else(|| StateError::Storage(StorageError::ErrorFetchingData))?;

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        if let Some(casm_definition) = tx
            .compiled_class_definition_at(block_id, class_hash)
            .map_err(map_anyhow_to_state_err)?
        {
            let casm_class: CasmContractClass =
                serde_json::from_slice(&casm_definition).map_err(|error| {
                    tracing::error!(%error, "Failed to parse CASM class definition");
                    StateError::Storage(error.into())
                })?;
            return Ok(CompiledClass::Casm(casm_class.into()));
        }

        if let Some(definition) = tx
            .class_definition_at(block_id, class_hash)
            .map_err(map_anyhow_to_state_err)?
        {
            let definition = String::from_utf8(definition).map_err(|error| {
                tracing::error!(%error, "Failed to convert class definition to UTF-8 string");
                StateError::Storage(StorageError::ErrorFetchingData)
            })?;

            let contract_class: ContractClass =
                definition.as_str().try_into().map_err(|error| {
                    tracing::error!(%error, "Failed to parse class definition");
                    StateError::CustomError(format!(
                        "Failed to parse Cairo class definition: {}",
                        error
                    ))
                })?;

            return Ok(CompiledClass::Deprecated(contract_class.into()));
        }

        tracing::error!(%class_hash, "Class definition not found");

        Err(StateError::Storage(StorageError::ErrorFetchingData))
    }

    fn get_compiled_class_hash(
        &mut self,
        class_hash: &starknet_in_rust::utils::ClassHash,
    ) -> Result<starknet_in_rust::utils::CompiledClassHash, StateError> {
        // should return the compiled class hash for a sierra class hash
        let pathfinder_class_hash =
            ClassHash(Felt::from_be_slice(class_hash).expect("Overflow in class hash"));

        let _span =
            tracing::debug_span!("get_compiled_class_hash", %pathfinder_class_hash).entered();

        tracing::trace!("Getting compiled class hash");

        let block_id = self
            .state_block_id()
            .ok_or_else(|| StateError::NoneCompiledHash(*class_hash))?;

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let casm_hash = tx
            .compiled_class_hash_at(block_id, pathfinder_class_hash)
            .map_err(map_anyhow_to_state_err)?
            .ok_or(StateError::NoneCompiledHash(*class_hash))?;

        Ok(casm_hash.0.to_be_bytes())
    }
}

// FIXME: we clearly need something more expressive than this
fn map_anyhow_to_state_err(
    error: anyhow::Error,
) -> starknet_in_rust::core::errors::state_errors::StateError {
    tracing::error!(%error, "Internal error in state reader");
    StateError::Storage(StorageError::ErrorFetchingData)
}
