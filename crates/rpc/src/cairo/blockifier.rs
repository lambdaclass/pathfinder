use std::collections::HashMap;

use anyhow::Context;
use blockifier::{
    block_context::BlockContext,
    state::{cached_state::CachedState, errors::StateError, state_api::StateReader},
    transaction::transaction_execution::Transaction,
    transaction::transactions::ExecutableTransaction,
};
use pathfinder_common::{
    BlockNumber, BlockTimestamp, ClassHash, ContractNonce, SequencerAddress, StorageAddress,
    StorageValue,
};
use primitive_types::U256;
use stark_hash::Felt;
use starknet_api::{
    core::PatriciaKey, hash::StarkFelt, hash::StarkHash, patricia_key, StarknetApiError,
};

pub struct FeeEstimate {
    pub gas_consumed: U256,
    pub gas_price: U256,
    pub overall_fee: U256,
}

pub fn estimate_fee_for_gateway_transactions(
    storage: pathfinder_storage::Storage,
    block_number: BlockNumber,
    block_timestamp: BlockTimestamp,
    sequencer_address: SequencerAddress,
    transactions: Vec<starknet_gateway_types::reply::transaction::Transaction>,
    chain_id: &str,
    gas_price: u128,
) -> anyhow::Result<Vec<FeeEstimate>> {
    let mut db = storage.connection()?;
    let db_tx = db.transaction()?;

    let state_reader = SqliteReader {
        storage,
        block_number,
    };

    let mut state = CachedState::new(state_reader);

    let block_context = construct_block_context(
        chain_id,
        block_number,
        block_timestamp,
        sequencer_address,
        gas_price,
    );

    let mut fees = Vec::new();

    for transaction in transactions {
        let span = tracing::debug_span!("execute", transaction_hash=%transaction.hash());
        let _enter = span.enter();
        tracing::trace!(?transaction, "Estimating transacion");

        let transaction = map_gateway_transaction(transaction, &db_tx)?;

        let tx_info = transaction.execute(&mut state, &block_context);
        match tx_info {
            Ok(tx_info) => {
                tracing::trace!(actual_fee=%tx_info.actual_fee.0, "Transaction execution finished");
                fees.push(FeeEstimate {
                    gas_consumed: (tx_info.actual_fee.0 / std::cmp::max(1_u128, gas_price)).into(),
                    gas_price: gas_price.into(),
                    overall_fee: tx_info.actual_fee.0.into(),
                });
            }
            Err(error) => {
                use std::error::Error;
                let source = error.source();
                match source {
                    Some(source) => {
                        tracing::error!(%error, %source, "Transaction execution failed");
                    }
                    None => tracing::error!(%error, "Transaction execution failed"),
                }
                // return Err(error.into());
            }
        }
    }

    Ok(fees)
}

fn construct_block_context(
    chain_id: &str,
    block_number: BlockNumber,
    block_timestamp: BlockTimestamp,
    sequencer_address: SequencerAddress,
    gas_price: u128,
) -> BlockContext {
    BlockContext {
        chain_id: starknet_api::core::ChainId(chain_id.to_owned()),
        block_number: starknet_api::block::BlockNumber(block_number.get()),
        block_timestamp: starknet_api::block::BlockTimestamp(block_timestamp.get()),
        sequencer_address: starknet_api::core::ContractAddress(
            PatriciaKey::try_from(StarkFelt::from(sequencer_address.0))
                .expect("Sequencer address overflow"),
        ),
        fee_token_address: starknet_api::core::ContractAddress(patricia_key!(
            "0x049d36570d4e46f48e99674bd3fcc84644ddd6b96f7c741b1562b82f9e004dc7"
        )),
        vm_resource_fee_cost: default_resource_fee_costs(),
        gas_price,
        invoke_tx_max_n_steps: 1_000_000,
        validate_max_n_steps: 1_000_000,
        max_recursion_depth: 50,
    }
}

fn default_resource_fee_costs() -> HashMap<String, f64> {
    use cairo_vm::vm::runners::builtin_runner::{
        BITWISE_BUILTIN_NAME, EC_OP_BUILTIN_NAME, HASH_BUILTIN_NAME, OUTPUT_BUILTIN_NAME,
        POSEIDON_BUILTIN_NAME, RANGE_CHECK_BUILTIN_NAME, SIGNATURE_BUILTIN_NAME,
    };

    const N_STEPS_FEE_WEIGHT: f64 = 0.01;

    HashMap::from([
        (
            blockifier::abi::constants::N_STEPS_RESOURCE.to_string(),
            N_STEPS_FEE_WEIGHT,
        ),
        (HASH_BUILTIN_NAME.to_string(), 32.0 * N_STEPS_FEE_WEIGHT),
        (
            RANGE_CHECK_BUILTIN_NAME.to_string(),
            16.0 * N_STEPS_FEE_WEIGHT,
        ),
        (
            SIGNATURE_BUILTIN_NAME.to_string(),
            2048.0 * N_STEPS_FEE_WEIGHT,
        ),
        (BITWISE_BUILTIN_NAME.to_string(), 64.0 * N_STEPS_FEE_WEIGHT),
        (POSEIDON_BUILTIN_NAME.to_string(), 32.0 * N_STEPS_FEE_WEIGHT),
        (OUTPUT_BUILTIN_NAME.to_string(), 0.0 * N_STEPS_FEE_WEIGHT),
        (EC_OP_BUILTIN_NAME.to_string(), 1024.0 * N_STEPS_FEE_WEIGHT),
    ])
}

fn map_gateway_transaction(
    transaction: starknet_gateway_types::reply::transaction::Transaction,
    db_transaction: &pathfinder_storage::Transaction<'_>,
) -> anyhow::Result<Transaction> {
    match transaction {
        starknet_gateway_types::reply::transaction::Transaction::Declare(tx) => match tx {
            starknet_gateway_types::reply::transaction::DeclareTransaction::V0(tx) => {
                let class_definition = db_transaction
                    .class_definition(tx.class_hash)?
                    .context("Fetching class definition")?;

                let class_definition = String::from_utf8(class_definition)?;

                let class =
                    blockifier::execution::contract_class::ContractClassV0::try_from_json_string(
                        &class_definition,
                    )?;

                let tx = starknet_api::transaction::DeclareTransactionV0V1 {
                    transaction_hash: starknet_api::transaction::TransactionHash(
                        tx.transaction_hash.0.into(),
                    ),
                    max_fee: starknet_api::transaction::Fee(u128::from_be_bytes(
                        tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap(),
                    )),
                    signature: starknet_api::transaction::TransactionSignature(
                        tx.signature.into_iter().map(|s| s.0.into()).collect(),
                    ),
                    nonce: starknet_api::core::Nonce(tx.nonce.0.into()),
                    class_hash: starknet_api::core::ClassHash(tx.class_hash.0.into()),
                    sender_address: starknet_api::core::ContractAddress(
                        PatriciaKey::try_from(StarkFelt::from(tx.sender_address.get()))
                            .expect("No sender address overflow expected"),
                    ),
                };

                let tx = Transaction::from_api(
                    starknet_api::transaction::Transaction::Declare(
                        starknet_api::transaction::DeclareTransaction::V0(tx),
                    ),
                    Some(blockifier::execution::contract_class::ContractClass::V0(
                        class,
                    )),
                    None,
                )?;

                Ok(tx)
            }
            starknet_gateway_types::reply::transaction::DeclareTransaction::V1(tx) => {
                let class_definition = db_transaction
                    .class_definition(tx.class_hash)?
                    .context("Fetching class definition")?;

                let class_definition = String::from_utf8(class_definition)?;

                let class =
                    blockifier::execution::contract_class::ContractClassV0::try_from_json_string(
                        &class_definition,
                    )?;

                let tx = starknet_api::transaction::DeclareTransactionV0V1 {
                    transaction_hash: starknet_api::transaction::TransactionHash(
                        tx.transaction_hash.0.into(),
                    ),
                    max_fee: starknet_api::transaction::Fee(u128::from_be_bytes(
                        tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap(),
                    )),
                    signature: starknet_api::transaction::TransactionSignature(
                        tx.signature.into_iter().map(|s| s.0.into()).collect(),
                    ),
                    nonce: starknet_api::core::Nonce(tx.nonce.0.into()),
                    class_hash: starknet_api::core::ClassHash(tx.class_hash.0.into()),
                    sender_address: starknet_api::core::ContractAddress(
                        PatriciaKey::try_from(StarkFelt::from(tx.sender_address.get()))
                            .expect("No sender address overflow expected"),
                    ),
                };

                let tx = Transaction::from_api(
                    starknet_api::transaction::Transaction::Declare(
                        starknet_api::transaction::DeclareTransaction::V1(tx),
                    ),
                    Some(blockifier::execution::contract_class::ContractClass::V0(
                        class,
                    )),
                    None,
                )?;

                Ok(tx)
            }
            starknet_gateway_types::reply::transaction::DeclareTransaction::V2(tx) => {
                let class_definition = db_transaction
                    .class_definition(tx.class_hash)?
                    .context("Fetching class definition")?;

                let class_definition = String::from_utf8(class_definition)?;

                let class =
                    blockifier::execution::contract_class::ContractClassV1::try_from_json_string(
                        &class_definition,
                    )?;

                let tx = starknet_api::transaction::DeclareTransactionV2 {
                    transaction_hash: starknet_api::transaction::TransactionHash(
                        tx.transaction_hash.0.into(),
                    ),
                    max_fee: starknet_api::transaction::Fee(u128::from_be_bytes(
                        tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap(),
                    )),
                    signature: starknet_api::transaction::TransactionSignature(
                        tx.signature.into_iter().map(|s| s.0.into()).collect(),
                    ),
                    nonce: starknet_api::core::Nonce(tx.nonce.0.into()),
                    class_hash: starknet_api::core::ClassHash(tx.class_hash.0.into()),
                    sender_address: starknet_api::core::ContractAddress(
                        PatriciaKey::try_from(StarkFelt::from(tx.sender_address.get()))
                            .expect("No sender address overflow expected"),
                    ),
                    compiled_class_hash: starknet_api::core::CompiledClassHash(
                        tx.compiled_class_hash.0.into(),
                    ),
                };

                let tx = Transaction::from_api(
                    starknet_api::transaction::Transaction::Declare(
                        starknet_api::transaction::DeclareTransaction::V2(tx),
                    ),
                    Some(blockifier::execution::contract_class::ContractClass::V1(
                        class,
                    )),
                    None,
                )?;

                Ok(tx)
            }
        },
        starknet_gateway_types::reply::transaction::Transaction::Deploy(_) => todo!(),
        starknet_gateway_types::reply::transaction::Transaction::DeployAccount(tx) => {
            let tx = starknet_api::transaction::DeployAccountTransaction {
                transaction_hash: starknet_api::transaction::TransactionHash(
                    tx.transaction_hash.0.into(),
                ),
                max_fee: starknet_api::transaction::Fee(u128::from_be_bytes(
                    tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap(),
                )),
                version: starknet_api::transaction::TransactionVersion(
                    StarkFelt::new(tx.version.0.as_fixed_bytes().to_owned())
                        .expect("No transaction version overflow expected"),
                ),
                signature: starknet_api::transaction::TransactionSignature(
                    tx.signature.into_iter().map(|s| s.0.into()).collect(),
                ),
                nonce: starknet_api::core::Nonce(tx.nonce.0.into()),
                class_hash: starknet_api::core::ClassHash(tx.class_hash.0.into()),
                contract_address: starknet_api::core::ContractAddress(
                    PatriciaKey::try_from(StarkFelt::from(tx.contract_address.get()))
                        .expect("No contract address overflow expected"),
                ),
                contract_address_salt: starknet_api::transaction::ContractAddressSalt(
                    tx.contract_address_salt.0.into(),
                ),
                constructor_calldata: starknet_api::transaction::Calldata(std::sync::Arc::new(
                    tx.constructor_calldata
                        .into_iter()
                        .map(|c| c.0.into())
                        .collect(),
                )),
            };

            let tx = Transaction::from_api(
                starknet_api::transaction::Transaction::DeployAccount(tx),
                None,
                None,
            )?;

            Ok(tx)
        }
        starknet_gateway_types::reply::transaction::Transaction::Invoke(tx) => match tx {
            starknet_gateway_types::reply::transaction::InvokeTransaction::V0(tx) => {
                let tx = starknet_api::transaction::InvokeTransactionV0 {
                    transaction_hash: starknet_api::transaction::TransactionHash(
                        tx.transaction_hash.0.into(),
                    ),
                    // TODO: maybe we should store tx.max_fee as u128 internally?
                    max_fee: starknet_api::transaction::Fee(u128::from_be_bytes(
                        tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap(),
                    )),
                    signature: starknet_api::transaction::TransactionSignature(
                        tx.signature.into_iter().map(|s| s.0.into()).collect(),
                    ),
                    nonce: starknet_api::core::Nonce(ContractNonce::ZERO.0.into()),
                    sender_address: starknet_api::core::ContractAddress(
                        PatriciaKey::try_from(StarkFelt::from(tx.sender_address.get()))
                            .expect("No sender address overflow expected"),
                    ),
                    entry_point_selector: starknet_api::core::EntryPointSelector(
                        tx.entry_point_selector.0.into(),
                    ),
                    calldata: starknet_api::transaction::Calldata(std::sync::Arc::new(
                        tx.calldata.into_iter().map(|c| c.0.into()).collect(),
                    )),
                };

                let tx = Transaction::from_api(
                    starknet_api::transaction::Transaction::Invoke(
                        starknet_api::transaction::InvokeTransaction::V0(tx),
                    ),
                    None,
                    None,
                )?;

                Ok(tx)
            }
            starknet_gateway_types::reply::transaction::InvokeTransaction::V1(tx) => {
                let tx = starknet_api::transaction::InvokeTransactionV1 {
                    transaction_hash: starknet_api::transaction::TransactionHash(
                        tx.transaction_hash.0.into(),
                    ),
                    // TODO: maybe we should store tx.max_fee as u128 internally?
                    max_fee: starknet_api::transaction::Fee(u128::from_be_bytes(
                        tx.max_fee.0.to_be_bytes()[16..].try_into().unwrap(),
                    )),
                    signature: starknet_api::transaction::TransactionSignature(
                        tx.signature.into_iter().map(|s| s.0.into()).collect(),
                    ),
                    nonce: starknet_api::core::Nonce(tx.nonce.0.into()),
                    sender_address: starknet_api::core::ContractAddress(
                        PatriciaKey::try_from(StarkFelt::from(tx.sender_address.get()))
                            .expect("No sender address overflow expected"),
                    ),
                    calldata: starknet_api::transaction::Calldata(std::sync::Arc::new(
                        tx.calldata.into_iter().map(|c| c.0.into()).collect(),
                    )),
                };

                let tx = Transaction::from_api(
                    starknet_api::transaction::Transaction::Invoke(
                        starknet_api::transaction::InvokeTransaction::V1(tx),
                    ),
                    None,
                    None,
                )?;

                Ok(tx)
            }
        },
        starknet_gateway_types::reply::transaction::Transaction::L1Handler(tx) => {
            let tx = starknet_api::transaction::L1HandlerTransaction {
                transaction_hash: starknet_api::transaction::TransactionHash(
                    tx.transaction_hash.0.into(),
                ),
                version: starknet_api::transaction::TransactionVersion(
                    StarkFelt::new(tx.version.0.as_fixed_bytes().to_owned())
                        .expect("No transaction version overflow expected"),
                ),
                nonce: starknet_api::core::Nonce(tx.nonce.0.into()),
                contract_address: starknet_api::core::ContractAddress(
                    PatriciaKey::try_from(StarkFelt::from(tx.contract_address.get()))
                        .expect("No contract address overflow expected"),
                ),
                entry_point_selector: starknet_api::core::EntryPointSelector(
                    tx.entry_point_selector.0.into(),
                ),
                calldata: starknet_api::transaction::Calldata(std::sync::Arc::new(
                    tx.calldata.into_iter().map(|c| c.0.into()).collect(),
                )),
            };

            let tx = Transaction::from_api(
                starknet_api::transaction::Transaction::L1Handler(tx),
                None,
                Some(starknet_api::transaction::Fee(1_000_000_000_000)),
            )?;

            Ok(tx)
        }
    }
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
    fn get_storage_at(
        &mut self,
        contract_address: starknet_api::core::ContractAddress,
        storage_key: starknet_api::state::StorageKey,
    ) -> blockifier::state::state_api::StateResult<StarkFelt> {
        let storage_key = StorageAddress::new(storage_key.0.key().into()).ok_or_else(|| {
            StateError::StarknetApiError(StarknetApiError::OutOfRange {
                string: "Storage key out of range".to_owned(),
            })
        })?;
        let pathfinder_contract_address =
            pathfinder_common::ContractAddress::new_or_panic(contract_address.0.key().into());

        let _span =
            tracing::debug_span!("get_storage_at", contract_address=%pathfinder_contract_address, block_number=%self.block_number)
                .entered();

        tracing::trace!(%storage_key, "Getting storage value");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let Some(block_id) = self.state_block_id() else {
            return Ok(Felt::ZERO.into());
        };

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let storage_val = tx
            .storage_value(block_id, pathfinder_contract_address, storage_key)
            .map_err(map_anyhow_to_state_err)?
            .unwrap_or(StorageValue(Felt::ZERO));

        Ok(storage_val.0.into())
    }

    fn get_nonce_at(
        &mut self,
        contract_address: starknet_api::core::ContractAddress,
    ) -> blockifier::state::state_api::StateResult<starknet_api::core::Nonce> {
        let pathfinder_contract_address =
            pathfinder_common::ContractAddress::new_or_panic(contract_address.0.key().into());

        let _span =
            tracing::debug_span!("get_nonce_at", contract_address=%pathfinder_contract_address)
                .entered();

        tracing::trace!("Getting nonce for contract");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let Some(block_id) = self.state_block_id() else {
            return Ok(starknet_api::core::Nonce(pathfinder_common::ContractNonce::ZERO.0.into()));
        };

        let nonce = tx
            .contract_nonce(pathfinder_contract_address, block_id)
            .map_err(map_anyhow_to_state_err)?
            .unwrap_or(pathfinder_common::ContractNonce::ZERO);

        Ok(starknet_api::core::Nonce(nonce.0.into()))
    }

    fn get_class_hash_at(
        &mut self,
        contract_address: starknet_api::core::ContractAddress,
    ) -> blockifier::state::state_api::StateResult<starknet_api::core::ClassHash> {
        let pathfinder_contract_address =
            pathfinder_common::ContractAddress::new_or_panic(contract_address.0.key().into());

        let _span = tracing::debug_span!("get_class_hash_at", contract_address=%pathfinder_contract_address).entered();

        tracing::trace!("Getting class hash at contract");

        let Some(block_id) = self.state_block_id() else {
            return Ok(starknet_api::core::ClassHash(ClassHash::ZERO.0.into()));
        };

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let class_hash = tx
            .contract_class_hash(block_id, pathfinder_contract_address)
            .map_err(map_anyhow_to_state_err)?;

        let Some(class_hash) = class_hash else {
            return Ok(starknet_api::core::ClassHash(ClassHash::ZERO.0.into()))
        };

        Ok(starknet_api::core::ClassHash(class_hash.0.into()))
    }

    fn get_compiled_contract_class(
        &mut self,
        class_hash: &starknet_api::core::ClassHash,
    ) -> blockifier::state::state_api::StateResult<
        blockifier::execution::contract_class::ContractClass,
    > {
        let class_hash = ClassHash(class_hash.0.into());

        let _span = tracing::debug_span!("get_compiled_class", %class_hash).entered();

        tracing::trace!("Getting class");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let block_id = self.state_block_id().ok_or_else(|| {
            blockifier::state::errors::StateError::UndeclaredClassHash(
                starknet_api::core::ClassHash(class_hash.0.into()),
            )
        })?;

        if let Some(casm_definition) = tx
            .compiled_class_definition_at(block_id, class_hash)
            .map_err(map_anyhow_to_state_err)?
        {
            let casm_definition = String::from_utf8(casm_definition).map_err(|error| {
                StateError::StateReadError(format!(
                    "Class definition is not valid UTF-8: {}",
                    error
                ))
            })?;

            let casm_class =
                blockifier::execution::contract_class::ContractClassV1::try_from_json_string(
                    &casm_definition,
                )
                .map_err(|error| StateError::ProgramError(error))?;

            return Ok(blockifier::execution::contract_class::ContractClass::V1(
                casm_class,
            ));
        }

        if let Some(definition) = tx
            .class_definition_at(block_id, class_hash)
            .map_err(map_anyhow_to_state_err)?
        {
            let definition = String::from_utf8(definition).map_err(|error| {
                StateError::StateReadError(format!(
                    "Class definition is not valid UTF-8: {}",
                    error
                ))
            })?;

            let class =
                blockifier::execution::contract_class::ContractClassV0::try_from_json_string(
                    &definition,
                )
                .map_err(|error| StateError::ProgramError(error))?;

            return Ok(blockifier::execution::contract_class::ContractClass::V0(
                class,
            ));
        }

        tracing::error!(%class_hash, "Class definition not found");

        Err(StateError::StateReadError(format!(
            "Class definition not found for class hash {}",
            class_hash
        )))
    }

    fn get_compiled_class_hash(
        &mut self,
        class_hash: starknet_api::core::ClassHash,
    ) -> blockifier::state::state_api::StateResult<starknet_api::core::CompiledClassHash> {
        let class_hash = ClassHash(class_hash.0.into());

        tracing::trace!(%class_hash, "Getting compiled class hash");

        let mut db = self.storage.connection().map_err(map_anyhow_to_state_err)?;
        let tx = db.transaction().map_err(map_anyhow_to_state_err)?;

        let block_id = self.state_block_id().ok_or_else(|| {
            blockifier::state::errors::StateError::UndeclaredClassHash(
                starknet_api::core::ClassHash(class_hash.0.into()),
            )
        })?;

        let casm_hash = tx
            .compiled_class_hash_at(block_id, class_hash)
            .map_err(map_anyhow_to_state_err)?
            .ok_or_else(|| {
                StateError::StateReadError("Error getting compiled class hash".to_owned())
            })?;

        Ok(starknet_api::core::CompiledClassHash(casm_hash.0.into()))
    }
}

fn map_anyhow_to_state_err(error: anyhow::Error) -> StateError {
    tracing::error!(%error, "Internal error in state reader");
    StateError::StateReadError(error.to_string())
}
