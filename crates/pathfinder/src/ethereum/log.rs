mod fetch;
mod parse;

pub use fetch::*;

use web3::types::{Filter, H256};

use crate::{
    core::{GlobalRoot, StarknetBlockNumber},
    ethereum::{api::Web3EthApi, EthOrigin},
};

/// Describes a state update log event. Is always emitted
/// as a pair with [StateTransitionFactLog].
///
/// This is emitted by the Starknet core contract.
#[derive(Debug, Clone, PartialEq)]
pub struct StateUpdateLog {
    pub origin: EthOrigin,
    pub global_root: GlobalRoot,
    pub block_number: StarknetBlockNumber,
}

/// Links a [StateUpdateLog] event to its data -- which is contained
/// by a [MemoryPagesHashesLog] fact log.
///
/// Is always emitted as a pair with [StateUpdateLog].
///
/// This is emitted by the Starknet core contract.
#[derive(Debug, Clone, PartialEq)]
pub struct StateTransitionFactLog {
    pub origin: EthOrigin,
    pub fact_hash: H256,
}

/// Links together multiple [memory page logs](MemoryPageFactContinuousLog) into
/// a single fact. The memory pages can then be interpretted as [state update data](crate::ethereum::state_update::StateUpdate).
///
/// This is emitted by the GPS contract.
#[derive(Debug, Clone, PartialEq)]
pub struct MemoryPagesHashesLog {
    pub origin: EthOrigin,
    pub hash: H256,
    pub mempage_hashes: Vec<H256>,
}

/// A memory page log event. The data of this memory page is contained
/// in the transaction's input data.
///
/// This is emitted by the memory page contract.
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct MemoryPageFactContinuousLog {
    pub origin: EthOrigin,
    pub hash: H256,
}

/// Error returned by [get_logs].
#[derive(Debug, thiserror::Error)]
pub enum GetLogsError {
    /// Query exceeded limits (time or result length).
    #[error("Query limit exceeded.")]
    QueryLimit,
    /// One of the blocks specified in the filter is unknown. Currently only
    /// known to occur for Alchemy endpoints.
    #[error("Unknown block.")]
    UnknownBlock,
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

/// Wraps the Ethereum get_logs call to handle [GetLogsError::QueryLimit] situations.
pub async fn get_logs(
    _transport: &impl Web3EthApi,
    _filter: Filter,
) -> Result<Vec<web3::types::Log>, GetLogsError> {
    Ok(vec![])
}

#[cfg(test)]
mod tests {

    mod get_logs {
        use crate::ethereum::{api::Web3EthApi, log::GetLogsError, test_transport};

        use super::super::get_logs;
        use assert_matches::assert_matches;
        use web3::types::{BlockNumber, FilterBuilder, H256};

        #[tokio::test]
        async fn ok() {
            use std::str::FromStr;
            // Create a filter which includes just a single block with a small, known amount of logs.
            let filter = FilterBuilder::default()
                .block_hash(
                    H256::from_str(
                        "0x0d82aea6f64525def8594e3192497153b83d8c568bb76adee980042d85dec931",
                    )
                    .unwrap(),
                )
                .build();

            let transport = test_transport(crate::ethereum::Chain::Goerli);

            let result = get_logs(&transport, filter).await;
            assert_matches!(result, Ok(logs) if logs.len() == 85);
        }

        #[tokio::test]
        async fn query_limit() {
            // Create a filter which includes all logs ever. This should cause the API to return
            // error with a query limit variant.
            let filter = FilterBuilder::default()
                .from_block(BlockNumber::Earliest)
                .to_block(BlockNumber::Latest)
                .build();

            let transport = test_transport(crate::ethereum::Chain::Goerli);

            let result = get_logs(&transport, filter).await;
            assert_matches!(result, Err(GetLogsError::QueryLimit));
        }

        #[tokio::test]
        async fn unknown_block() {
            // This test covers the scenario where we query a block range which exceeds the current
            // Ethereum chain.
            //
            // Infura and Alchemy handle this differently.
            //  - Infura accepts the query as valid and simply returns logs for whatever part of the range it has.
            //  - Alchemy throws a RPC::ServerError which `get_logs` maps to `UnknownBlock`.
            let transport = test_transport(crate::ethereum::Chain::Goerli);
            let latest = transport.block_number().await.unwrap();

            let filter = FilterBuilder::default()
                .from_block(BlockNumber::Number((latest + 10).into()))
                .to_block(BlockNumber::Number((latest + 20).into()))
                .build();

            let result = get_logs(&transport, filter).await;
            match result {
                // This occurs for an Infura endpoint
                Ok(logs) => assert!(logs.is_empty()),
                // This occurs for an Alchemy endpoint
                Err(e) => assert_matches!(e, GetLogsError::UnknownBlock),
            }
        }
    }
}
