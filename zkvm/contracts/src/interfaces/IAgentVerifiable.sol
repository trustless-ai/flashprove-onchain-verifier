// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IAgentVerifier} from "./IAgentVerifier.sol";

/// @title IAgentVerifiable — ERC-8274 declaration layer
/// @notice Implemented by settlement contracts to declare which IAgentVerifier they trust.
interface IAgentVerifiable {
    /// @notice Returns the agent verifier used by this contract.
    function getAgentVerifier() external view returns (IAgentVerifier);

    /// @notice MUST be emitted when the agent verifier changes.
    /// @param data Encoding of the verifier change, chosen by the deployment.
    event AgentVerifierUpdated(bytes data);
}
