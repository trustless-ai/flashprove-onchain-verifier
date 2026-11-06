// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IProofVerifier} from "./IProofVerifier.sol";

/// @title IAgentVerifier — ERC-8274 outer, stateful application layer
/// @notice Answers: "for this task, was this agent authorized to make this claim, and does the
///         proof confirm it?" Wraps one or more IProofVerifier implementations.
interface IAgentVerifier {
    /// @notice SHOULD be emitted on every verify() call, passing and failing.
    event VerificationCompleted(
        bytes32 indexed taskId,
        bytes32 indexed agentId,
        bytes32 indexed verificationDigest,
        bool valid,
        bytes32 inputHash,
        bytes32 outputHash,
        bytes32 agentProofProfile,
        uint256 timestamp,
        bytes instanceId,
        bytes chainId
    );

    /// @notice Verify an agent's inference claim for a specific task.
    /// @return valid              Whether the agent is authorized and the proof is valid.
    /// @return verificationDigest Hash of the event's fields, returned whatever the outcome.
    function verify(
        bytes32 taskId,
        bytes32 agentId,
        bytes32 inputHash,
        bytes32 outputHash,
        bytes calldata proof
    ) external returns (bool valid, bytes32 verificationDigest);
}

/// @notice Optional ERC-8274 extension for callers that need the profile before verify().
interface IAgentProofProfile {
    function agentProofProfile() external view returns (bytes32);
}
