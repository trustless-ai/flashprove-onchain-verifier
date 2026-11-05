// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title IProofVerifier — ERC-8274 inner, stateless cryptographic verification layer
/// @notice Answers: "is this proof cryptographically valid for this input and output?"
/// @dev Implemented by proof-system providers, called by IAgentVerifier. Stateless: all
///      deployment configuration arrives through `metadata`.
interface IProofVerifier {
    /// @notice Verify an AI inference proof.
    /// @param inputHash  Commitment to the model input (hash scheme is backend-specific).
    /// @param outputHash Commitment to the model output (hash scheme is backend-specific).
    /// @param metadata   Invariant deployment configuration, e.g. abi.encode(bytes32 programVKey).
    /// @param proof      Per-inference cryptographic evidence.
    /// @return True if the proof is cryptographically valid for the given input and output.
    function verify(
        bytes32 inputHash,
        bytes32 outputHash,
        bytes calldata metadata,
        bytes calldata proof
    ) external returns (bool);

    /// @notice Proof system identifier in "{paradigm}/{variant}" format.
    function proofSystem() external view returns (string memory);

    /// @notice Collision-resistant description of this verifier's verification type and
    ///         configuration version.
    function proofProfile() external view returns (bytes32);
}
