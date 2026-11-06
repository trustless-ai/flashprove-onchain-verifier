// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ISP1Verifier} from "../interfaces/ISP1Verifier.sol";

/// @title MockSP1Verifier — a stand-in for the SP1 verifier in local tests
/// @notice NOT FOR PRODUCTION. It accepts a placeholder proof whose first four bytes are
///         "FP-P" (0x46502d50) after the other shape checks pass. The anvil smoke test uses it to
///         walk the whole ERC-8274 call path without a real proof; a real deployment points
///         FlashProveVerifier at the deployed Succinct verifier instead.
contract MockSP1Verifier is ISP1Verifier {
    /// @dev First four bytes of the placeholder proof: "FP-P".
    bytes4 public constant PLACEHOLDER_HEAD = 0x46502d50;

    bool public accept;
    bytes32 public expectedProgramVKey;

    constructor(bool accept_) {
        accept = accept_;
    }

    function setAccept(bool accept_) external {
        accept = accept_;
    }

    function setExpectedProgramVKey(bytes32 programVKey_) external {
        expectedProgramVKey = programVKey_;
    }

    function verifyProof(
        bytes32 programVKey,
        bytes calldata publicValues,
        bytes calldata proofBytes
    ) external view {
        require(accept, "MockSP1: rejected by configuration");
        require(publicValues.length >= 128, "MockSP1: short public values");
        if (expectedProgramVKey != bytes32(0)) {
            require(programVKey == expectedProgramVKey, "MockSP1: wrong program vkey");
        }
        require(proofBytes.length >= 4, "MockSP1: empty proof");
        bytes4 head;
        assembly {
            head := calldataload(proofBytes.offset)
        }
        require(head == PLACEHOLDER_HEAD, "MockSP1: not the placeholder proof");
    }
}
