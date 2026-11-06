// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {TestBase} from "./utils/TestBase.sol";
import {ExampleAgentVerifier} from "../src/examples/ExampleAgentVerifier.sol";
import {IERC165} from "../src/interfaces/IERC165.sol";
import {IAgentProofProfile, IAgentVerifier} from "../src/interfaces/IAgentVerifier.sol";
import {IProofVerifier} from "../src/interfaces/IProofVerifier.sol";
import {MockSP1Verifier} from "../src/mocks/MockSP1Verifier.sol";
import {FlashProveVerifier} from "../src/FlashProveVerifier.sol";

contract ExampleAgentVerifierTest is TestBase {
    MockSP1Verifier private mock;
    FlashProveVerifier private sp1;
    ExampleAgentVerifier private agentVerifier;

    bytes32 private constant VKEY = keccak256("program-vkey");
    bytes32 private constant COMMITMENT_ID = keccak256("flashprove-commitment");
    bytes32 private constant INPUT = keccak256("model input");
    bytes32 private constant RESULT = keccak256("result-v1 line");
    bytes32 private constant AGENT = bytes32(uint256(uint160(address(0xA11CE))));
    bytes32 private constant OTHER_AGENT = bytes32(uint256(uint160(address(0xB0B))));
    bytes32 private constant TASK = keccak256("task-1");
    bytes32 private constant TASK_2 = keccak256("task-2");
    bytes private constant PLACEHOLDER = "FP-PLACEHOLDER-PROOF";

    uint16 private constant ACCEPT_YES_AND_WITHIN_LIMITS = (1 << 1) | (1 << 2);

    function setUp() public {
        mock = new MockSP1Verifier(true);
        mock.setExpectedProgramVKey(VKEY);
        sp1 = new FlashProveVerifier(address(mock));
        agentVerifier = deployAgentVerifier(ACCEPT_YES_AND_WITHIN_LIMITS, true);
    }

    function deployAgentVerifier(
        uint16 accepted,
        bool requireStatusZero
    ) private returns (ExampleAgentVerifier) {
        bytes32[] memory agents = new bytes32[](1);
        agents[0] = AGENT;
        return
            new ExampleAgentVerifier(
                IProofVerifier(address(sp1)),
                abi.encode(VKEY),
                COMMITMENT_ID,
                accepted,
                requireStatusZero,
                agents
            );
    }

    function proof(
        uint8 verdict,
        uint16 status,
        bytes32 commitmentId,
        bytes32 inputHash,
        bytes32 resultHash
    ) private pure returns (bytes memory) {
        bytes memory pv = buildPublicValues(
            verdict,
            status,
            0,
            commitmentId,
            inputHash,
            resultHash
        );
        return abi.encode(pv, PLACEHOLDER);
    }

    function goodProof() private pure returns (bytes memory) {
        return proof(1, 0, COMMITMENT_ID, INPUT, RESULT);
    }

    function expectedDigest(
        bytes32 taskId,
        bytes32 agentId,
        bytes32 inputHash,
        bytes32 outputHash,
        bool valid
    ) private view returns (bytes32) {
        return
            keccak256(
                abi.encode(
                    taskId,
                    agentId,
                    inputHash,
                    outputHash,
                    valid,
                    agentVerifier.agentProofProfile(),
                    block.timestamp,
                    abi.encodePacked(address(agentVerifier)),
                    abi.encode(block.chainid)
                )
            );
    }

    function test_accepts_and_consumes_a_valid_claim() public {
        (bool valid, bytes32 digest) = agentVerifier.verify(
            TASK,
            AGENT,
            INPUT,
            RESULT,
            goodProof()
        );
        assertTrue(valid, "valid claim rejected");
        assertEq(digest, expectedDigest(TASK, AGENT, INPUT, RESULT, true), "digest");
        assertTrue(agentVerifier.usedTasks(TASK), "task not consumed");
    }

    function test_single_use_task() public {
        (bool first, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, goodProof());
        assertTrue(first, "first attempt");
        (bool second, bytes32 digest) = agentVerifier.verify(
            TASK,
            AGENT,
            INPUT,
            RESULT,
            goodProof()
        );
        assertFalse(second, "replayed task accepted");
        assertEq(digest, expectedDigest(TASK, AGENT, INPUT, RESULT, false), "failed digest");
    }

    function test_rejects_an_unauthorized_agent() public {
        (bool valid, ) = agentVerifier.verify(TASK, OTHER_AGENT, INPUT, RESULT, goodProof());
        assertFalse(valid, "unauthorized agent accepted");
        assertFalse(agentVerifier.usedTasks(TASK), "task consumed on failure");
    }

    function test_rejects_another_commitment_id() public {
        bytes memory wrong = proof(1, 0, keccak256("another commitment"), INPUT, RESULT);
        (bool valid, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, wrong);
        assertFalse(valid, "another commitment accepted");
    }

    function test_rejects_an_unaccepted_verdict() public {
        bytes memory no = proof(3, 0, COMMITMENT_ID, INPUT, RESULT);
        (bool valid, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, no);
        assertFalse(valid, "NO verdict accepted");
    }

    function test_accepts_within_limits_when_configured() public {
        bytes memory withinLimits = proof(2, 0, COMMITMENT_ID, INPUT, RESULT);
        (bool valid, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, withinLimits);
        assertTrue(valid, "WITHIN_LIMITS verdict rejected");

        ExampleAgentVerifier yesOnly = deployAgentVerifier(1 << 1, true);
        (bool validYes, ) = yesOnly.verify(TASK_2, AGENT, INPUT, RESULT, withinLimits);
        assertFalse(validYes, "a YES-only deployment accepted WITHIN_LIMITS");
    }

    function test_rejects_a_nonzero_status() public {
        bytes memory badStatus = proof(1, 1, COMMITMENT_ID, INPUT, RESULT);
        (bool valid, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, badStatus);
        assertFalse(valid, "nonzero status accepted");
    }

    function test_rejects_wrong_input_or_output() public {
        bytes memory wrongInput = proof(1, 0, COMMITMENT_ID, keccak256("other"), RESULT);
        (bool valid, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, wrongInput);
        assertFalse(valid, "wrong input accepted");

        bytes memory wrongOutput = proof(1, 0, COMMITMENT_ID, INPUT, keccak256("other"));
        (bool validOutput, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, wrongOutput);
        assertFalse(validOutput, "wrong output accepted");
    }

    function test_rejects_when_the_inner_verifier_rejects() public {
        mock.setAccept(false);
        (bool valid, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, goodProof());
        assertFalse(valid, "rejected proof accepted");
    }

    function test_rejects_a_malformed_proof() public {
        (bool valid, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, hex"deadbeef");
        assertFalse(valid, "malformed proof accepted");
        (bool valid2, ) = agentVerifier.verify(TASK, AGENT, INPUT, RESULT, new bytes(64));
        assertFalse(valid2, "undecodable proof accepted");
    }

    function test_agent_proof_profile() public view {
        bytes32 expected = keccak256(
            abi.encode(address(sp1), sp1.proofProfile(), keccak256(abi.encode(VKEY)))
        );
        assertEq(agentVerifier.agentProofProfile(), expected, "agent profile");
    }

    function test_supports_interfaces() public view {
        assertTrue(
            agentVerifier.supportsInterface(type(IAgentVerifier).interfaceId),
            "IAgentVerifier"
        );
        assertTrue(
            agentVerifier.supportsInterface(type(IAgentProofProfile).interfaceId),
            "IAgentProofProfile"
        );
        assertTrue(agentVerifier.supportsInterface(type(IERC165).interfaceId), "IERC165");
        assertFalse(agentVerifier.supportsInterface(0xffffffff), "unknown interface");
    }

    function test_binding_checks_are_exposed() public view {
        assertTrue(
            agentVerifier.checkBinding(goodProof(), INPUT, RESULT),
            "checkBinding rejected a good bundle"
        );
        assertFalse(
            agentVerifier.checkBinding(goodProof(), keccak256("x"), RESULT),
            "checkBinding accepted a wrong input"
        );
    }
}
