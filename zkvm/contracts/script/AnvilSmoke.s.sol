// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Vm} from "../test/utils/TestBase.sol";
import {FlashProveAgentVerifier} from "../src/FlashProveAgentVerifier.sol";
import {FlashProvePublicValues} from "../src/libraries/FlashProvePublicValues.sol";
import {IProofVerifier} from "../src/interfaces/IProofVerifier.sol";
import {MockSP1Verifier} from "../src/mocks/MockSP1Verifier.sol";
import {SP1ProofVerifier} from "../src/SP1ProofVerifier.sol";

/// @title AnvilSmoke — deploy the stack to a local anvil and walk the ERC-8274 call path
/// @notice The proof is a placeholder: the bundle's public values are the real FPV1 block from
///         `fp-pv bundle`, and the proof bytes start with "FP-P", which MockSP1Verifier accepts.
///         No real proving is involved. Parameters come from environment variables, filled by
///         `zkvm/scripts/anvil-smoke.sh` from `zkvm/config/flashprove.json`:
///           DEPLOYER_PRIVATE_KEY, PROGRAM_VKEY, COMMITMENT_ID, ACCEPTED_VERDICTS,
///           REQUIRE_STATUS_ZERO, AGENT_ID, TASK_ID
///         The bundle is the `run(bytes)` argument.
contract AnvilSmoke {
    Vm private constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    event Smoke(
        address mockSp1Verifier,
        address sp1ProofVerifier,
        address agentVerifier,
        bytes32 commitmentId,
        bytes32 inputHash,
        bytes32 outputHash,
        bool valid,
        bytes32 verificationDigest
    );

    function run(bytes calldata bundle) external {
        uint256 deployerKey = vm.envUint("DEPLOYER_PRIVATE_KEY");
        bytes32 programVKey = vm.envBytes32("PROGRAM_VKEY");
        bytes32 commitmentId = vm.envBytes32("COMMITMENT_ID");
        uint16 acceptedVerdicts = uint16(vm.envUint("ACCEPTED_VERDICTS"));
        bool requireStatusZero = vm.envBool("REQUIRE_STATUS_ZERO");
        bytes32 agentId = vm.envBytes32("AGENT_ID");
        bytes32 taskId = vm.envBytes32("TASK_ID");

        (bytes memory publicValues, ) = abi.decode(bundle, (bytes, bytes));
        FlashProvePublicValues.Values memory values = FlashProvePublicValues.decode(publicValues);
        require(values.commitmentId == commitmentId, "smoke: bundle is for another commitment");
        require(values.verdict == FlashProvePublicValues.VERDICT_YES, "smoke: fixture is not YES");

        bytes32[] memory agents = new bytes32[](1);
        agents[0] = agentId;

        vm.startBroadcast(deployerKey);
        MockSP1Verifier mock = new MockSP1Verifier(true);
        mock.setExpectedProgramVKey(programVKey);
        SP1ProofVerifier sp1 = new SP1ProofVerifier(address(mock));
        FlashProveAgentVerifier agentVerifier = new FlashProveAgentVerifier(
            IProofVerifier(address(sp1)),
            abi.encode(programVKey),
            commitmentId,
            acceptedVerdicts,
            requireStatusZero,
            agents
        );
        (bool valid, bytes32 digest) = agentVerifier.verify(
            taskId,
            agentId,
            values.inputDigest,
            values.resultV1Digest,
            bundle
        );
        vm.stopBroadcast();

        require(valid, "smoke: the placeholder proof did not verify");
        require(agentVerifier.usedTasks(taskId), "smoke: the task was not consumed");
        require(agentVerifier.agentProofProfile() != bytes32(0), "smoke: empty profile");

        emit Smoke(
            address(mock),
            address(sp1),
            address(agentVerifier),
            values.commitmentId,
            values.inputDigest,
            values.resultV1Digest,
            valid,
            digest
        );
    }
}
