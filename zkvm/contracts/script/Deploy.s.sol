// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Vm} from "../test/utils/TestBase.sol";
import {FlashProveAgentVerifier} from "../src/FlashProveAgentVerifier.sol";
import {IProofVerifier} from "../src/interfaces/IProofVerifier.sol";
import {SP1ProofVerifier} from "../src/SP1ProofVerifier.sol";

/// @title Deploy — the production deployment, configured entirely by environment parameters
/// @notice Required parameters (the deploy script `zkvm/scripts/deploy.sh` fills them from the
///         JSON configuration):
///           DEPLOYER_PRIVATE_KEY  the deploying key
///           SP1_VERIFIER          the deployed SP1 verifier (gateway or circuit-specific)
///           PROGRAM_VKEY          the SP1 program vkey (bytes32)
///           COMMITMENT_ID         the FlashProve commitment ID this deployment binds
///           ACCEPTED_VERDICTS     the verdict bit mask (bit `code`; YES = 2, WITHIN_LIMITS = 4)
///           REQUIRE_STATUS_ZERO   true or false
///           AUTHORIZED_AGENTS     comma-separated 32-byte hex agent IDs
contract Deploy {
    Vm private constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    event Deployed(
        address indexed sp1ProofVerifier,
        address indexed agentVerifier,
        bytes32 programVKey,
        bytes32 commitmentId,
        uint16 acceptedVerdicts
    );

    function run() external {
        uint256 deployerKey = vm.envUint("DEPLOYER_PRIVATE_KEY");
        address sp1Verifier = vm.envAddress("SP1_VERIFIER");
        bytes32 programVKey = vm.envBytes32("PROGRAM_VKEY");
        bytes32 commitmentId = vm.envBytes32("COMMITMENT_ID");
        uint16 acceptedVerdicts = uint16(vm.envUint("ACCEPTED_VERDICTS"));
        bool requireStatusZero = vm.envBool("REQUIRE_STATUS_ZERO");
        bytes32[] memory agents = parseAgents(vm.envString("AUTHORIZED_AGENTS"));

        vm.startBroadcast(deployerKey);
        SP1ProofVerifier sp1 = new SP1ProofVerifier(sp1Verifier);
        FlashProveAgentVerifier agentVerifier = new FlashProveAgentVerifier(
            IProofVerifier(address(sp1)),
            abi.encode(programVKey),
            commitmentId,
            acceptedVerdicts,
            requireStatusZero,
            agents
        );
        vm.stopBroadcast();

        emit Deployed(
            address(sp1),
            address(agentVerifier),
            programVKey,
            commitmentId,
            acceptedVerdicts
        );
    }

    function parseAgents(string memory list) internal pure returns (bytes32[] memory agents) {
        bytes memory data = bytes(list);
        if (data.length == 0) {
            return new bytes32[](0);
        }
        uint256 count = 1;
        for (uint256 i = 0; i < data.length; i++) {
            if (data[i] == ",") count++;
        }
        agents = new bytes32[](count);
        uint256 index;
        uint256 start;
        for (uint256 i = 0; i <= data.length; i++) {
            if (i == data.length || data[i] == ",") {
                agents[index++] = parseHex(data, start, i);
                start = i + 1;
            }
        }
    }

    function parseHex(
        bytes memory data,
        uint256 start,
        uint256 end
    ) internal pure returns (bytes32) {
        if (end - start >= 2 && data[start] == "0" && data[start + 1] == "x") {
            start += 2;
        }
        require(end - start == 64, "Deploy: an agent must be 32 bytes of hex");
        uint256 value;
        for (uint256 i = start; i < end; i++) {
            value = value * 16 + nibble(data[i]);
        }
        return bytes32(value);
    }

    function nibble(bytes1 character) internal pure returns (uint256) {
        uint8 c = uint8(character);
        if (c >= 0x30 && c <= 0x39) return c - 0x30;
        if (c >= 0x61 && c <= 0x66) return c - 0x61 + 10;
        if (c >= 0x41 && c <= 0x46) return c - 0x41 + 10;
        revert("Deploy: not hex");
    }
}
