// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Vm} from "../test/utils/TestBase.sol";
import {FlashProveVerifier} from "../src/FlashProveVerifier.sol";

/// @title DeployVerifier — deploy the stateless `IProofVerifier`, and nothing else
/// @notice This is the deployment every application shares. It has one constructor parameter and
///         holds no application configuration: the program vkey arrives per call, inside
///         `metadata`, from whichever `IAgentVerifier` is invoking it.
/// @dev    Parameters (`contracts/scripts/deploy.sh` fills them from the JSON configuration):
///           DEPLOYER_PRIVATE_KEY  the deploying key
///           SP1_VERIFIER          the deployed SP1 verifier (gateway or circuit-specific)
contract DeployVerifier {
    Vm private constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    event VerifierDeployed(address indexed verifier, address sp1Verifier);

    function run() external {
        uint256 deployerKey = vm.envUint("DEPLOYER_PRIVATE_KEY");
        address sp1Verifier = vm.envAddress("SP1_VERIFIER");

        vm.startBroadcast(deployerKey);
        FlashProveVerifier verifier = new FlashProveVerifier(sp1Verifier);
        vm.stopBroadcast();

        emit VerifierDeployed(address(verifier), sp1Verifier);
    }
}
