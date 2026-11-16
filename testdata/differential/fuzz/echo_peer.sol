// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// The differential fuzzer's peer at 0x5000 for suites without their own: it
// returns its arguments, so a call whose return types match its arguments'
// round-trips and any other decodes or reverts as the caller's code decides.
contract EchoPeer {
    fallback(bytes calldata input) external payable returns (bytes memory) {
        return input.length < 4 ? input : input[4:];
    }
}
