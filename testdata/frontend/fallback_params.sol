// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

// A fallback with parameters and returns, which the core's fallback does
// not take, is unsupported: the rest of the contract runs, and a call
// reaching the fallback is refused.
contract FallbackParams {
    function add(uint256 x, uint256 y) public pure returns (uint256) {
        return x + y;
    }

    fallback(bytes calldata input) external returns (bytes memory) {
        return input;
    }
}
