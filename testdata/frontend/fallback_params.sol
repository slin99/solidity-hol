// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

// A fallback taking the calldata as bytes and returning bytes: a call
// reaching it returns its calldata as the return data.
contract FallbackParams {
    function add(uint256 x, uint256 y) public pure returns (uint256) {
        return x + y;
    }

    fallback(bytes calldata input) external returns (bytes memory) {
        return input;
    }
}
