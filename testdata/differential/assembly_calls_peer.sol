// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// A token-like peer for the assembly call suite: transfer returns true,
// false, nothing or reverts by amount, and data returns more than one word.
contract AsmPeer {
    uint256 private total;

    function transfer(address, uint256 amount) external returns (bool) {
        require(amount != 1, "peer refused");
        total += amount;
        return amount != 2;
    }

    function silent(uint256 amount) external {
        total += amount;
    }

    function data(uint256 n) external pure returns (uint256, uint256, uint256) {
        return (n, n + 1, n + 2);
    }

    function read() external view returns (uint256) { return total; }
}
