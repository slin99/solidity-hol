// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract StorageBytesAliases {
    bytes[] private first;
    bytes[] private second;

    function overlap(uint256 index) external {
        first[0] = first[index];
    }

    function sameSlot(uint256 index) external {
        first[0] = second[index];
    }
}
