// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract FixedDynamicPeer {
    function total(string[2] calldata a) external pure returns (uint256) {
        return bytes(a[0]).length + bytes(a[1]).length;
    }

    function lengths(uint256[][2] calldata a) external pure returns (uint256, uint256) {
        return (a[0].length, a[1].length);
    }
}
