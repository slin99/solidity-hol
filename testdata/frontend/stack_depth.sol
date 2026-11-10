// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract StackDepth {
    function sum(uint a0, uint a1, uint a2, uint a3, uint a4, uint a5, uint a6, uint a7, uint a8, uint a9, uint a10, uint a11, uint a12, uint a13, uint a14, uint a15, uint a16)
        external pure returns (uint)
    {
        return a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16;
    }
}
