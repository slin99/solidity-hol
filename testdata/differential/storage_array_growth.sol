// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Copies into a storage array of static length from a shorter static array:
// the destination keeps its length and its elements past the source's are
// cleared.
contract StorageArrayGrowth {
    bytes8[9] short9;
    bytes17[10] long10;
    uint256[2][] pairs;
    uint256[4][] quads;
    uint256[2][3] grid;

    function staticGrow() public returns (bytes17, bytes17, bytes17) {
        for (uint256 i = 0; i < short9.length; ++i) short9[i] = bytes8(uint64(i + 1));
        long10[8] = bytes8(uint64(2));
        long10[9] = bytes8(uint64(2));
        long10 = short9;
        return (long10[0], long10[8], long10[9]);
    }

    function quadsFromCalldata(uint256[2][] calldata a) external returns (uint256, uint256, uint256) {
        quads = new uint256[4][](3);
        quads[0][3] = 9;
        quads[2][0] = 9;
        quads = a;
        return (quads.length, quads[0][1], quads[0][3]);
    }

    function quadsFromStorage() public returns (uint256, uint256) {
        quads = new uint256[4][](3);
        quads[1][2] = 9;
        pairs = new uint256[2][](2);
        pairs[1][1] = 6;
        quads = pairs;
        return (quads.length, quads[1][1] + quads[1][2]);
    }

    function gridFromMemory() public returns (uint256, uint256) {
        grid[2][1] = 5;
        grid[1][0] = 5;
        uint256[2][2] memory m;
        m[0][0] = 1;
        m[1][1] = 2;
        grid = m;
        return (grid[1][1] + grid[1][0], grid[2][1]);
    }
}
