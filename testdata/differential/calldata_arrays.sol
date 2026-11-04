// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface Reverser {
    function rev(uint256[] calldata a) external pure returns (uint256[] memory);
}

contract CalldataArrays {
    function at(uint8[] calldata a, uint256 i) external pure returns (uint8, uint256) {
        return (a[i], a.length);
    }

    function nested(uint256[][] calldata a, uint256 i, uint256 j) external pure returns (uint256, uint256) {
        return (a[i][j], a[i].length);
    }

    function rows(uint256[2][] calldata a, uint256 i) external pure returns (uint256, uint256) {
        uint256[2] calldata row = a[i];
        return (row[0] + row[1], a.length);
    }

    function fixedParam(uint256[3] calldata a) external pure returns (uint256, uint256) {
        return (a[0] + a[2], a.length);
    }

    function strings(string[] calldata a, uint256 i) external pure returns (uint256) {
        return bytes(a[i]).length;
    }

    function copy(uint256[] calldata a) external pure returns (uint256, uint256) {
        uint256[] memory m = a;
        m[0] = 9;
        return (m[0], a[0]);
    }

    function copyNested(uint8[][] calldata a) external pure returns (uint8[][] memory) {
        return a;
    }

    function echo(uint8[] calldata a) external pure returns (uint8[] calldata) {
        return a;
    }

    function sumInternal(uint256[] calldata a) private pure returns (uint256 total) {
        for (uint256 i = 0; i < a.length; i++) {
            total += a[i];
        }
    }

    function sum(uint256[] calldata a) external pure returns (uint256) {
        uint256[] calldata b = a;
        return sumInternal(b);
    }

    function viaPeer(address target, uint256[] calldata a) external pure returns (uint256[] memory) {
        return Reverser(target).rev(a);
    }

    function memoryViaPeer(address target) external pure returns (uint256, uint256) {
        uint256[] memory m = new uint256[](3);
        m[0] = 1;
        m[2] = 3;
        uint256[] memory r = Reverser(target).rev(m);
        return (r[0], r.length);
    }
}
