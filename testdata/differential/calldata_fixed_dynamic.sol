// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface FixedDynamicPeer {
    function total(string[2] calldata a) external pure returns (uint256);
    function lengths(uint256[][2] calldata a) external pure returns (uint256, uint256);
}

contract CalldataFixedDynamic {
    string[2] names;
    uint256[][2] lists;

    function strings(string[2] calldata a, uint256 i) external pure returns (uint256, uint256) {
        return (bytes(a[i]).length, a.length);
    }

    function stringAt(string[2] calldata a, uint256 i) external pure returns (string memory) {
        return a[i];
    }

    function bytesAt(bytes[2] calldata a, uint256 i, uint256 j) external pure returns (bytes1, uint256) {
        bytes calldata e = a[i];
        return (e[j], e.length);
    }

    function nested(uint256[][2] calldata a, uint256 i, uint256 j) external pure returns (uint256, uint256) {
        return (a[i][j], a[i].length);
    }

    function rows(string[2][] calldata a, uint256 i, uint256 j) external pure returns (string memory, uint256) {
        string[2] calldata row = a[i];
        return (row[j], a.length);
    }

    function copy(string[2] calldata a) external pure returns (string[2] memory) {
        string[2] memory m = a;
        m[0] = "x";
        return m;
    }

    function copyNested(uint256[][2] calldata a) external pure returns (uint256[][2] memory) {
        return a;
    }

    function store(string[2] calldata a, uint256[][2] calldata b) external returns (uint256, uint256) {
        names = a;
        lists = b;
        return (bytes(names[1]).length, lists[0].length);
    }

    function encode(string[2] calldata a) external pure returns (bytes memory) {
        return abi.encode(a, uint256(7));
    }

    function encodeRows(bytes[2][] calldata a) external pure returns (bytes memory) {
        return abi.encode(a);
    }

    function echo(bytes[2] calldata a) external pure returns (bytes[2] calldata) {
        return a;
    }

    function viaPeer(address target, string[2] calldata a) external pure returns (uint256) {
        return FixedDynamicPeer(target).total(a);
    }

    function nestedViaPeer(address target, uint256[][2] calldata a) external pure returns (uint256, uint256) {
        return FixedDynamicPeer(target).lengths(a);
    }
}
