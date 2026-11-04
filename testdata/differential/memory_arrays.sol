// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract MemoryArrays {
    function dynamicWriteRead(uint256 n, uint256 i, uint256 v) external pure returns (uint256, uint256) {
        uint256[] memory a = new uint256[](n);
        a[i] = v;
        return (a.length, a[i]);
    }

    function staticDefault(uint256 i) external pure returns (uint256, uint256) {
        uint256[3] memory a;
        a[1] = 5;
        return (a[i], a.length);
    }

    function aliasing(uint8 v) external pure returns (uint8, uint8) {
        uint8[] memory a = new uint8[](2);
        uint8[] memory b = a;
        b[0] = v;
        b = new uint8[](1);
        b[0] = 9;
        return (a[0], b[0]);
    }

    function nestedDynamic(uint256 i) external pure returns (uint256, uint256) {
        uint256[][] memory a = new uint256[][](2);
        uint256 before = a[i].length;
        a[1] = new uint256[](3);
        a[1][2] = 4;
        return (before, a[1].length * 10 + a[1][2]);
    }

    function nestedStatic(uint256 v) external pure returns (uint256, uint256, uint256) {
        uint256[2][] memory a = new uint256[2][](2);
        a[1][0] = v;
        uint256[2] memory row = a[1];
        row[1] = 3;
        return (a[0][0], a[1][0], a[1][1]);
    }

    function staticMatrix(uint256 v) external pure returns (uint256) {
        uint256[2][3] memory m;
        m[2][1] = v;
        return m[2][1] + m[0][0];
    }

    function bytesElements(bytes1 v) external pure returns (uint256, bytes1) {
        bytes[] memory a = new bytes[](2);
        uint256 empty = a[0].length;
        a[1] = new bytes(3);
        a[1][2] = v;
        return (empty, a[1][2]);
    }

    function newString(uint256 n, bytes1 v) external pure returns (uint256, bytes1) {
        string memory s = new string(n);
        bytes memory b = new bytes(n);
        b[0] = v;
        return (bytes(s).length, b[0]);
    }

    function fill(uint256[] memory a, uint256 v) private pure {
        a[0] = v;
        a[0] += 1;
    }

    function internalAlias(uint256 v) external pure returns (uint256) {
        uint256[] memory a = new uint256[](1);
        fill(a, v);
        return a[0];
    }

    function sum(uint256[] memory xs) public pure returns (uint256 total) {
        for (uint256 i = 0; i < xs.length; i++) {
            total += xs[i];
        }
    }

    function depth(uint256[][] memory xs) external pure returns (uint256) {
        return xs[0][0] + xs[1].length * 10;
    }

    function range(uint8 n) external pure returns (uint8[] memory r) {
        r = new uint8[](n);
        for (uint8 i = 0; i < n; i++) {
            r[i] = i;
        }
    }

    function swap(uint256[2] memory p) external pure returns (uint256[2] memory q) {
        q[0] = p[1];
        q[1] = p[0];
    }

    function dirty(uint8[] memory xs) external pure returns (uint8) {
        return xs[0];
    }

    function bytesParam(bytes[] memory xs) external pure returns (uint256, bytes1) {
        return (xs.length, xs[1][0]);
    }

    function pairParam(bytes[2] memory xs) external pure returns (uint256) {
        return xs[0].length + xs[1].length;
    }

    function nestedReturn() external pure returns (uint256[][] memory r) {
        r = new uint256[][](2);
        r[1] = new uint256[](1);
        r[1][0] = 5;
    }

    function bytesReturn(bytes1 v) external pure returns (bytes[] memory r) {
        r = new bytes[](1);
        r[0] = new bytes(1);
        r[0][0] = v;
    }
}
