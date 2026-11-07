// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Conditionals {
    enum Side { Left, Right }

    uint8 public small;
    uint256 public calls;
    bytes public blob;
    uint256[] nums;

    function literals(bool c) public pure returns (uint16, int256) {
        uint16 a = c ? 1 : 300;
        int256 z = c ? -1 : int256(7);
        return (a, z);
    }

    function widened(bool c, uint16 x) public view returns (uint256) {
        return c ? x : small;
    }

    function nested(uint256 x) public pure returns (uint256) {
        return x < 10 ? (x < 5 ? 1 : 2) : 3;
    }

    function bump(uint256 by) internal returns (uint256) {
        calls += by;
        return calls;
    }

    function onlyChosen(bool c) public returns (uint256) {
        return c ? bump(1) : bump(100);
    }

    function unchosenOverflow(bool c, uint256 a) public pure returns (uint256) {
        return c ? a : a + 1;
    }

    function conditionFirst() public returns (uint256) {
        return calls++ > 0 ? calls : 42;
    }

    function operandOrder(uint256 x, bool c) public pure returns (uint256) {
        return x + (c ? x++ : 0);
    }

    function others(bool c, address a, bytes4 s) public view returns (address, bytes4, Side, bool) {
        return (c ? a : address(this), c ? s : bytes4(0), c ? Side.Right : Side.Left, c ? false : true);
    }

    function greeting(bool c) public pure returns (string memory) {
        return c ? "hello" : "";
    }

    function storageOrMemory(bool c, bytes memory m) public view returns (bytes memory) {
        return c ? blob : m;
    }

    function setBlob(bytes memory b) public {
        blob = b;
    }

    function aliased(bool c) public pure returns (uint256, uint256) {
        uint256[] memory left = new uint256[](1);
        uint256[] memory right = new uint256[](1);
        uint256[] memory chosen = c ? left : right;
        chosen[0] = 9;
        return (left[0], right[0]);
    }

    function twice(uint256 x) internal pure returns (uint256) {
        return 2 * x;
    }

    function asArgument(bool c, uint256 x) public pure returns (uint256) {
        require(c ? x > 0 : true, "zero");
        return twice(c ? x : 5);
    }

    function calldataOrMemory(bool c, bytes calldata d, bytes memory m) external pure returns (bytes memory) {
        return c ? d : m;
    }

    function storageArray(bool c) public view returns (uint256, uint256) {
        uint256[] memory m = new uint256[](1);
        uint256[] memory r = c ? nums : m;
        return (r.length, r[0]);
    }

    function conditionEffect(uint256 x) public pure returns (uint256) {
        return x + (x++ > 0 ? 1 : 2);
    }

    function loops(uint256 n) public pure returns (uint256 i, uint256 j) {
        while (i < (n > 5 ? 5 : n)) {
            i++;
        }
        do {
            j++;
        } while (j < (n > 5 ? 5 : n));
    }

    function statement(bool c, uint256 x) public pure returns (uint256) {
        c ? x++ : x--;
        return x;
    }

    function writeThrough(bool c) public pure returns (uint256, uint256, uint256) {
        uint256[] memory left = new uint256[](1);
        uint256[] memory right = new uint256[](2);
        (c ? left : right)[0] = 9;
        return (left[0], right[0], (c ? left : right).length);
    }

    function calldataArray(bool c, uint256[] calldata d) external pure returns (uint256, uint256) {
        uint256[] memory m = new uint256[](1);
        uint256[] memory r = c ? d : m;
        return (r.length, r[0]);
    }

    function staticArray(bool c) public pure returns (uint256, uint256) {
        uint256[2] memory a;
        a[0] = 4;
        uint256[2] memory b;
        b[1] = 5;
        uint256[2] memory r = c ? a : b;
        return (r[0], r[1]);
    }

    function signedWiden(bool c, int8 a, int16 b) public pure returns (int256) {
        return c ? a : b;
    }

    function inShortCircuit(bool c, uint256 x) public pure returns (bool) {
        return x > 0 && (c ? x > 5 : x < 5);
    }

    function count(uint256 by) external returns (uint256) {
        calls += by;
        return calls;
    }

    function viaReceiver(bool c) external returns (uint256) {
        Conditionals other = this;
        return (c ? this : other).count(c ? 1 : 2);
    }
}
