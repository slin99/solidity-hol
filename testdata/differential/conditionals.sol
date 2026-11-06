// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Conditionals {
    enum Side { Left, Right }

    uint8 public small;
    uint256 public calls;
    bytes public blob;

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
}
