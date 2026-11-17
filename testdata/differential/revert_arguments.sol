// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IRevertErrors {
    error Foreign(bytes detail);
}

contract RevertArguments {
    error Pair(uint256 first, uint256 second);
    error Dynamic(string text, bytes data, uint256 count);
    error Empty();

    uint256 private ticks;
    string private text;
    bytes private data;

    function custom(bool condition) external returns (uint256) {
        require(condition, Pair(++ticks, ++ticks));
        return ticks;
    }

    function conditionFirst() external returns (uint256) {
        require(++ticks == 1, Pair(++ticks, ++ticks));
        return ticks;
    }

    function named(bool condition) external returns (uint256) {
        require(condition, Pair({second: ++ticks, first: ++ticks}));
        return ticks;
    }

    function conditionSnapshot(bool condition) external pure returns (bool) {
        require(condition, Pair((condition = false) ? 1 : 2, 0));
        return condition;
    }

    function qualified(bool condition, bytes calldata b) external pure {
        require(condition, IRevertErrors.Foreign(b));
    }

    function divide() internal view returns (uint256) {
        return 1 / ticks;
    }

    function successfulConditionStillPanics() external view {
        require(true, Pair(divide(), 0));
    }

    function computed() internal returns (string memory) {
        ++ticks;
        return string.concat("bad", "!\x00");
    }

    function message(bool condition) external returns (uint256) {
        require(condition, computed());
        return ticks;
    }

    function computedRevert() external {
        revert(computed());
    }

    function calldataError(bool condition, string calldata s, bytes calldata b) external pure {
        require(condition, Dynamic(s, b, 7));
    }

    function memoryError(string memory s, bytes memory b) external pure {
        revert Dynamic(s, b, 9);
    }

    function calldataMessage(bool condition, string calldata s) external pure {
        require(condition, s);
    }

    function storageError(bool condition) external view returns (uint256) {
        require(condition, Dynamic(text, data, 7));
        return ticks;
    }

    function storageMessage(bool condition) external view returns (uint256) {
        require(condition, text);
        return ticks;
    }

    function changeData() internal returns (uint256) {
        data[0] = 0xff;
        return ++ticks;
    }

    function liveStorage() external {
        revert Dynamic(text, data, changeData());
    }

    function changeMemory(bytes memory b) internal pure returns (uint256) {
        b[0] = 0xff;
        return 3;
    }

    function liveMemory(bytes memory b) external pure {
        revert Dynamic("memory", b, changeMemory(b));
    }

    function empty(bool condition) external pure returns (bool) {
        require(condition, Empty());
        return true;
    }
}
