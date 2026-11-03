// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface BytePeer {
    function putBytes(bytes calldata data) external;
    function putString(string calldata text) external;
    function rawInput(bytes calldata data) external pure returns (bytes memory);
    function afterMutation(bytes calldata data, uint256 ignored) external returns (bytes memory);
    function raw(uint256 mode) external pure returns (bytes memory);
    function echo(bytes calldata data, string calldata text) external returns (bytes memory, string memory);
}

contract DynamicBytes {
    string private title;
    bytes private stored;
    event Snapshot(bytes data, uint256 mutation);
    event StringSnapshot(string text, uint256 mutation);
    event One(bytes data);
    event Stored(bytes indexed data, bytes plain);
    event Values(bytes data, string text, uint256 count);
    event Indexed(bytes indexed data, string indexed text, bytes plain);

    constructor(string memory name, bytes memory data) {
        title = name;
        stored = data;
    }

    function name() external view returns (string memory) { return title; }
    function value() external view returns (bytes memory) { return stored; }
    function echo(bytes calldata data, string memory text) external pure returns (bytes memory, string memory) {
        return (data, text);
    }
    function empty() external pure returns (bytes memory, string memory) {
        return (hex"", "");
    }
    function memoryLength(bytes memory data) external pure returns (uint256) { return data.length; }
    function calldataLength(bytes calldata data) external pure returns (uint256) { return data.length; }
    function takeString(string calldata text) external pure returns (uint256) { return bytes(text).length; }
    function overlapping(bytes calldata first, bytes calldata second) external pure returns (uint256, bytes1, bytes1) {
        return (first.length + second.length, first[0], second[0]);
    }
    function changeMemory(bytes memory data, bytes1 replacement) external pure returns (bytes memory) {
        data[0] = replacement;
        return data;
    }
    function emitValues(bytes calldata data, string calldata text) external {
        emit Values(data, text, data.length);
        emit Indexed(data, text, data);
    }
    function peerRaw(address target, uint256 mode) external view returns (bytes memory) {
        return BytePeer(target).raw(mode);
    }
    function throughPeer(address target, bytes memory data, string memory text) external returns (bytes memory, string memory) {
        return BytePeer(target).echo(data, text);
    }

    function mutate(bytes1 replacement) internal returns (uint256) {
        stored[0] = replacement;
        return 0;
    }
    function mutateTitle(bytes1 replacement) internal returns (uint256) {
        bytes(title)[0] = replacement;
        return 0;
    }
    function eventAfterMutation(bytes1 replacement) external {
        emit Snapshot(stored, mutate(replacement));
    }
    function stringEventAfterMutation(bytes1 replacement) external {
        emit StringSnapshot(title, mutateTitle(replacement));
    }
    function peerAfterMutation(address target, bytes1 replacement) external returns (bytes memory) {
        return BytePeer(target).afterMutation(stored, mutate(replacement));
    }
    function eventThenPeerRaw(address target, bytes calldata data) external returns (bytes memory) {
        emit One(data);
        return BytePeer(target).raw(4);
    }
    function literalEventThenPeerRaw(address target) external returns (bytes memory) {
        emit One(hex"80");
        return BytePeer(target).raw(4);
    }
    function emitStored() external {
        emit Stored(stored, stored);
    }
    function peerUnmutated(address target) external returns (bytes memory) {
        return BytePeer(target).afterMutation(stored, 0);
    }
    function peerInput(address target) external view returns (bytes memory) {
        return BytePeer(target).rawInput(stored);
    }
    function defaultBytesThenPeerRaw(address target) external returns (bytes memory) {
        bytes memory data;
        emit One(data);
        return BytePeer(target).raw(4);
    }
    function defaultStringThenPeerRaw(address target) external returns (bytes memory) {
        string memory text;
        emit One(bytes(text));
        return BytePeer(target).raw(4);
    }
    function peerVoidBytes(address target) external {
        BytePeer(target).putBytes(stored);
    }
    function peerVoidString(address target) external {
        BytePeer(target).putString(title);
    }
}
