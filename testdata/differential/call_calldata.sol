// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;
import "./call_calldata_types.sol";

contract CallCalldata {
    struct Data { uint256 n; bytes blob; }
    uint8[] stored;
    int16[2] signedStored;
    bytes2[] bytesStored;

    function getBalance(address peer, address owner) external view returns (uint256) {
        return GetterView(peer).balanceOf(owner);
    }
    function getScalar(address peer) external view returns (uint256) {
        return GetterView(peer).scalar();
    }
    function getArray(address peer, uint256 index) external view returns (uint16) {
        return GetterView(peer).values(index);
    }
    function getNamed(address peer, address owner, uint256 index) external view returns (uint256) {
        return GetterView(peer).nested({index: index, owner: owner});
    }
    function getItem(address peer) external view returns (uint256, bytes memory) {
        return GetterView(peer).item();
    }
    function getBlob(address peer) external view returns (bytes memory) {
        return GetterView(peer).blob();
    }
    function getConstant(address peer) external view returns (uint256) {
        return GetterView(peer).constantValue();
    }
    function tryArray(address peer, uint256 index) external view returns (uint256) {
        try GetterView(peer).values(index) returns (uint16 value) { return value; }
        catch { return 999; }
    }
    function signature() external pure returns (bytes4) { return msg.sig; }
    function internalSignature() external pure returns (bytes4) { return readSignature(); }
    function readSignature() internal pure returns (bytes4) { return msg.sig; }
    fallback(bytes calldata) external returns (bytes memory) { return abi.encode(msg.sig); }

    function structLocal(bool first, Data calldata a, Data calldata b)
        external pure returns (uint256, uint256)
    {
        Data calldata local;
        if (first) local = a; else local = b;
        return (local.n, local.blob.length);
    }
    function arrayLocal(bool first, uint256[] calldata a, uint256[] calldata b)
        external pure returns (uint256, uint256)
    {
        uint256[] calldata local;
        if (first) local = a; else local = b;
        return (local.length, local[0]);
    }
    function bytesLocal(bytes calldata input) external pure returns (bytes memory) {
        bytes calldata local;
        local = input;
        return local;
    }
    function fixedLocal(uint256[2] calldata input) external pure returns (uint256) {
        uint256[2] calldata local;
        local = input;
        return local[1];
    }
    function assemblyLocal(uint256[] calldata input) external pure returns (uint256) {
        uint256[] calldata local;
        assembly { local.offset := input.offset local.length := input.length }
        return local[0];
    }
    function packedMemory(uint8[] memory input) external pure returns (bytes memory) {
        return abi.encodePacked(input);
    }
    function packedCalldata(int16[] calldata input) external pure returns (bytes memory) {
        return abi.encodePacked(input);
    }
    function packedFixed(bytes2[2] calldata input) external pure returns (bytes memory) {
        return abi.encodePacked(input);
    }
    function packedHashes(bytes32[] memory input) external pure returns (bytes memory) {
        return abi.encodePacked(input);
    }
    function packedStored() external view returns (bytes memory) { return abi.encodePacked(stored); }
    function packedSignedStored() external view returns (bytes memory) { return abi.encodePacked(signedStored); }
    function packedBytesStored() external view returns (bytes memory) { return abi.encodePacked(bytesStored); }
}
