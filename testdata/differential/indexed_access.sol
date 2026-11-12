// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract IndexedAccess {
    bytes32 private word;
    bytes private data;

    function fixed1(bytes1 b, uint256 i) external pure returns (bytes1) {
        return b[i];
    }

    function fixed16(bytes16 b, uint256 i) external pure returns (bytes1) {
        return b[i];
    }

    function fixed32(bytes32 b, uint256 i) external pure returns (bytes1) {
        return b[i];
    }

    function constantHash(uint256 i) external pure returns (bytes1) {
        return keccak256("indexed access")[i];
    }

    function memoryByte(bytes memory b, uint256 i) external pure returns (bytes1) {
        return b[i];
    }

    function calldataByte(bytes calldata b, uint256 i) external pure returns (bytes1) {
        return b[i];
    }

    function calldataArray(uint16[] calldata a, uint256 i) external pure returns (uint16) {
        return a[i];
    }

    function changeWord() private returns (uint256) {
        word = bytes32(uint256(0xff));
        return 0;
    }

    function capturedWord() external returns (bytes1) {
        word = hex"123456789abcdef0";
        return word[changeWord()];
    }

    function changeData() private returns (uint256) {
        data = hex"090807";
        return 1;
    }

    function liveStorageBytes() external returns (bytes1) {
        data = hex"010203";
        return data[changeData()];
    }

    function mutateBytes(bytes memory b) private pure returns (uint256) {
        b[1] = 0xee;
        return 1;
    }

    function liveMemoryBytes() external pure returns (bytes1) {
        bytes memory b = hex"010203";
        return b[mutateBytes(b)];
    }

    function mutateArray(uint256[] memory a) private pure returns (uint256) {
        a[0] = 19;
        return 0;
    }

    function liveMemoryArray() external pure returns (uint256) {
        uint256[] memory a = new uint256[](2);
        a[0] = 7;
        return a[mutateArray(a)];
    }
}
