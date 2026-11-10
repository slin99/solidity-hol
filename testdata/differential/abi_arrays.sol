// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract AbiArrays {
    uint16[] numbers;
    bytes[] chunks;

    function memoryArrays(bytes[] memory b, address[] memory a,
                          uint256[] memory u, bytes32[] memory w)
        external pure returns (bytes memory)
    {
        return abi.encode(b, a, u, w);
    }

    function calldataArrays(bytes[] calldata b, address[] calldata a,
                            uint256[] calldata u, bytes32[] calldata w)
        external pure returns (bytes memory)
    {
        return abi.encode(b, a, u, w);
    }

    function nestedMemory(uint256[][] memory a) external pure returns (bytes memory) {
        return abi.encode(a);
    }

    function nestedCalldata(bytes[][] calldata a) external pure returns (bytes memory) {
        return abi.encode(a);
    }

    function fixedMemory(int8[2][2] memory a) external pure returns (bytes memory) {
        return abi.encode(a);
    }

    function fixedElements(uint16[2][] calldata a) external pure returns (bytes memory) {
        return abi.encode(a);
    }

    function storedNumbers() external view returns (bytes memory) {
        return abi.encode(numbers);
    }

    function storedBlobs() external view returns (bytes memory) {
        return abi.encode(chunks);
    }

    function mutate() internal returns (uint256) {
        numbers[0] = 7;
        return 1;
    }

    function afterArgumentSideEffect() external returns (bytes memory) {
        return abi.encode(numbers, mutate());
    }

    function selector(bytes4 s, bytes[] calldata a) external pure returns (bytes memory) {
        return abi.encodeWithSelector(s, a);
    }

    function signature(bytes32[] memory a) external pure returns (bytes memory) {
        return abi.encodeWithSignature("receiveWords(bytes32[])", a);
    }
}
