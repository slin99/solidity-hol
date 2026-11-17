// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract ArrayEvents {
    uint16[] numbers;
    bytes[] chunks;

    event Scalars(uint256[] indexed topic, uint256[] data);
    event Signed(int8[2] indexed topic, int8[2] data);
    event Nested(uint256[][] indexed topic, uint256[][] data);
    event Blobs(bytes[] indexed topic, bytes[] data);
    event Text(string[] indexed topic, string[] data);
    event Proposal(address[] targets, uint256[] values, string[] signatures, bytes[] calldatas);
    event Stored(uint16[] indexed topic, uint16[] data, uint256 marker);
    event Anonymous(uint256[] indexed topic, uint256 indexed marker) anonymous;

    function scalarsMemory(uint256[] memory a) external {
        emit Scalars(a, a);
    }
    function scalarsCalldata(uint256[] calldata a) external {
        emit Scalars(a, a);
    }
    function signedFixed(int8[2] calldata a) external {
        emit Signed(a, a);
    }
    function nestedMemory(uint256[][] memory a) external {
        emit Nested(a, a);
    }
    function nestedCalldata(uint256[][] calldata a) external {
        emit Nested(a, a);
    }
    function blobsMemory(bytes[] memory a) external {
        emit Blobs(a, a);
    }
    function blobsCalldata(bytes[] calldata a) external {
        emit Blobs(a, a);
    }
    function texts(string[] memory a) external {
        emit Text(a, a);
    }
    function proposal(address[] calldata a, uint256[] calldata v,
                      string[] calldata s, bytes[] calldata b) external {
        emit Proposal(a, v, s, b);
    }
    function stored() external {
        emit Stored(numbers, numbers, 0);
    }
    function storedBlobs() external {
        emit Blobs(chunks, chunks);
    }
    function mutate() internal returns (uint256) {
        numbers[0] = 7;
        return 1;
    }
    function afterArgumentSideEffect() external {
        emit Stored(numbers, numbers, mutate());
    }
    function anonymousEvent(uint256[] calldata a) external {
        emit Anonymous(a, 9);
    }
    function rolledBack(uint256[] calldata a) external {
        emit Scalars(a, a);
        revert();
    }
}
