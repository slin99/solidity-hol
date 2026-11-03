// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract CalldataBytes {
    uint256 private size;

    constructor(uint256 x) {
        size = msg.data.length + x;
        if (x == 0) size = uint8(msg.data[0]);
    }

    fallback() external {
        assert(msg.data.length == 0);
    }

    function dataLength() external pure returns (uint256) {
        return (msg.data).length;
    }

    function byteAt(uint256 i) external pure returns (bytes1) {
        return (msg.data)[i];
    }

    function checkLength(uint256 expected) external pure {
        assert(msg.data.length == expected);
    }
}
