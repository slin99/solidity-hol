// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// abi.decode of memory bytes into elementary types: one value, several, data
// made by abi.encode or given by the caller, short data, values outside their
// type, and data after the encoding.
contract AbiDecodes {
    function selector(bytes memory data) public pure returns (bytes4) {
        return abi.decode(data, (bytes4));
    }

    function several(bytes memory data)
        public pure returns (uint8 a, bool b, address c, int16 d, uint256 e)
    {
        (a, b, c, d, e) = abi.decode(data, (uint8, bool, address, int16, uint256));
    }

    function roundTrip(uint256 x, address y, bytes32 z) public pure returns (bool) {
        bytes memory data = abi.encode(x, y, z);
        (uint256 x1, address y1, bytes32 z1) = abi.decode(data, (uint256, address, bytes32));
        return x1 == x && y1 == y && z1 == z;
    }

    // The decoded value of the bytes a second local aliases.
    function aliased(uint256 x) public pure returns (uint256) {
        bytes memory data = abi.encode(x);
        bytes memory same = data;
        data[31] = bytes1(uint8(7));
        return abi.decode(same, (uint256));
    }

    function matchesSelector(bytes memory data) public pure returns (bool) {
        return data.length == 32 && abi.decode(data, (bytes4)) == bytes4(0x12345678);
    }
}
