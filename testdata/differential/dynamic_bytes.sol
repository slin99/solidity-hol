// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface BytePeer {
    function raw(uint256 mode) external pure returns (bytes memory);
    function echo(bytes calldata data, string calldata text) external returns (bytes memory, string memory);
}

contract DynamicBytes {
    string private title;
    bytes private stored;
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
}

contract EchoPeer {
    function raw(uint256 mode) external pure returns (bytes memory) {
        assembly {
            mstore(0, 32)
            switch mode
            case 0 {
                mstore(32, 3)
                mstore(64, shl(232, 0x616263))
                return(0, 67)
            }
            case 1 {
                mstore(32, 3)
                return(0, 64)
            }
            case 3 {
                mstore(32, 0xffffffffffffff40)
                return(0, 64)
            }
            default {
                mstore(32, 0x10000000000000000)
                return(0, 64)
            }
        }
    }

    function echo(bytes calldata data, string calldata text) external pure returns (bytes memory, string memory) {
        return (data, text);
    }
}
