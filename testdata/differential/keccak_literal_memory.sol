// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract KeccakLiteralMemory {
    bytes32 public constant ROLE = keccak256("ROLE");

    function stringLiteral() public pure returns (uint256 gap, bytes32 hash) {
        bytes memory beforeHash = new bytes(1);
        hash = keccak256("abcdef");
        bytes memory afterHash = new bytes(1);
        assembly {
            gap := sub(afterHash, beforeHash)
        }
    }

    function hexLiteral() public pure returns (uint256 gap, bytes32 hash) {
        bytes memory beforeHash = new bytes(1);
        hash = keccak256(hex"aabbcc");
        bytes memory afterHash = new bytes(1);
        assembly {
            gap := sub(afterHash, beforeHash)
        }
    }

    function emptyString() public pure returns (uint256 gap, bytes32 hash) {
        bytes memory beforeHash = new bytes(1);
        hash = keccak256("");
        bytes memory afterHash = new bytes(1);
        assembly {
            gap := sub(afterHash, beforeHash)
        }
    }

    function emptyHex() public pure returns (uint256 gap, bytes32 hash) {
        bytes memory beforeHash = new bytes(1);
        hash = keccak256(hex"");
        bytes memory afterHash = new bytes(1);
        assembly {
            gap := sub(afterHash, beforeHash)
        }
    }

    function multiwordLiteral() public pure returns (uint256 gap, bytes32 hash) {
        bytes memory beforeHash = new bytes(1);
        hash = keccak256("0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789");
        bytes memory afterHash = new bytes(1);
        assembly {
            gap := sub(afterHash, beforeHash)
        }
    }

    function constantHash() public pure returns (uint256 gap, bytes32 hash) {
        bytes memory beforeHash = new bytes(1);
        hash = ROLE;
        bytes memory afterHash = new bytes(1);
        assembly {
            gap := sub(afterHash, beforeHash)
        }
    }

    function memoryBytes() public pure returns (uint256 gap, bytes32 hash) {
        bytes memory beforeHash = new bytes(1);
        bytes memory data = "abcdef";
        hash = keccak256(data);
        bytes memory afterHash = new bytes(1);
        assembly {
            gap := sub(afterHash, beforeHash)
        }
    }
}
