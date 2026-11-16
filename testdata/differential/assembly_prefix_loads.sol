// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Sub-word big-endian loads as Solady writes them: shr(k, mload(p)) and
// byte(0, mload(p)) keep only the leading bytes of the word read, so the
// bytes they shift out may be ones the block never wrote.
contract AssemblyPrefixLoads {
    // The address in the low 20 bytes of the word at 0x00, read back from
    // 0x0c, as ERC20Votes._delegate does; [0x20, 0x2c) is never written.
    function addressAt(address a) external pure returns (address r) {
        assembly {
            mstore(0x00, a)
            r := shr(96, mload(0x0c))
        }
    }

    // The low half of a word written at 0x10, read from 0x20, as
    // RedBlackTreeLib does; [0x30, 0x40) is never written.
    function lowHalf(uint256 v) external pure returns (uint256 r) {
        assembly {
            mstore(0x10, v)
            r := shr(128, mload(0x20))
        }
    }

    // The byte at s[i] of the 32 bytes of v, as JSONParserLib reads
    // characters: at the last one the rest of the word is past s's end.
    function charAt(uint256 v, uint256 i) external pure returns (uint256 r) {
        bytes memory s = abi.encodePacked(v);
        assembly {
            r := byte(0, mload(add(add(s, 0x20), i)))
        }
    }

    // The four bytes from s[i]; from i = 29 on, some are past s's end.
    function fourAt(uint256 v, uint256 i) external pure returns (uint256 r) {
        bytes memory s = abi.encodePacked(v);
        assembly {
            r := shr(224, mload(add(add(s, 0x20), i)))
        }
    }
}
