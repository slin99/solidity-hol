// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Inline assembly over memory bytes and strings, which a block reads as
// their addresses: a signature split into its words, a string's digits
// written byte by byte through a pointer kept in a uint256, a reason bubbled
// up as revert data, a whole word stored into a shorter bytes, the shared
// empty bytes, and the length word read back.
contract AssemblyMemory {
    function split(bytes memory sig) public pure returns (bytes32 r, bytes32 s, uint8 v) {
        assembly {
            r := mload(add(sig, 0x20))
            s := mload(add(sig, 0x40))
            v := byte(0, mload(add(sig, 0x60)))
        }
    }

    function toString(uint256 value) public pure returns (string memory) {
        unchecked {
            uint256 length = 1;
            for (uint256 t = value; t >= 10; t /= 10) {
                length++;
            }
            string memory buffer = new string(length);
            uint256 ptr;
            assembly {
                ptr := add(buffer, add(32, length))
            }
            while (true) {
                ptr--;
                assembly {
                    mstore8(ptr, add(48, mod(value, 10)))
                }
                value /= 10;
                if (value == 0) break;
            }
            return buffer;
        }
    }

    function bubble(bytes memory reason) public pure {
        assembly {
            revert(add(32, reason), mload(reason))
        }
    }

    function wordInto() public pure returns (bytes memory b) {
        b = new bytes(5);
        assembly {
            mstore(add(b, 32), 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20)
        }
    }

    function lengths(bytes memory b, string memory s) public pure returns (uint256 m, uint256 n, uint256 z) {
        bytes memory empty;
        assembly {
            m := mload(b)
            n := mload(s)
            z := mload(empty)
        }
    }
}
