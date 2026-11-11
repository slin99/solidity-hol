// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Inline assembly over calldata references: x.offset and x.length of a
// calldata byte sequence or dynamic array, and the plain name of a calldata
// static array, read and rebound.
library CalldataSlices {
    // OpenZeppelin's Calldata.emptyBytes
    function emptyBytes() internal pure returns (bytes calldata result) {
        assembly ("memory-safe") {
            result.offset := 0
            result.length := 0
        }
    }

    uint256 constant OFFSET_OR_LENGTH_MASK = 0xffffffff;
    uint256 constant SLICE_ERROR_SELECTOR = 0x3b99b53d;

    // Uniswap v4's CalldataDecoder.toBytes: argument i of an ABI-encoded
    // tuple of byte sequences
    function toBytes(bytes calldata _bytes, uint256 _arg) internal pure returns (bytes calldata res) {
        uint256 length;
        assembly ("memory-safe") {
            let lengthPtr :=
                add(_bytes.offset, and(calldataload(add(_bytes.offset, shl(5, _arg))), OFFSET_OR_LENGTH_MASK))
            length := and(calldataload(lengthPtr), OFFSET_OR_LENGTH_MASK)
            let offset := add(lengthPtr, 0x20)
            res.length := length
            res.offset := offset
            if lt(add(_bytes.length, _bytes.offset), add(length, offset)) {
                mstore(0, SLICE_ERROR_SELECTOR)
                revert(0x1c, 4)
            }
        }
    }
}

contract AssemblyCalldata {
    function bounds(bytes calldata b) external pure returns (uint256 o, uint256 l) {
        assembly {
            o := b.offset
            l := b.length
        }
    }

    function words(uint256[] calldata xs) external pure returns (uint256 o, uint256 l, uint256 first) {
        assembly {
            o := xs.offset
            l := xs.length
            first := calldataload(xs.offset)
        }
    }

    function tail(uint256[] calldata xs) external pure returns (uint256[] calldata ys) {
        require(xs.length > 0);
        assembly {
            ys.offset := add(xs.offset, 32)
            ys.length := sub(xs.length, 1)
        }
    }

    function argument(bytes calldata data, uint256 i) external pure returns (bytes calldata) {
        return CalldataSlices.toBytes(data, i);
    }

    function emptyLength() external pure returns (uint256) {
        return CalldataSlices.emptyBytes().length;
    }

    function where(uint256[2] calldata a) external pure returns (uint256 o) {
        assembly {
            o := a
        }
    }

    function pick(uint256[2] calldata a, uint256[2] calldata b, bool second) external pure returns (uint256[2] calldata r) {
        r = a;
        assembly {
            if second {
                r := b
            }
        }
    }

    // A reference rebound past the end of the calldata: solc reads zeros
    // there, the source model fails closed.
    function overLength(uint256[] calldata xs) external pure returns (uint256) {
        assembly {
            xs.length := add(xs.length, 100)
        }
        return xs.length;
    }

    function overOffset(bytes calldata b) external pure returns (uint256) {
        assembly {
            b.offset := calldatasize()
        }
        return b.length;
    }

    function overStatic(uint256[2] calldata a) external pure returns (uint256) {
        assembly {
            a := sub(calldatasize(), 32)
        }
        return a[0];
    }
}
