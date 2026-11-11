// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Inline assembly over memory arrays of value types, which a block reads as
// their addresses: OpenZeppelin's unchecked element read, Morpho's in-place
// writes into a fresh array, a static array (no length word), an array
// decoded from an external call's return data, and the length word.
contract AssemblyArrays {
    function unsafeMemoryAccess(address[] memory arr, uint256 pos) internal pure returns (address res) {
        assembly {
            res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
        }
    }

    function pick(address[] memory arr, uint256 pos) public pure returns (address) {
        return unsafeMemoryAccess(arr, pos);
    }

    function fill(uint256 n, bytes32 seed) public pure returns (bytes32[] memory res) {
        res = new bytes32[](n);
        for (uint256 i; i < n;) {
            bytes32 word = keccak256(abi.encode(seed, i++));
            assembly ("memory-safe") {
                mstore(add(res, mul(i, 32)), word)
            }
        }
    }

    function bump(uint8[] memory xs) public pure returns (uint8[] memory) {
        assembly {
            let n := mload(xs)
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let p := add(add(xs, 0x20), mul(i, 0x20))
                mstore(p, and(add(mload(p), 1), 0xff))
            }
        }
        return xs;
    }

    function swapStatic(uint256 a, uint256 b) public pure returns (uint256[2] memory s, uint256 first) {
        s[0] = a;
        s[1] = b;
        assembly {
            first := mload(s)
            let t := mload(add(s, 0x20))
            mstore(add(s, 0x20), first)
            mstore(s, t)
        }
    }

    function signs(int8[] memory xs) public pure returns (uint256 w, int8[] memory) {
        assembly {
            w := mload(add(xs, 0x20))
            mstore(add(xs, 0x40), not(0))
        }
        return (w, xs);
    }

    function words(uint256 n) external pure returns (bytes32[] memory r) {
        r = new bytes32[](n);
        for (uint256 i; i < n; i++) {
            r[i] = bytes32(i + 0x100);
        }
    }

    function third(uint256 n) public view returns (bytes32 w, uint256 len) {
        bytes32[] memory data = this.words(n);
        assembly {
            len := mload(data)
            w := mload(add(data, 0x60))
        }
    }
}
