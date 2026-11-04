// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Inline assembly over value-type locals and state variable locations: reads
// and writes of locals (cleaned on the way back), slot and offset, storage,
// scratch memory, control flow, functions, logs, the block ending the call
// with return, stop or revert, and blocks in and under modifiers.
contract InlineAssembly {
    uint256 total;
    uint64 packedLow;
    uint64 packedHigh;
    mapping(uint256 => uint256) balances;

    function add(uint256 x, uint256 y) public pure returns (uint256 r) {
        assembly {
            r := add(x, y)
        }
    }

    // Writes leave high-order garbage the Solidity side cleans.
    function dirtyUint8(uint256 x) public pure returns (uint8 r) {
        assembly {
            r := x
        }
    }

    function dirtyBool(uint256 x) public pure returns (bool b) {
        assembly {
            b := x
        }
    }

    function signed(int8 x) public pure returns (int256 w, int8 back) {
        assembly {
            w := x
            back := add(x, 0x100)
        }
    }

    // bytesN sits in the high-order bytes of the word.
    function fixedBytes(bytes4 b) public pure returns (uint256 w, bytes4 back) {
        assembly {
            w := b
            back := shl(224, 0xdeadbeef)
        }
    }

    // bytesN(0) and a hex literal of N bytes, over words assembly writes.
    function literalBytes() public pure returns (bool zero, bytes32 wide) {
        bytes32 x = bytes32(uint256(1));
        assembly {
            x := iszero(x)
        }
        zero = x == bytes32(0);
        bytes1 n = bytes1(bytes16(0x31313131313131313131313131313131));
        assembly {
            wide := n
        }
    }

    function addressBits(address a) public pure returns (uint256 w, address back) {
        assembly {
            w := a
            back := not(0)
        }
    }

    function locations() public pure returns (uint256 s, uint256 o, uint256 s2, uint256 o2) {
        assembly {
            s := packedHigh.slot
            o := packedHigh.offset
            s2 := total.slot
            o2 := total.offset
        }
    }

    function store(uint256 v) public {
        assembly {
            sstore(total.slot, v)
        }
    }

    function load() public view returns (uint256 v) {
        assembly {
            v := sload(total.slot)
        }
    }

    // The mapping's slot computed in scratch memory.
    function balanceOf(uint256 k) public view returns (uint256 v) {
        assembly {
            mstore(0, k)
            mstore(0x20, balances.slot)
            v := sload(keccak256(0, 0x40))
        }
    }

    function loops(uint256 n) public pure returns (uint256 acc) {
        assembly {
            function triple(v) -> w {
                w := mul(v, 3)
            }
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                if eq(i, 7) { break }
                if iszero(mod(i, 2)) { continue }
                acc := add(acc, triple(i))
            }
        }
    }

    function classify(uint256 x) public pure returns (uint256 r) {
        assembly {
            switch x
            case 0 { r := 10 }
            case 1 { r := 20 }
            default { r := 30 }
        }
    }

    function blockThenSolidity(uint8 x) public pure returns (uint8) {
        uint8 y = x;
        assembly {
            y := add(y, 1)
        }
        return y + 1;
    }

    function emitLog(uint256 v) public {
        assembly {
            mstore(0, v)
            log1(0, 0x20, 0x1234)
        }
    }

    function sender() public view returns (address a) {
        assembly {
            a := caller()
        }
    }

    function returnFromAssembly(uint256 v) public pure returns (uint256) {
        assembly {
            mstore(0x80, v)
            return(0x80, 0x20)
        }
    }

    function stopEarly(uint256 v) public {
        total = 1;
        assembly {
            stop()
        }
        total = v;
    }

    function revertFromAssembly(uint256 v) public {
        total = 5;
        assembly {
            mstore(0, v)
            revert(0, 0x20)
        }
    }

    // A block writing a modifier parameter.
    modifier scaled(uint256 k) {
        assembly {
            k := mul(k, 2)
        }
        total = k;
        _;
    }

    // A stop in a modifier skips the body and the rest of the modifier.
    modifier haltIf(uint256 c) {
        assembly {
            if iszero(c) { stop() }
        }
        _;
        total = 99;
    }

    function withModifier(uint256 k) public scaled(k) returns (uint256) {
        return total;
    }

    function haltInModifier(uint256 c) public haltIf(c) {
        total = 7;
    }

    // A return in the body passes out through the modifier's placeholder.
    function haltUnderModifier(uint256 v) public scaled(v) returns (uint256) {
        assembly {
            mstore(0x80, v)
            return(0x80, 0x20)
        }
    }
}
