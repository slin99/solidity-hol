// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Constants and state variable locations read by inline assembly: integer and
// bool constants, folded and through another constant, read at the top
// of a block and inside a Yul function, a function whose parameter and
// result reuse a constant's name, and a Yul function reading x.slot and
// x.offset.
contract AssemblyConstants {
    uint16 x;
    uint16 y;
    uint256 z;

    uint256 constant FIVE = 2 + 3;
    uint256 constant SEVEN = 7;
    uint256 constant ALSO_SEVEN = SEVEN;
    int8 constant MINUS_ONE = -1;
    bool constant YES = true;
    uint8 constant SMALL = 255;

    function values() public pure
        returns (uint256 a, uint256 b, uint256 c, uint256 d, uint256 g)
    {
        assembly {
            a := FIVE
            b := ALSO_SEVEN
            c := MINUS_ONE
            d := YES
            g := SMALL
        }
    }

    function inFunction(uint256 v) public pure returns (uint256 r, uint256 s, uint256 t) {
        assembly {
            function scaled(w) -> q {
                q := mul(w, FIVE)
            }
            function shadowed(FIVE) -> SEVEN {
                SEVEN := add(FIVE, 1)
                SEVEN := add(SEVEN, 1)
            }
            let k := SEVEN
            r := scaled(v)
            s := shadowed(v)
            t := add(FIVE, k)
        }
    }

    function unchecked_() public pure returns (uint256 r) {
        unchecked {
            assembly {
                r := add(MINUS_ONE, SMALL)
            }
        }
    }

    // A Yul function writing through a slot and reading an offset.
    function locationsInFunction() public returns (uint256 o, uint256 stored) {
        assembly {
            function f() -> o1 {
                sstore(z.slot, 7)
                o1 := y.offset
            }
            o := f()
        }
        stored = z;
    }
}
