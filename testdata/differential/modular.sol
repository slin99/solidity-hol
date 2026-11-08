// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// mulDiv as OpenZeppelin Contracts 5.1 (MIT) writes it, with the helpers it
// calls from Panic and SafeCast.
library FullMath {
    uint256 internal constant UNDER_OVERFLOW = 0x11;
    uint256 internal constant DIVISION_BY_ZERO = 0x12;

    function panic(uint256 code) internal pure {
        assembly ("memory-safe") {
            mstore(0x00, 0x4e487b71)
            mstore(0x20, code)
            revert(0x1c, 0x24)
        }
    }

    function toUint(bool b) internal pure returns (uint256 u) {
        assembly ("memory-safe") {
            u := iszero(iszero(b))
        }
    }

    function ternary(bool condition, uint256 a, uint256 b) internal pure returns (uint256) {
        unchecked {
            return b ^ ((a ^ b) * toUint(condition));
        }
    }

    function mulDiv(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256 result) {
        unchecked {
            uint256 prod0 = x * y;
            uint256 prod1;
            assembly {
                let mm := mulmod(x, y, not(0))
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            if (prod1 == 0) {
                return prod0 / denominator;
            }

            if (denominator <= prod1) {
                panic(ternary(denominator == 0, DIVISION_BY_ZERO, UNDER_OVERFLOW));
            }

            uint256 remainder;
            assembly {
                remainder := mulmod(x, y, denominator)
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            uint256 twos = denominator & (0 - denominator);
            assembly {
                denominator := div(denominator, twos)
                prod0 := div(prod0, twos)
                twos := add(div(sub(0, twos), twos), 1)
            }

            prod0 |= prod1 * twos;

            uint256 inverse = (3 * denominator) ^ 2;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;

            result = prod0 * inverse;
            return result;
        }
    }
}

// addmod and mulmod: the built-ins over full-width sums and products, which
// panic on a zero modulus, and the Yul builtins, which give 0 for one.
contract Modular {
    uint256 public trace;

    error Stop();

    function addMod(uint256 a, uint256 b, uint256 k) public pure returns (uint256) {
        return addmod(a, b, k);
    }

    function mulMod(uint256 a, uint256 b, uint256 k) public pure returns (uint256) {
        return mulmod(a, b, k);
    }

    function uncheckedMulMod(uint256 a, uint256 b, uint256 k) public pure returns (uint256) {
        unchecked {
            return mulmod(a, b, k);
        }
    }

    // Narrower operands and literals convert to uint256.
    function narrow(uint8 a, uint16 b, uint32 k) public pure returns (uint256, uint256) {
        return (addmod(a, b, k), mulmod(a, 1000, k));
    }

    function literals(uint256 k) public pure returns (uint256, uint256) {
        return (addmod(2 ** 255, 2 ** 255, k), mulmod(2 ** 255, 4, k));
    }

    function step(uint256 d) internal returns (uint256) {
        trace = trace * 10 + d;
        return d;
    }

    // The operands in order, then the modulus.
    function ordered(uint256 k) public returns (uint256) {
        return addmod(step(1), step(2), step(k));
    }

    // An operand is read before a later operand assigns it.
    function snapshot() public pure returns (uint256) {
        uint256 x = 1;
        return addmod(x, addmod(x = 2, 0, 10), 10);
    }

    function stop(uint256 x) internal pure returns (uint256) {
        if (x == 0) revert Stop();
        return x;
    }

    // A zero modulus panics only once every operand is evaluated.
    function stopFirst(uint256 k) public pure returns (uint256) {
        return mulmod(1, stop(k), k);
    }

    function asmAddMod(uint256 a, uint256 b, uint256 k) public pure returns (uint256 r) {
        assembly {
            r := addmod(a, b, k)
        }
    }

    function asmMulMod(uint256 a, uint256 b, uint256 k) public pure returns (uint256 r) {
        assembly {
            r := mulmod(a, b, k)
        }
    }

    function mulDiv(uint256 x, uint256 y, uint256 d) public pure returns (uint256) {
        return FullMath.mulDiv(x, y, d);
    }
}
