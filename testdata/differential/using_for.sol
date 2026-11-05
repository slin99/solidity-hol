// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

library Arith {
    uint256 constant BONUS = 7;
    uint256 constant DOUBLE_BONUS = BONUS * 2;

    error TooBig(uint256 value);

    function addBonus(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b + BONUS;
    }

    function twice(uint256 a) private pure returns (uint256) {
        return addBonus(a, a);
    }

    function capped(uint256 a) internal pure returns (uint256) {
        if (a > 1000) revert TooBig(a);
        return twice(twice(a));
    }

    function factorial(uint256 n) internal pure returns (uint256) {
        if (n == 0) return 1;
        return n * factorial(n - 1);
    }

    function combine(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * 1000 + b;
    }

    function narrow(uint8 a) internal pure returns (uint8) {
        return a + 1;
    }
}

library Arrays {
    function sum(uint256[] memory xs) internal pure returns (uint256 total) {
        for (uint256 i = 0; i < xs.length; i++) total += xs[i];
    }

    function fill(uint256[] memory xs, uint256 v) internal pure {
        for (uint256 i = 0; i < xs.length; i++) xs[i] = v;
    }
}

// Not used by the contract: its public function and struct are not imported.
library Unused {
    struct Pair { uint256 a; uint256 b; }

    function external_(uint256 a) public pure returns (uint256) {
        return a;
    }
}

using Arith for uint256;

contract UsingFor {
    using Arrays for uint256[];
    using Arith for uint8;

    uint256 public counter;

    function bound(uint256 a, uint256 b) external pure returns (uint256) {
        return a.addBonus(b);
    }

    function direct(uint256 a) external pure returns (uint256) {
        return Arith.capped(a) + Arith.DOUBLE_BONUS;
    }

    function recursive(uint256 n) external pure returns (uint256) {
        return n.factorial();
    }

    function narrowed(uint8 a) external pure returns (uint8) {
        return a.narrow();
    }

    function arrays(uint256 n, uint256 v) external pure returns (uint256, uint256) {
        uint256[] memory xs = new uint256[](n);
        xs.fill(v);
        xs[0] = 1;
        return (xs.sum(), xs.length);
    }

    function next() internal returns (uint256) {
        counter += 1;
        return counter * 10;
    }

    // The receiver is evaluated before the arguments.
    function order() external returns (uint256) {
        return next().combine(next());
    }

    function literal() external pure returns (uint256) {
        return uint256(3).addBonus(4);
    }
}
