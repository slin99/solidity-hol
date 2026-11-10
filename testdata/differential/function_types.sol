// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

library Doubling {
    function twiceFirst(uint256 a, uint256 b) internal pure returns (uint256) {
        return 2 * a + b;
    }
}

function larger(uint256 a, uint256 b) pure returns (uint256) {
    return a > b ? a : b;
}

contract FunctionTypesBase {
    uint256 public counter;

    function combine(uint256 a, uint256 b) internal view virtual returns (uint256) {
        return a + b + counter;
    }

    // `combine` here names the base declaration; run on FunctionTypes, the
    // value is its override
    function overriddenValue(uint256 a, uint256 b) external view returns (uint256) {
        function(uint256, uint256) view returns (uint256) f = combine;
        return f(a, b);
    }
}

// Internal function values: references to private, internal, library, free
// and overridden functions, passed, returned, chosen and called.
contract FunctionTypes is FunctionTypesBase {
    uint224 public total;
    uint256 public scaled;

    modifier bump() {
        counter += 1;
        _;
    }

    function add(uint256 a, uint256 b) private pure returns (uint256) {
        return a + b;
    }

    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    function combine(uint256 a, uint256 b) internal view override returns (uint256) {
        return a * b + counter;
    }

    function bumped(uint256 a, uint256 b) internal bump returns (uint256) {
        return a + b + counter;
    }

    function applyView(function(uint256, uint256) view returns (uint256) op, uint256 a, uint256 b)
        internal view returns (uint256)
    {
        return op(a, b);
    }

    function applyNonpayable(function(uint256, uint256) returns (uint256) op, uint256 a, uint256 b)
        internal returns (uint256)
    {
        return op(a, b);
    }

    function privateValue(uint256 a, uint256 b) external view returns (uint256) {
        return applyView(add, a, b);
    }

    function libraryValue(uint256 a, uint256 b) external view returns (uint256) {
        return applyView(Doubling.twiceFirst, a, b);
    }

    function freeValue(uint256 a, uint256 b) external view returns (uint256) {
        return applyView(larger, a, b);
    }

    function modifiedValue(uint256 a, uint256 b) external returns (uint256) {
        return applyNonpayable(bumped, a, b);
    }

    function pick(bool s) internal pure returns (function(uint256, uint256) pure returns (uint256) r) {
        if (s) r = add;
    }

    function picked(bool s, uint256 a, uint256 b) external pure returns (uint256) {
        return pick(s)(a, b);
    }

    function chosen(bool s, uint256 a, uint256 b) external pure returns (uint256) {
        function(uint256, uint256) pure returns (uint256) f = s ? add : sub;
        return f(a, b);
    }

    function reassigned(uint256 a, uint256 b) external pure returns (uint256) {
        function(uint256, uint256) pure returns (uint256) f = add;
        f = sub;
        return f(a, b);
    }

    function unassigned() external pure returns (uint256) {
        function(uint256, uint256) pure returns (uint256) f;
        return f(1, 2);
    }

    function applyPure(function(uint256, uint256) pure returns (uint256) g) internal pure returns (uint256) {
        return g(3, 1);
    }

    // the callee is the value before the argument reassigns it
    function calleeBeforeArguments() external pure returns (uint256) {
        function(uint256, uint256) pure returns (uint256) f = add;
        uint256 first = f(9, applyPure(f = sub));
        return first * 100 + f(7, 2);
    }

    function step(uint256 x) internal returns (uint256) {
        counter = counter * 10 + x;
        return x;
    }

    function chooser() internal returns (function(uint256, uint256) view returns (uint256)) {
        step(1);
        return combine;
    }

    // the callee expression runs before the arguments
    function order() external returns (uint256) {
        return chooser()(step(2), step(3));
    }

    // the arguments run before the zero value's panic: x = 0 fails in them
    function zeroAfterArguments(uint256 x) external returns (uint256) {
        function(uint256, uint256) view returns (uint256) f;
        return f(step(4), x - 1);
    }

    // function values as tuple components: returned, destructured, assigned
    function pickPair(bool s)
        internal pure returns (function(uint256, uint256) pure returns (uint256), uint256)
    {
        return (s ? add : sub, 7);
    }

    function pairCall(bool s, uint256 a) external pure returns (uint256) {
        (function(uint256, uint256) pure returns (uint256) g, uint256 b) = pickPair(s);
        return g(a, b);
    }

    function tupleAssigned(uint256 a) external pure returns (uint256) {
        function(uint256, uint256) pure returns (uint256) f = add;
        uint256 b;
        (f, b) = (sub, 2);
        return f(a, b);
    }

    // OpenZeppelin Votes._push: the operation is a parameter
    function _add(uint224 a, uint224 b) private pure returns (uint224) {
        return a + b;
    }

    function _subtract(uint224 a, uint224 b) private pure returns (uint224) {
        return a - b;
    }

    function _push(function(uint224, uint224) view returns (uint224) op, uint224 delta)
        private returns (uint224 oldValue, uint224 newValue)
    {
        oldValue = total;
        newValue = op(oldValue, delta);
        total = newValue;
    }

    function moveVotes(bool mint, uint224 amount) external returns (uint224, uint224) {
        if (mint) return _push(_add, amount);
        return _push(_subtract, amount);
    }

    // Aave ScaledBalanceTokenBase._mintScaled: the rounding is a parameter
    function _mintScaled(
        uint256 amount,
        uint256 index,
        function(uint256, uint256) internal pure returns (uint256) getTokenBalance
    ) internal returns (uint256) {
        uint256 before = getTokenBalance(scaled, index);
        scaled += amount;
        return getTokenBalance(scaled, index) - before;
    }

    function getBalance(uint256 s, uint256 index) internal pure returns (uint256) {
        return s * index / 1000;
    }

    function mintScaled(uint256 amount, uint256 index) external returns (uint256) {
        return _mintScaled(amount, index, getBalance);
    }

    function typedComponents(address a, uint32 x) external pure returns (bool) {
        function(address, bytes4) pure returns (bool) f = matches;
        return f(a, bytes4(x));
    }

    function matches(address a, bytes4 b) internal pure returns (bool) {
        return uint32(uint160(a)) == uint32(b);
    }
}
