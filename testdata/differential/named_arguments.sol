// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Named arguments: evaluated in the call's order, then passed in the order
// of the parameters, for internal, bound library, super and external calls,
// events and errors.
library Weights {
    function weigh(uint256 x, uint256 a, uint256 b) internal pure returns (uint256) {
        return x * 10000 + a * 100 + b;
    }
}

contract NamedBase {
    function mix(uint256 a, uint256 b) public virtual returns (uint256) {
        return a * 100 + b;
    }

    // An override may rename its parameters: a call takes the names of the
    // declaration it names, not those of the function that runs.
    function swap(uint256 a, uint256 b) public pure virtual returns (uint256) {
        return a * 10 + b;
    }

    function swapFromBase() external pure returns (uint256) {
        return swap({a: 1, b: 2});
    }
}

contract NamedArguments is NamedBase {
    using Weights for uint256;

    uint256 public trace;

    event Pair(uint256 indexed a, uint256 b);
    error Bad(uint256 a, bool b);

    // Appends tag to trace, which so records the order of evaluation.
    function tick(uint256 tag) internal returns (uint256) {
        trace = trace * 10 + tag;
        return tag;
    }

    function digits(uint256 a, uint256 b, uint256 c) internal pure returns (uint256) {
        return a * 100 + b * 10 + c;
    }

    function pair(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * 100 + b;
    }

    function wide(uint256 big, uint16 small) internal pure returns (uint256) {
        return big * 100000 + small;
    }

    function lengths(bytes memory a, uint256[] memory b) internal pure returns (uint256) {
        return a.length * 100 + b.length;
    }

    function mix(uint256 a, uint256 b) public override returns (uint256) {
        return super.mix({b: b, a: a}) + 1;
    }

    function internalOrder() external returns (uint256 r, uint256 t) {
        trace = 0;
        r = digits({c: tick(3), a: tick(1), b: tick(2)});
        t = trace;
    }

    function inParameterOrder() external pure returns (uint256) {
        return digits({a: 1, b: 2, c: 3});
    }

    function assignOrder(uint256 x) external pure returns (uint256) {
        return pair({b: x, a: x = 5});
    }

    function converted(uint8 x) external pure returns (uint256) {
        return wide({small: x, big: 7});
    }

    function memoryArguments() external pure returns (uint256) {
        return lengths({b: new uint256[](3), a: "hello"});
    }

    function boundOrder() external returns (uint256 r, uint256 t) {
        trace = 0;
        uint256 x = 9;
        r = x.weigh({b: tick(8), a: tick(7)});
        t = trace;
    }

    function superOrder() external returns (uint256 r, uint256 t) {
        trace = 0;
        r = super.mix({b: tick(2), a: tick(1)});
        t = trace;
    }

    function overridden() external returns (uint256) {
        return mix({b: 4, a: 3});
    }

    function externalOrder() external returns (uint256 r, uint256 t) {
        trace = 0;
        r = this.mix({b: tick(6), a: tick(5)});
        t = trace;
    }

    function payment(uint256 a, uint256 b) external payable returns (uint256) {
        return a * 100 + b * 10 + msg.value;
    }

    function externalValueOrder() external payable returns (uint256 r, uint256 t) {
        trace = 0;
        r = this.payment{value: tick(4)}({b: tick(6), a: tick(5)});
        t = trace;
    }

    function swap(uint256 b, uint256 a) public pure override returns (uint256) {
        return b * 10 + a;
    }

    function swapFromDerived() external pure returns (uint256) {
        return swap({a: 1, b: 2});
    }

    function emitOrder() external returns (uint256) {
        trace = 0;
        emit Pair({b: tick(2), a: tick(1)});
        return trace;
    }

    function revertOrder() external {
        trace = 0;
        revert Bad({b: tick(3) == 3, a: trace});
    }
}
