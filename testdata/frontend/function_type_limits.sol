// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

// Function types the core does not model inside a body: function values in
// inline assembly and comparisons of function values. Those functions are
// unsupported; an internal function value in a local runs.
contract FunctionTypeLimits {
    function inc(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    function local(uint256 x) public pure returns (uint256) {
        function(uint256) pure returns (uint256) f = inc;
        return f(x);
    }

    function compares() public pure returns (bool) {
        function(uint256) pure returns (uint256) f = inc;
        return f == inc;
    }

    function inAssembly() public pure returns (uint256 r) {
        function(uint256) pure returns (uint256) f = inc;
        assembly { r := f }
    }
}
