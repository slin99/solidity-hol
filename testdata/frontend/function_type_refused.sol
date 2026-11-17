// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

// Function types the core does not model in a unit's storage layout or in a
// function header: a function value in storage and an external function type
// parameter. Either refuses the whole unit.
contract FunctionTypeRefused {
    function(uint256) internal pure returns (uint256) stored;

    function readsStored(uint256 x) public view returns (uint256) {
        return stored(x);
    }

    function external_(function(uint256) external view returns (uint256) g)
        internal view returns (uint256)
    {
        return g(1);
    }
}
