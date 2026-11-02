// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Declarations imports.sol takes from another file: a file-level struct, an
// interface with an event, and an abstract base contract.

struct Point {
    uint256 x;
    uint256 y;
}

interface ICounter {
    event Bumped(uint256 count);

    function count() external view returns (uint256);
}

abstract contract Counter is ICounter {
    uint256 internal n;

    function bump(uint256 by) public virtual returns (uint256) {
        n += by;
        emit Bumped(n);
        return n;
    }
}
