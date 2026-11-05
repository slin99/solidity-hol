// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Immutables during creation: read in a base constructor's argument before
// the derived contract's initializer assigns it, in a constructor modifier
// and in an internal function the constructor calls; a creation that reverts
// after assigning; and a constructor argument whose allocation crosses the
// memory limit only because creation reserves a word per immutable.
contract ImmutableBase {
    uint256 public immutable fromArg;

    constructor(uint256 x) {
        fromArg = x;
    }
}

contract ImmutableCreation is ImmutableBase {
    uint256 immutable size;
    uint256 immutable later = 5;
    uint256 public observed;
    uint256 public inModifier;

    modifier records() {
        inModifier = later;
        _;
    }

    constructor(bytes memory b, bool fail) ImmutableBase(later + 1) records {
        size = b.length;
        observed = helper();
        require(!fail);
    }

    function helper() internal view returns (uint256) {
        return size + later;
    }

    function sizes() external view returns (uint256, uint256) {
        return (size, fromArg);
    }
}
