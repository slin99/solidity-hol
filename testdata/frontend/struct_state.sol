// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// A state variable of a struct the core cannot hold (a string-keyed
// mapping member) rejects the unit.
library Keys {
    struct Named {
        mapping(string => uint256) m;
        uint8 n;
    }
}

contract StructState {
    Keys.Named named;

    function count() external view returns (uint8) {
        return named.n;
    }
}
