// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// A state variable of a struct the core cannot hold (a function-typed
// member) rejects the unit.
library Keys {
    struct Named {
        function () external f;
        uint8 n;
    }
}

contract StructState {
    Keys.Named named;

    function count() external view returns (uint8) {
        return named.n;
    }
}
