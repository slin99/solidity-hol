// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// SELFDESTRUCT under EIP-6780, reached by delegatecalling the peer's
// selfdestructing fallback: a contract destroyed in the transaction that
// created it is deleted when the transaction ends, a revert discards the
// pending deletion, and one destroyed in a later transaction keeps its code
// and storage.
contract SelfDestructs {
    uint256 public x;

    constructor(bool destroy, bool fail) {
        x = 1;
        if (destroy) _destroy();
        if (fail) revert("after destroy");
    }

    function destroy() external {
        x = 2;
        _destroy();
    }

    function _destroy() internal {
        address peer = address(uint160(0x5000));
        assembly {
            if iszero(delegatecall(gas(), peer, 0, 0, 0, 0)) { revert(0, 0) }
        }
    }
}
