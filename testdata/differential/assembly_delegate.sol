// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IDelegatePeer {
    function add(uint256 amount) external returns (uint256);
}

// Inline assembly delegatecall: OpenZeppelin v5.1.0's Proxy._delegate behind
// a fallback, and a delegatecall whose block goes on after it.
contract AssemblyDelegate {
    uint256 public total;
    address public impl;

    function _delegate(address implementation) internal {
        assembly {
            calldatacopy(0, 0, calldatasize())
            let result := delegatecall(gas(), implementation, 0, calldatasize(), 0, 0)
            returndatacopy(0, 0, returndatasize())
            switch result
            case 0 { revert(0, returndatasize()) }
            default { return(0, returndatasize()) }
        }
    }

    fallback() external {
        _delegate(impl);
    }

    function delegateAdd(uint256 amount) external returns (bool ok, uint256 size) {
        bytes4 sel = IDelegatePeer.add.selector;
        address target = impl;
        assembly {
            mstore(0, sel)
            mstore(4, amount)
            ok := delegatecall(gas(), target, 0, 36, 0, 0)
            size := returndatasize()
        }
    }
}
