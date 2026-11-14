// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract TrySuccessPeer {
    fallback() external {
        assembly {
            let p := add(4, calldataload(4))
            let n := calldataload(p)
            calldatacopy(0, add(p, 32), n)
            if calldataload(36) { revert(0, n) }
            return(0, n)
        }
    }
}
