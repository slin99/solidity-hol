// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.37;

contract TransferPeer {
    fallback() external payable {
        assembly {
            switch sload(0)
            case 0 { mstore(0, 0x1234) return(0, 32) }
            case 1 { mstore(0, 0x5678) revert(0, 32) }
            default { sstore(1, 1) }
        }
    }
}
