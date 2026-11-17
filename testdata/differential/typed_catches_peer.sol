// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract TypedCatchPeer {
    function run(bytes calldata data, uint256 mode) external returns (uint256) {
        if (mode == 0) return 7;
        if (mode == 2) {
            assembly { return(0, 0) }
        }
        assembly {
            calldatacopy(0, data.offset, data.length)
            revert(0, data.length)
        }
    }
}
