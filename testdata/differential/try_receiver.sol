// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract TryReceiver {
    uint256 private calls;

    function receiveToken(uint256 mode) external returns (bytes4) {
        calls += 1;
        if (mode == 1) revert("rejected");
        if (mode == 2) {
            assembly { revert(0, 0) }
        }
        if (mode == 3) {
            assembly { return(0, 0) }
        }
        if (mode == 4) return bytes4(0);
        return bytes4(0x150b7a02);
    }

    function count() external view returns (uint256) {
        return calls;
    }

    function ping() external {}
}
