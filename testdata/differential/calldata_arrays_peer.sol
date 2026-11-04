// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract ArrayPeer {
    function rev(uint256[] calldata a) external pure returns (uint256[] memory r) {
        r = new uint256[](a.length);
        for (uint256 i = 0; i < a.length; i++) {
            r[i] = a[a.length - 1 - i];
        }
    }
}
