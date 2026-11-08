// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IReceiver {
    function receiveToken(uint256 mode) external returns (bytes4);
    function count() external view returns (uint256);
    function ping() external;
}

contract TryCalls {
    uint256 public calls;

    function argument(uint256 mode) internal returns (uint256) {
        calls += 1;
        if (mode == 9) {
            uint256 zero = 0;
            return 1 / zero;
        }
        return mode;
    }

    function attempt(address target, uint256 mode) public returns (bytes4, uint256, bytes memory) {
        calls += 1;
        try IReceiver(target).receiveToken(argument(mode)) returns (bytes4 result) {
            require(result == bytes4(0x150b7a02), "wrong receiver");
            bytes memory empty = hex"";
            return (result, IReceiver(target).count(), empty);
        } catch (bytes memory reason) {
            bytes4 zero = bytes4(0);
            return (zero, IReceiver(target).count(), reason);
        }
    }

    function noReturns(address target) public returns (uint256) {
        try IReceiver(target).ping() {
            return 1;
        } catch (bytes memory reason) {
            return 2 + reason.length;
        }
    }
}
