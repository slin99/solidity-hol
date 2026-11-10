// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IAsmPeer {
    function transfer(address to, uint256 amount) external returns (bool);
    function silent(uint256 amount) external;
    function data(uint256 n) external pure returns (uint256, uint256, uint256);
    function read() external view returns (uint256);
}

// Inline assembly that calls out: call and staticcall with gas(), return data
// read back with returndatasize and returndatacopy, and OpenZeppelin v5.1.0's
// SafeERC20 _callOptionalReturn and _callOptionalReturnBool.
contract AssemblyCalls {
    error SafeERC20FailedOperation(address token);

    uint256 public seen;

    function rawCall(address target, uint256 amount)
        external returns (bool ok, uint256 size, uint256 peerTotal)
    {
        bytes memory data = abi.encodeCall(IAsmPeer.transfer, (address(this), amount));
        assembly {
            ok := call(gas(), target, 0, add(data, 0x20), mload(data), 0, 0)
            size := returndatasize()
        }
        peerTotal = IAsmPeer(target).read();
    }

    function bubble(address target, uint256 amount) external {
        bytes memory data = abi.encodeCall(IAsmPeer.transfer, (address(this), amount));
        assembly {
            if iszero(call(gas(), target, 0, add(data, 0x20), mload(data), 0, 0)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0, returndatasize())
                revert(ptr, returndatasize())
            }
        }
        seen += 1;
    }

    function staticRead(address target) external view returns (uint256 v) {
        bytes memory data = abi.encodeCall(IAsmPeer.read, ());
        assembly {
            let ok := staticcall(gas(), target, add(data, 0x20), mload(data), 0, 0x20)
            if iszero(ok) { revert(0, 0) }
            v := mload(0)
        }
    }

    function copyBack(address target, uint256 n) external view returns (uint256 a, uint256 b, uint256 size) {
        bytes memory data = abi.encodeCall(IAsmPeer.data, (n));
        bytes memory out = new bytes(64);
        assembly {
            let ok := staticcall(gas(), target, add(data, 0x20), mload(data), 0, 0)
            size := returndatasize()
            returndatacopy(add(out, 0x20), 0x20, 0x40)
        }
        assembly {
            a := mload(add(out, 0x20))
            b := mload(add(out, 0x40))
        }
    }

    function limitedGas(address target, uint256 amount) external returns (bool ok) {
        bytes memory data = abi.encodeCall(IAsmPeer.silent, (amount));
        assembly {
            ok := call(50000, target, 0, add(data, 0x20), mload(data), 0, 0)
        }
    }

    function safeTransfer(address token, uint256 amount) external {
        _callOptionalReturn(token, abi.encodeCall(IAsmPeer.transfer, (address(this), amount)));
        seen += amount;
    }

    function trySafeTransfer(address token, uint256 amount) external returns (bool) {
        return _callOptionalReturnBool(token, abi.encodeCall(IAsmPeer.transfer, (address(this), amount)));
    }

    function _callOptionalReturn(address token, bytes memory data) private {
        uint256 returnSize;
        uint256 returnValue;
        assembly ("memory-safe") {
            let success := call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0x20)
            // bubble errors
            if iszero(success) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0, returndatasize())
                revert(ptr, returndatasize())
            }
            returnSize := returndatasize()
            returnValue := mload(0)
        }

        if (returnSize == 0 ? address(token).code.length == 0 : returnValue != 1) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    function _callOptionalReturnBool(address token, bytes memory data) private returns (bool) {
        bool success;
        uint256 returnSize;
        uint256 returnValue;
        assembly ("memory-safe") {
            success := call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0x20)
            returnSize := returndatasize()
            returnValue := mload(0)
        }
        return success && (returnSize == 0 ? address(token).code.length > 0 : returnValue == 1);
    }
}
