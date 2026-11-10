// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IAsmPeer {
    function transfer(address to, uint256 amount) external returns (bool);
}

// Inline assembly using memory as token-transfer helpers do: a call encoded
// at the free memory pointer without moving it, a call's output and return
// data read in the same expression (arguments run right to left), return data
// copied into the scratch space, if and switch bodies that halt, and
// allocations made after a block left bytes above the free memory pointer.
contract AssemblyScratch {
    error TransferFailed(address token);

    uint256 public seen;

    // The shape of solmate's and Uniswap v4's transfer helpers: the call's
    // 32-byte output and return data size are read left of the call, and the
    // encoding is cleared afterwards.
    function packedResult(address token, uint256 amount) external returns (bool success) {
        bytes4 selector = IAsmPeer.transfer.selector;
        assembly {
            let p := mload(0x40)
            mstore(p, selector)
            mstore(add(p, 4), and(token, 0xffffffffffffffffffffffffffffffffffffffff))
            mstore(add(p, 36), amount)
            success := and(
                or(and(eq(mload(0), 1), gt(returndatasize(), 31)), iszero(returndatasize())),
                call(gas(), token, 0, p, 68, 0, 32)
            )
            mstore(p, 0)
            mstore(add(p, 0x20), 0)
            mstore(add(p, 0x40), 0)
        }
        seen += 1;
    }

    // The shape of GPv2's transfer result check: return data copied into
    // the scratch space, then read.
    function lastResult(address token, uint256 amount) external returns (bool success) {
        bytes4 selector = IAsmPeer.transfer.selector;
        assembly {
            let p := mload(0x40)
            mstore(p, selector)
            mstore(add(p, 4), and(token, 0xffffffffffffffffffffffffffffffffffffffff))
            mstore(add(p, 36), amount)
            let ok := call(gas(), token, 0, p, 68, 0, 0)
            switch returndatasize()
            case 0 { success := ok }
            case 32 {
                returndatacopy(0, 0, returndatasize())
                success := and(ok, iszero(iszero(mload(0))))
            }
            default { revert(0, 0) }
        }
    }

    // A halting branch that bubbles the callee's revert data from the
    // scratch space.
    function bubbleScratch(address token, uint256 amount) external {
        bytes memory data = abi.encodeCall(IAsmPeer.transfer, (address(this), amount));
        assembly {
            if iszero(call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0)) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
        }
        seen += amount;
    }

    // A halting branch that writes a custom error above the scratch space.
    function customError(address token, uint256 amount) external {
        bytes memory data = abi.encodeCall(IAsmPeer.transfer, (address(this), amount));
        bytes4 selector = TransferFailed.selector;
        assembly {
            if iszero(call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0)) {
                mstore(0x80, selector)
                mstore(0x84, and(token, 0xffffffffffffffffffffffffffffffffffffffff))
                revert(0x80, 0x24)
            }
        }
        seen += amount;
    }

    // A block that ends in a switch halting in every branch, as a proxy's
    // forwarding does.
    function forward(address token, uint256 amount) external returns (bool) {
        bytes memory data = abi.encodeCall(IAsmPeer.transfer, (address(this), amount));
        assembly {
            let ok := call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0)
            returndatacopy(0, 0, returndatasize())
            switch ok
            case 0 { revert(0, returndatasize()) }
            default { return(0, returndatasize()) }
        }
    }

    // Allocations after a block filled memory above the free memory pointer:
    // each one's padding still reads as zeros.
    function dirtyThenAllocate(uint8 v) external pure returns (uint256 a, uint256 b, uint256 c) {
        assembly {
            let p := mload(0x40)
            for { let i := 0 } lt(i, 0x200) { i := add(i, 0x20) } {
                mstore(add(p, i), not(0))
            }
        }
        bytes memory x = new bytes(5);
        bytes memory y = "abc";
        bytes memory z = abi.encodePacked(v);
        assembly {
            a := mload(add(x, 0x20))
            b := mload(add(y, 0x20))
            c := mload(add(z, 0x20))
        }
    }
}
