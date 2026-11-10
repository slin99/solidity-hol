// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IRdPeer {
    function transfer(address to, uint256 amount) external returns (bool);
    function data(uint256 n) external pure returns (uint256, uint256, uint256);
}

// Inline assembly reading the return data the contract's calls left: after a
// high-level, try or low-level call, after an internal call, and in the block
// after one that called, as Uniswap v4's CustomRevert.bubbleUpAndRevertWith
// and GPv2's SafeERC20 read it.
contract AssemblyReturnData {
    function atEntry() external view returns (uint256 size) {
        assembly { size := returndatasize() }
    }

    function afterCall(address target, uint256 n) external view returns (uint256, uint256 size) {
        (uint256 a, , ) = IRdPeer(target).data(n);
        assembly { size := returndatasize() }
        return (a, size);
    }

    function afterLowLevel(address target, uint256 amount) external returns (bool, uint256 size) {
        (bool ok, ) = target.call(abi.encodeCall(IRdPeer.transfer, (address(this), amount)));
        assembly { size := returndatasize() }
        return (ok, size);
    }

    // A caught revert's data is still the return data in the catch clause.
    function bubbleCaught(address target, uint256 amount) external returns (bool) {
        try IRdPeer(target).transfer(address(this), amount) returns (bool ok) {
            return ok;
        } catch (bytes memory) {
            assembly {
                let p := mload(0x40)
                returndatacopy(p, 0, returndatasize())
                revert(p, returndatasize())
            }
        }
    }

    function _data(address target, uint256 n) private view returns (uint256) {
        (uint256 a, , ) = IRdPeer(target).data(n);
        return a;
    }

    function afterInternal(address target, uint256 n) external view returns (uint256 a, uint256 size) {
        a = _data(target, n);
        assembly { size := returndatasize() }
    }

    function acrossBlocks(address target, uint256 n) external view returns (bool ok, uint256 size) {
        bytes4 sel = IRdPeer.data.selector;
        assembly {
            mstore(0, sel)
            mstore(4, n)
            ok := staticcall(gas(), target, 0, 36, 0, 0)
        }
        assembly { size := returndatasize() }
    }
}
