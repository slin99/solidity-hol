// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IFormsPeer {
    function data(uint256 n) external pure returns (uint256, uint256, uint256);
}

type Price is uint128;

// Inline assembly as Solady and solmate write it: hashing in the memory
// below 0x80, with the free memory pointer and the zero slot restored before
// the block ends; return data copied by a Yul function of the block; and
// enum and user-defined value type locals.
contract AssemblyLibraryForms {
    enum State { Unset, Waiting, Ready }

    // Two words in the scratch space.
    function hashPair(uint256 a, uint256 b) external pure returns (bytes32 h) {
        assembly {
            mstore(0x00, a)
            mstore(0x20, b)
            h := keccak256(0x00, 0x40)
        }
    }

    // Four words over the scratch space, the free memory pointer and the
    // zero slot, both restored, as Solady's EIP712 hashes do.
    function hashFour(uint256 a, uint256 b, uint256 c, uint256 d)
        external pure returns (bytes32 h, uint256 after_)
    {
        assembly {
            let m := mload(0x40)
            mstore(0x00, a)
            mstore(0x20, b)
            mstore(0x40, c)
            mstore(0x60, d)
            h := keccak256(0x00, 0x80)
            mstore(0x40, m)
            mstore(0x60, 0)
        }
        bytes memory fresh = new bytes(1);
        after_ = fresh.length;
    }

    // Byte writes and a copy feeding later reads, inside a loop and a
    // branch.
    function packed(uint256 n, bool twice) external pure returns (bytes32 h) {
        assembly {
            mstore(0x00, 0)
            mstore(0x20, 0)
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                mstore8(i, add(i, 0x41))
            }
            if twice { mcopy(0x20, 0x00, 0x20) }
            h := keccak256(0x00, 0x40)
        }
    }

    // Each read below covers memory written only inside the loop, branch or
    // switch before it.
    function loopByte(uint256 n) external pure returns (bytes32 h) {
        assembly {
            for { let i := 0 } lt(i, add(n, 1)) { i := add(i, 1) } {
                mstore8(0x00, add(i, 0x41))
            }
            h := keccak256(0x00, 0x01)
        }
    }

    function branchCopy(bool b, uint256) external pure returns (bytes32 h) {
        assembly {
            // The second argument, copied from calldata.
            if b { calldatacopy(0x00, 0x24, 0x20) }
            h := keccak256(0x00, 0x20)
        }
    }

    function switchCopy(uint256 k, uint256 v) external pure returns (bytes32 h) {
        assembly {
            switch k
            case 0 {
                mstore(0x20, v)
                mcopy(0x00, 0x20, 0x20)
            }
            default {
                mstore(0x20, k)
                mcopy(0x00, 0x20, 0x20)
            }
            h := keccak256(0x00, 0x40)
        }
    }

    // The zero slot as scratch; v left there must be zero at the end.
    function zeroSlot(uint256 v) external pure returns (uint256 r) {
        assembly {
            mstore(0x60, v)
            r := add(mload(0x60), 1)
        }
    }

    // Return data copied by a Yul function, as JSONParserLib's helpers do.
    function lastWord(address peer, uint256 n) external view returns (uint256 size, uint256 w) {
        bytes4 sel = IFormsPeer.data.selector;
        assembly {
            function firstReturned() -> r {
                if iszero(lt(returndatasize(), 0x20)) {
                    returndatacopy(0x00, 0x00, 0x20)
                    r := mload(0x00)
                }
            }
            mstore(0x00, sel)
            mstore(0x04, n)
            if iszero(staticcall(gas(), peer, 0x00, 0x24, 0x00, 0x00)) { revert(0, 0) }
            size := returndatasize()
            w := firstReturned()
        }
    }

    // An enum local computed in assembly, as Solady's Timelock.operationState
    // does; a word past the last member has no source value.
    function nextState(State s) external pure returns (State r) {
        assembly {
            r := add(s, 1)
        }
    }

    // A user-defined value type local, kept as its underlying uint128.
    function doubled(Price p) external pure returns (Price q) {
        assembly {
            q := mul(p, 2)
        }
    }
}
