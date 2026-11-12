// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface ICatchPeer {
    function run(bytes memory data, uint256 mode) external returns (uint256);
}

contract TypedCatches {
    function classify(address target, bytes memory data, uint256 mode)
        public returns (uint256, uint256, bytes memory)
    {
        try ICatchPeer(target).run(data, mode) returns (uint256 value) {
            return (0, value, hex"");
        } catch Error(string memory reason) {
            return (1, bytes(reason).length, bytes(reason));
        } catch Panic(uint256 code) {
            return (2, code, hex"");
        } catch (bytes memory raw) {
            return (3, raw.length, raw);
        }
    }

    function bare(address target, bytes memory data) public returns (uint256) {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch Error(string memory) {
            return 1;
        } catch Panic(uint256 code) {
            return code;
        } catch {
            return 3;
        }
    }

    function reversed(address target, bytes memory data) public returns (uint256) {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch {
            return 3;
        } catch Panic(uint256 code) {
            return code;
        } catch Error(string memory reason) {
            return 100 + bytes(reason).length;
        }
    }

    function onlyError(address target, bytes memory data) public returns (uint256) {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch Error(string memory reason) {
            return bytes(reason).length;
        }
    }

    function onlyPanic(address target, bytes memory data) public returns (uint256) {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch Panic(uint256 code) {
            return code;
        }
    }

    function bareOnly(address target, bytes memory data) public returns (uint256) {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch {
            return 4;
        }
    }

    function handlerFailure(address target, bytes memory data) public returns (uint256) {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch Error(string memory) {
            revert("handler");
        } catch {
            return 3;
        }
    }

    function nested(address target, bytes memory data) public returns (uint256) {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch Error(string memory reason) {
            try ICatchPeer(target).run(hex"", 1) returns (uint256 value) {
                return value;
            } catch {
                return bytes(reason).length;
            }
        }
    }

    function overlap(address target, bytes memory data) public returns (uint256) {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch Error(string memory) {
            bytes memory later = new bytes(256);
            uint256 length;
            assembly { length := mload(later) }
            return length;
        }
    }

    function bareMemory(address target, bytes memory data) public returns (uint256) {
        uint256 beforePtr;
        assembly { beforePtr := mload(0x40) }
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch {
            uint256 afterPtr;
            assembly { afterPtr := mload(0x40) }
            return afterPtr - beforePtr;
        }
    }

    function memoryLayout(address target, bytes memory data) public returns (uint256, uint256) {
        uint256 beforePtr;
        assembly { beforePtr := mload(0x40) }
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return (value, 0);
        } catch Error(string memory reason) {
            uint256 ptr;
            uint256 afterPtr;
            assembly { ptr := reason afterPtr := mload(0x40) }
            return (ptr - beforePtr, afterPtr - beforePtr);
        } catch Panic(uint256) {
            uint256 afterPtr;
            assembly { afterPtr := mload(0x40) }
            return (0, afterPtr - beforePtr);
        } catch (bytes memory raw) {
            uint256 ptr;
            uint256 afterPtr;
            assembly { ptr := raw afterPtr := mload(0x40) }
            return (ptr - beforePtr, afterPtr - beforePtr);
        }
    }

    function writeOverlap(address target, bytes memory data, uint256 offset)
        public returns (uint256)
    {
        try ICatchPeer(target).run(data, 1) returns (uint256 value) {
            return value;
        } catch Error(string memory reason) {
            bytes memory later = new bytes(256);
            assembly { mstore8(add(reason, offset), 1) }
            return later.length;
        }
    }
}
