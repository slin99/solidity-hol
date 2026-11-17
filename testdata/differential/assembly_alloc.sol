// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Inline assembly that allocates memory objects from the free memory pointer
// and leaves memory locals at them: OpenZeppelin's _asSingletonArrays, Uniswap
// v4's callHook copying return data into new bytes, a static array, bytes
// whose padding the block leaves dirty, two locals sharing one array, and core
// allocations after a block's.
contract AssemblyAlloc {
    function _asSingletonArrays(uint256 element1, uint256 element2)
        private
        pure
        returns (uint256[] memory array1, uint256[] memory array2)
    {
        assembly ("memory-safe") {
            array1 := mload(0x40)
            mstore(array1, 1)
            mstore(add(array1, 0x20), element1)
            array2 := add(array1, 0x40)
            mstore(array2, 1)
            mstore(add(array2, 0x20), element2)
            mstore(0x40, add(array2, 0x40))
        }
    }

    function singletons(uint256 a, uint256 b) public pure returns (uint256[] memory, uint256[] memory) {
        return _asSingletonArrays(a, b);
    }

    function thenNew(uint256 a) public pure returns (uint256[] memory x, uint256[] memory y) {
        (x, ) = _asSingletonArrays(a, a + 1);
        y = new uint256[](2);
        y[0] = 5;
        x[0] = 6;
    }

    function callHook(address target, bytes memory data) internal returns (bytes memory result) {
        bool success;
        assembly ("memory-safe") {
            success := call(gas(), target, 0, add(data, 0x20), mload(data), 0, 0)
        }
        require(success);
        assembly ("memory-safe") {
            result := mload(0x40)
            mstore(0x40, add(result, and(add(returndatasize(), 0x3f), not(0x1f))))
            mstore(result, returndatasize())
            returndatacopy(add(result, 0x20), 0, returndatasize())
        }
    }

    function raw(uint256 n) external pure {
        assembly {
            mstore(0, 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20)
            mstore(0x20, 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40)
            return(0, n)
        }
    }

    function hook(uint256 n) public returns (bytes memory r, uint256 len) {
        r = callHook(address(this), abi.encodeCall(this.raw, (n)));
        len = r.length;
    }

    function pair(uint256 a, uint256 b) public pure returns (uint256[2] memory s) {
        assembly {
            s := mload(0x40)
            mstore(s, a)
            mstore(add(s, 0x20), b)
            mstore(0x40, add(s, 0x40))
        }
    }

    function word(bytes32 w, uint256 n) public pure returns (bytes memory r, bytes32 h) {
        require(n <= 32);
        assembly {
            r := mload(0x40)
            mstore(r, n)
            mstore(add(r, 0x20), w)
            mstore(0x40, add(r, 0x40))
        }
        h = keccak256(r);
    }

    function shared(uint256 a) public pure returns (uint256[] memory x, uint256[] memory y) {
        assembly {
            x := mload(0x40)
            mstore(x, 1)
            mstore(add(x, 0x20), a)
            y := x
            mstore(0x40, add(x, 0x40))
        }
        y[0] = a + 1;
    }
}
