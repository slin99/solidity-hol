// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Storage-pointer locals declared without a value and assigned before each
// read: a struct pointer from a mapping inside a loop, and a dynamic array
// pointer on both arms of a branch. (solc rejects a mapping pointer declared
// without a value.)
contract UninitializedStoragePointers {
    struct Set {
        address[] values;
        mapping(address => uint256) indexes;
    }

    mapping(uint256 => Set) sets;
    uint256[] evens;
    uint256[] odds;

    function add(Set storage s, address a) internal {
        s.values.push(a);
        s.indexes[a] = s.values.length;
    }

    function addToEach(uint256 n, address a) public returns (uint256 total, uint256 length) {
        add(sets[1], address(0x11));
        Set storage s;
        for (uint256 i = 0; i < n; ++i) {
            s = sets[i];
            for (uint256 j = 0; j < s.values.length; ++j) {
                total += s.indexes[s.values[j]];
            }
            add(s, a);
        }
        length = sets[1].values.length;
    }

    function sort(uint256 v) public returns (uint256, uint256) {
        uint256[] storage xs;
        if (v % 2 == 0) {
            xs = evens;
        } else {
            xs = odds;
        }
        xs.push(v);
        xs[0] += 1;
        return (xs.length, xs[0]);
    }
}
