// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

interface IArrayPeer {
    function rev(uint256[] calldata a) external pure returns (uint256[] memory);
    function count(uint256[][] calldata a) external pure returns (uint256);
    function firstWord(bytes[] calldata a) external pure returns (uint256);
}

contract StorageArrayValues {
    uint256[] dyn;
    uint8[] small;
    uint16[] wider;
    uint8[3] fixedSmall;
    uint256[][] nested;
    uint256[2][] pairs;
    bytes[] blobs;
    string[] names;
    bytes8[] shortTags;
    bytes10[] longTags;
    uint256 sentinel;

    function fill(uint256 n) internal {
        for (uint256 i = 0; i < n; i++) {
            dyn.push(i + 10);
        }
    }

    function toMemory(uint256 n) public returns (uint256, uint256, uint256) {
        fill(n);
        uint256[] memory m = dyn;
        m[0] = 99;
        return (m.length, m[n - 1], dyn[0]);
    }

    function fromMemory(uint256 n, uint256 grown) public returns (uint256, uint256, uint256) {
        fill(grown);
        uint256[] memory m = new uint256[](n);
        for (uint256 i = 0; i < n; i++) {
            m[i] = i * 3 + 1;
        }
        dyn = m;
        m[0] = 77;
        uint256 first = dyn[0];
        uint256 stale;
        assembly {
            mstore(0, dyn.slot)
            stale := sload(add(keccak256(0, 0x20), n))
        }
        return (dyn.length, first, stale);
    }

    function fromCalldata(uint256[] calldata a) external returns (uint256, uint256) {
        dyn = a;
        return (dyn.length, dyn[dyn.length - 1]);
    }

    function smallFromCalldata(uint8[] calldata a) external returns (uint256, uint8) {
        small = a;
        return (small.length, small[small.length - 1]);
    }

    function packedShrink(uint256 n, uint256 keep) public returns (uint256, uint256, uint256) {
        for (uint256 i = 0; i < n; i++) {
            small.push(uint8(i + 1));
        }
        uint8[] memory m = new uint8[](keep);
        for (uint256 i = 0; i < keep; i++) {
            m[i] = uint8(200 + i);
        }
        small = m;
        uint256 first;
        uint256 second;
        assembly {
            mstore(0, small.slot)
            first := sload(keccak256(0, 0x20))
            second := sload(add(keccak256(0, 0x20), 1))
        }
        return (small.length, first, second);
    }

    function widen(uint256 n) public returns (uint256, uint16, uint16) {
        for (uint256 i = 0; i < n; i++) {
            small.push(uint8(250 + i));
        }
        wider.push(1);
        wider.push(2);
        wider.push(3);
        wider.push(4);
        wider = small;
        return (wider.length, wider[0], wider[wider.length - 1]);
    }

    function staticToDynamic(uint8 x) public returns (uint256, uint8, uint256) {
        uint8[3] memory m;
        m[0] = x;
        m[2] = x + 1;
        fixedSmall = m;
        small = fixedSmall;
        dyn = fixedSmall;
        return (small.length, small[2], dyn[0] + dyn[1] + dyn[2]);
    }

    function staticToMemory(uint8 x) public returns (uint8, uint8) {
        fixedSmall[1] = x;
        uint8[3] memory m = fixedSmall;
        m[1] = 0;
        return (m[1], fixedSmall[1]);
    }

    function selfAssign(uint256 n) public returns (uint256, uint256) {
        fill(n);
        dyn = dyn;
        return (dyn.length, dyn[n - 1]);
    }

    function nestedRoundTrip(uint256 rows) public returns (uint256, uint256, uint256) {
        uint256[][] memory m = new uint256[][](rows);
        for (uint256 i = 0; i < rows; i++) {
            m[i] = new uint256[](i + 1);
            m[i][i] = i + 5;
        }
        nested = m;
        uint256[][] memory back = nested;
        back[0][0] = 42;
        uint256[2][] memory p = new uint256[2][](2);
        p[1][1] = 9;
        pairs = p;
        return (back.length, back[rows - 1][rows - 1], nested[0][0] + pairs[1][1]);
    }

    function nestedShrink() public returns (uint256, uint256) {
        uint256[][] memory m = new uint256[][](2);
        m[0] = new uint256[](3);
        m[1] = new uint256[](2);
        m[1][1] = 8;
        nested = m;
        nested = new uint256[][](1);
        uint256 row;
        uint256 cell;
        assembly {
            mstore(0, nested.slot)
            let data := keccak256(0, 0x20)
            row := sload(add(data, 1))
            mstore(0, add(data, 1))
            cell := sload(add(keccak256(0, 0x20), 1))
        }
        return (nested.length, row + cell);
    }

    function blobRoundTrip(uint256 n) public returns (uint256, uint256, bytes1) {
        bytes[] memory m = new bytes[](2);
        m[0] = "short";
        m[1] = new bytes(n);
        bytes1 last;
        if (n > 0) {
            m[1][n - 1] = bytes1(uint8(127));
        }
        blobs = m;
        bytes[] memory back = blobs;
        if (n > 0) {
            last = blobs[1][n - 1];
        }
        return (back.length, back[1].length, last);
    }

    function namesRoundTrip() public returns (string memory, uint256) {
        string[] memory m = new string[](2);
        m[0] = "alpha";
        m[1] = "a string that is longer than thirty-one bytes";
        names = m;
        return (names[1], bytes(names[0]).length);
    }

    function tagsWiden(bytes8 t) public returns (bytes10, uint256) {
        shortTags.push(t);
        shortTags.push(~t);
        longTags = shortTags;
        return (longTags[1], longTags.length);
    }

    function returnsStorage(uint256 n) public returns (uint256[] memory) {
        fill(n);
        return dyn;
    }

    function setNested() internal {
        nested = new uint256[][](2);
        nested[0].push(1);
        nested[1].push(6);
        nested[1].push(7);
    }

    function returnsNested() public returns (uint256[][] memory) {
        setNested();
        return nested;
    }

    function revViaPeer(address peer, uint256 n) public returns (uint256, uint256) {
        fill(n);
        uint256[] memory r = IArrayPeer(peer).rev(dyn);
        return (r.length, r[0]);
    }

    function countViaPeer(address peer) public returns (uint256) {
        setNested();
        return IArrayPeer(peer).count(nested);
    }
    function selfAssignKeepsDirtyTail() public returns (uint256) {
        small.push(1);
        assembly {
            mstore(0, small.slot)
            let data := keccak256(0, 0x20)
            sstore(data, or(sload(data), shl(248, 0xab)))
        }
        small = small;
        uint256 word;
        assembly {
            mstore(0, small.slot)
            word := sload(keccak256(0, 0x20))
        }
        return word;
    }

    function nestedFromCalldata(uint256[][] calldata a) external returns (uint256, uint256) {
        nested = a;
        return (nested.length, nested[0][0]);
    }
    function dirtyBlobViaPeer(address peer) public returns (uint256) {
        blobs = new bytes[](1);
        assembly {
            mstore(0, blobs.slot)
            sstore(keccak256(0, 0x20), or(shl(240, 0x61ff), 2))
        }
        return IArrayPeer(peer).firstWord(blobs);
    }

    function growOverStale(uint256 which) public returns (uint256) {
        uint256 word;
        if (which == 0) {
            assembly {
                mstore(0, small.slot)
                sstore(keccak256(0, 0x20), 0x100)
            }
            small = new uint8[](1);
            assembly {
                mstore(0, small.slot)
                word := sload(keccak256(0, 0x20))
            }
        } else if (which == 1) {
            assembly {
                mstore(0, nested.slot)
                let row := keccak256(0, 0x20)
                sstore(row, 1)
                mstore(0, row)
                sstore(keccak256(0, 0x20), 42)
            }
            nested = new uint256[][](1);
            assembly {
                mstore(0, nested.slot)
                mstore(0, keccak256(0, 0x20))
                word := sload(keccak256(0, 0x20))
            }
        } else {
            assembly {
                mstore(0, blobs.slot)
                sstore(keccak256(0, 0x20), 1)
            }
            blobs = new bytes[](1);
        }
        return word;
    }
}
