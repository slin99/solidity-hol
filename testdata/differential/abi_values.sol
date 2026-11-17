// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Structs and arrays of them across every ABI boundary: calldata parameters
// and their fields, memory and storage values, returns, external calls (caught
// or not), abi.encode/abi.decode, events, custom errors and constructor
// parameters.

enum Kind { Low, Mid, High }

struct Inner {
    uint8 x;
    bytes b;
}

struct Outer {
    uint64 a;
    Inner[] items;
    string name;
    Kind k;
}

struct Pair {
    uint128 left;
    bool flag;
}

struct Kinds {
    Kind[] values;
}

interface IAbiPeer {
    function combined(Outer calldata o, Inner[] calldata xs) external;
    function echo(Outer calldata o) external pure returns (Outer memory);
    function make(uint64 a, string calldata name) external pure returns (Outer memory, Pair memory);
    function fail(Inner calldata i) external pure returns (Outer memory);
}

contract AbiValues {
    struct Stored {
        uint128 a;
        bool b;
        string s;
    }

    Pair public pair;
    Stored stored;

    event Logged(Inner indexed i, Outer o, Pair p);
    event LoggedStored(Stored indexed key, Stored value);
    error Bad(Inner i, Kind k);
    error BadStored(Stored value);

    constructor(Pair memory p, Inner[] memory items) {
        pair = p;
        pair.left += uint128(items.length);
    }

    function echo(Outer calldata o) external pure returns (Outer memory) {
        return o;
    }

    function echoMemory(Outer memory o) external pure returns (Outer memory) {
        return o;
    }

    function fieldBytes(Outer calldata o, uint256 i) external pure returns (bytes memory, uint8, Kind) {
        return (o.items[i].b, o.items[i].x, o.k);
    }

    function nameOf(Outer calldata o) external pure returns (string memory) {
        return o.name;
    }

    function firstOfFixed(Inner[2] calldata xs) external pure returns (bytes memory, uint8) {
        return (xs[1].b, xs[0].x);
    }

    function pairs(Pair[] calldata ps) external pure returns (uint256 total, Pair memory last) {
        for (uint256 i = 0; i < ps.length; i++) {
            total += ps[i].left;
        }
        last = ps[ps.length - 1];
    }

    function setStored(Stored calldata s) external {
        stored = s;
    }

    function getStored() external view returns (Stored memory) {
        return stored;
    }

    function encodeStored() external view returns (bytes memory) {
        return abi.encode(stored, pair);
    }

    function encodeCallStored() external view returns (bytes memory) {
        return abi.encodeCall(this.setStored, (stored));
    }

    function encodeCallValues(Outer calldata o, Inner[] memory xs) external pure returns (bytes memory) {
        return abi.encodeCall(IAbiPeer.combined, (o, xs));
    }

    function encodeValues(Outer calldata o, Pair memory p) external pure returns (bytes memory) {
        Inner memory i = Inner(7, hex"beef");
        return abi.encode(o, p, i, o.items);
    }

    function decodeOuter(bytes memory data) external pure returns (Outer memory, Pair memory) {
        (Outer memory o, Pair memory p) = abi.decode(data, (Outer, Pair));
        return (o, p);
    }

    function decodeItems(bytes calldata data) external pure returns (uint256, bytes memory) {
        Inner[] memory items = abi.decode(data, (Inner[]));
        return (items.length, items[items.length - 1].b);
    }

    function viaPeer(address peer, Outer memory o) external pure returns (Outer memory) {
        return IAbiPeer(peer).echo(o);
    }

    function makeViaPeer(address peer, uint64 a, string memory name) external pure returns (uint256, string memory, bool) {
        (Outer memory o, Pair memory p) = IAbiPeer(peer).make(a, name);
        return (o.items.length + o.a, o.name, p.flag);
    }

    function tryPeer(address peer, Inner memory i, bool failing) external pure returns (bool, uint256) {
        if (failing) {
            try IAbiPeer(peer).fail(i) returns (Outer memory o) {
                return (true, o.a);
            } catch {
                return (false, 0);
            }
        }
        Outer memory arg = Outer(3, new Inner[](1), "x", Kind.High);
        arg.items[0] = i;
        try IAbiPeer(peer).echo(arg) returns (Outer memory o) {
            return (true, o.items[0].x);
        } catch {
            return (false, 1);
        }
    }

    function emitLogged(Outer calldata o, Pair calldata p) external {
        emit Logged(o.items[0], o, p);
    }

    function emitStored() external {
        emit LoggedStored(stored, stored);
    }

    function emitMemory(Stored memory value) external {
        emit LoggedStored(value, value);
    }

    function revertStored() external view {
        revert BadStored(stored);
    }

    function revertMemory(Stored memory value) external pure {
        revert BadStored(value);
    }

    function kinds(Kind[] memory ks) external pure returns (Kind[] memory, uint256) {
        return (ks, ks.length);
    }

    function calldataKinds(Kind[] calldata ks) external pure returns (Kind[] memory) {
        return ks;
    }

    function structKinds(Kinds calldata ks) external pure returns (uint256, Kind, Kind[] memory) {
        return (ks.values.length, ks.values[1], ks.values);
    }

    function slicePairs(Pair[] calldata ps) external pure returns (Pair[] memory) {
        return ps[1:];
    }

    function revertBad(Inner calldata i) external pure {
        revert Bad(i, Kind.Mid);
    }
}
