// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

// A contract of supported and unsupported functions (ripemd160 is not
// modelled, nor are halting assembly in a constructor or fixed-byte indexing
// in a constant): the unsupported ones, and those calling them, have no
// procedure, and calls of them are refused.
contract Base {
    function twice(uint256 x) public pure virtual returns (uint256) {
        return x * 2;
    }
}

contract Mid is Base {
    function twice(uint256 x) public pure virtual override returns (uint256) {
        return uint256(uint160(ripemd160(abi.encodePacked(x))));
    }
}

// A member type the importer cannot represent: the structs are left out,
// so only the functions using them are unsupported.
library Hooks {
    struct Hook {
        function () internal pure returns (uint256) f;
        uint8 n;
    }

    struct Box {
        Hook hook;
    }
}

// A recursive struct: the core holds no recursive struct in memory, so the
// functions with one in memory, or that copy one in storage, are
// unsupported.
struct Node {
    uint8 v;
    Node[] kids;
}

// The ABI forms of structs: the functions that encode or emit a memory
// struct, or pass one to an external call, elaborate.
struct Pair {
    uint8 a;
    uint8 b;
}

interface IPair {
    function put(Pair memory p) external;
}

// A struct holding an enum-keyed mapping.
library Roles {
    enum Role { A, B }

    struct Grant {
        mapping(Role => bool) granted;
        uint8 n;
    }
}

contract Partial is Mid {
    uint256 public total;
    Node tree;
    Node otherTree;

    event Paired(Pair p);

    // Fixed-byte indexing does not elaborate, so the constant has no procedure:
    // its getter and the functions reading it are unsupported
    bytes16 public constant DIGITS = bytes16(bytes32("0123456789abcdef")[0]);

    // imports and passes the source check, but does not elaborate
    constructor() {
        assembly { stop() }
    }

    function add(uint256 x) public returns (uint256) {
        total += x;
        return total;
    }

    function digest(bytes memory b) public pure returns (bytes32) {
        return ripemd160(b);
    }

    function digestTwice(bytes memory b) public pure returns (bytes32) {
        return digest(abi.encodePacked(digest(b)));
    }

    // super reaches Mid.twice, which is unsupported, not Base.twice
    function twice(uint256 x) public pure override returns (uint256) {
        return super.twice(x) + 1;
    }

    function callsTwice(uint256 x) public pure returns (uint256) {
        return twice(x);
    }

    function digits() public pure returns (bytes16) {
        return DIGITS;
    }

    // admitted, but leaves b below the free memory pointer: fails at run time
    function pointer(bytes memory b) public pure returns (uint256 p) {
        assembly { b := p }
    }

    function hookCount() public pure returns (uint8) {
        Hooks.Box memory b;
        return b.hook.n;
    }

    function nodeValue() public pure returns (uint8) {
        Node memory n;
        return n.v;
    }

    function nodeCount() public pure returns (uint256) {
        return new Node[](2).length;
    }

    function copyTree() public {
        tree = otherTree;
    }

    function encodePair() public pure returns (bytes memory) {
        return abi.encode(Pair(1, 2));
    }

    function emitPair() public {
        emit Paired(Pair(1, 2));
    }

    function putPair(IPair t) public {
        t.put(Pair(1, 2));
    }

    function grantCount() internal view returns (uint8) {
        Roles.Grant storage g;
        assembly { g.slot := 0 }
        return g.n;
    }

    // a modifier parameter holding a recursive struct in memory
    modifier withNode(Node memory n) {
        _;
    }

    function nodeModified() public withNode(tree) {}

    // a storage parameter of a struct holding an enum-keyed mapping
    function grantParam(Roles.Grant storage) internal pure {}

    // a tuple holding a storage struct, as a reference
    function treeTuple() public view {
        (tree, 1);
    }

    fallback() external {
        total = uint256(uint160(ripemd160(msg.data)));
    }
}
