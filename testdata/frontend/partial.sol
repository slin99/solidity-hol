// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

// A contract of supported and unsupported functions (sha256 is not
// modelled, nor are halting assembly in a constructor, fixed-byte indexing in a constant,
// or assembly assigning a bytes local): the unsupported ones,
// and those calling them, have no procedure, and calls of them are refused.
contract Base {
    function twice(uint256 x) public pure virtual returns (uint256) {
        return x * 2;
    }
}

contract Mid is Base {
    function twice(uint256 x) public pure virtual override returns (uint256) {
        return uint256(sha256(abi.encodePacked(x)));
    }
}

contract Partial is Mid {
    uint256 public total;

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
        return sha256(b);
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

    // imports, but assembly may not assign a memory reference
    function pointer(bytes memory b) public pure returns (uint256 p) {
        assembly { b := p }
    }

    fallback() external {
        total = uint256(sha256(msg.data));
    }
}
