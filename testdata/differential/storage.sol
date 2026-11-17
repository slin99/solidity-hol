// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Value-type state variables: packed slots, signed and fixed-bytes values,
// writes seen across internal calls, and reverts discarding writes; writes
// under an if, and storage-free loops (one with a require in its body) in
// functions that read or write state. Reverts are panics or a bare require,
// and there are no negative literals.
contract Storage {
    uint256 total;
    uint8 small;
    int16 signedValue;
    bool flag;
    address owner;
    bytes4 tag;
    uint128 low;
    uint128 high;
    int256 wide;

    function setTotal(uint256 x) public {
        total = x;
    }

    function getTotal() public view returns (uint256) {
        return total;
    }

    function getFlag() public view returns (bool) {
        return flag;
    }

    function packed(uint8 a, int16 b, bool c, address d) public returns (uint8, int16, bool, address) {
        small = a;
        signedValue = b;
        flag = c;
        owner = d;
        return (small, signedValue, flag, owner);
    }

    function setTag(bytes4 t) public returns (bytes4) {
        tag = t;
        return tag;
    }

    function halves(uint128 a, uint128 b) public returns (uint256) {
        low = a;
        high = b;
        return uint256(high) + uint256(low);
    }

    function bump() internal returns (uint256) {
        total += 1;
        return total;
    }

    function acrossCalls() public returns (uint256, uint256) {
        total = 10;
        uint256 seen = bump();
        total *= 2;
        return (seen, total);
    }

    function increments() public returns (uint8, uint8, int16) {
        small = 253;
        uint8 before = small++;
        ++small;
        signedValue--;
        return (before, small, signedValue);
    }

    function overflow() public {
        small = 255;
        small++;
    }

    function writeThenRevert(uint256 x) public returns (uint256) {
        total = x;
        wide = int256(x) - 6;
        return 10 / x;
    }

    function swap() public returns (uint128, uint128) {
        (low, high) = (high, low);
        return (low, high);
    }

    function readOrder() public returns (uint256) {
        total = 1;
        return total + bump();
    }

    function compound() public returns (int256) {
        wide = int256(uint256(small)) - 5;
        wide -= int256(uint256(small));
        return wide;
    }

    function writeIf(bool c, uint256 x) public returns (uint256) {
        if (c) total = x;
        return total;
    }

    function writeIfElse(bool c, uint256 x) public returns (uint256, int256) {
        if (c) {
            total = x;
        } else {
            wide = int256(x);
        }
        return (total, wide);
    }

    function loopThenWrite(uint256 n) public returns (uint256) {
        uint256 acc;
        for (uint256 i = 0; i < n; i++) {
            acc += i;
        }
        total = acc;
        return total;
    }

    function readLoopWrite(uint256 n) public returns (uint256) {
        uint256 acc = total;
        for (uint256 i = 0; i < n; i++) {
            acc += i;
        }
        low = uint128(acc);
        return uint256(low);
    }

    function requireInLoop(uint256 n, uint256 limit) public returns (uint256) {
        total = 1;
        uint256 acc;
        for (uint256 i = 0; i < n; i++) {
            require(i < limit);
            acc += i;
        }
        total = acc;
        return total;
    }
}
