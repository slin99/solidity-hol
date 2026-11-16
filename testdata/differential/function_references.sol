// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Internal function values whose parameters and returns are storage
// pointers, memory and calldata references; modifiers around functions
// returning static memory arrays and memory structs, running the placeholder
// twice; a hex literal selector; abi.decode of storage bytes.
library Sums {
    function total(uint256[2] storage xs, uint256[] memory ys) internal view returns (uint256 s) {
        for (uint256 i = 0; i < xs.length; i++) s += xs[i];
        for (uint256 i = 0; i < ys.length; i++) s += ys[i];
    }

    function weighted(uint256[2] storage xs, uint256[] memory ys) internal view returns (uint256 s) {
        for (uint256 i = 0; i < xs.length; i++) s += (i + 1) * xs[i];
        for (uint256 i = 0; i < ys.length; i++) s += 10 * ys[i];
    }
}

contract FunctionReferences {
    struct Pair {
        uint256 a;
        uint256 b;
    }

    uint256[2] values;
    Pair stored;
    bytes payload;
    uint256 public runs;

    // a function-pointer local with a storage pointer and a memory
    // parameter, chosen by a conditional, then called
    function pick(bool up, uint256 z) external view returns (uint256) {
        function(uint256[2] storage, uint256[] memory) internal view returns (uint256) f =
            up ? Sums.total : Sums.weighted;
        uint256[] memory ys = new uint256[](2);
        ys[0] = z;
        ys[1] = z + 1;
        return f(values, ys);
    }

    function bump(Pair storage p, uint256 k) internal returns (Pair memory r) {
        p.a += k;
        r = p;
    }

    function scale(Pair storage p, uint256 k) internal returns (Pair memory r) {
        p.b *= k;
        r = p;
    }

    // storage-pointer parameter and memory struct return
    function update(bool add, uint256 k) external returns (uint256, uint256, uint256, uint256) {
        function(Pair storage, uint256) internal returns (Pair memory) g = add ? bump : scale;
        Pair memory r = g(stored, k);
        return (r.a, r.b, stored.a, stored.b);
    }

    function head(uint256[] calldata xs) internal pure returns (uint256) {
        return xs.length == 0 ? 0 : xs[0];
    }

    function last(uint256[] calldata xs) internal pure returns (uint256) {
        return xs.length == 0 ? 0 : xs[xs.length - 1];
    }

    // a calldata parameter
    function ends(bool first, uint256[] calldata xs) external pure returns (uint256) {
        function(uint256[] calldata) internal pure returns (uint256) h = first ? head : last;
        return h(xs);
    }

    modifier twice() {
        _;
        _;
        runs += 1;
    }

    modifier after_(uint256 k) {
        _;
        runs += k;
    }

    // the placeholder runs twice; both runs share the return array the
    // outermost call allocated
    function counts(uint256 k) public twice returns (uint256[3] memory c) {
        c[0] += k;
        c[1] += 1;
        runs += c[0];
    }

    function pairs(uint256 k) public twice after_(2) returns (Pair memory p) {
        p.a += k;
        p.b += p.a;
        runs += p.b;
    }

    function counter() public twice returns (uint256 r) {
        r += 1;
        runs += r;
    }

    // code after the modified call reads the returns
    function readCounts(uint256 k) external returns (uint256, uint256, uint256, uint256) {
        uint256[3] memory c = counts(k);
        Pair memory p = pairs(k);
        return (c[0], c[1], p.a + p.b, counter());
    }

    // a hex literal selector
    function encodeTransfer(address to, uint256 amount) external pure returns (bytes memory) {
        return abi.encodeWithSelector(0xa9059cbb, to, amount);
    }

    // abi.decode of storage bytes
    function decodeStored(uint256 x, address y) external returns (uint256, address) {
        payload = abi.encode(x, y);
        return abi.decode(payload, (uint256, address));
    }
}
