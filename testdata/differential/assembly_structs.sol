// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract AssemblyStructs {
    struct PoolKey {
        address currency0;
        address currency1;
        uint24 fee;
        int24 tickSpacing;
        address hooks;
    }
    struct MarketParams {
        address loanToken;
        address collateralToken;
        address oracle;
        address irm;
        uint256 lltv;
    }
    struct Pair { uint256 a; uint256 b; }
    struct Scalars { uint8 n; bool flag; int24 signed; bytes4 tag; address owner; }
    struct Box { Pair pair; bytes data; uint256[] xs; uint256[2] fixeds; }

    function poolId(address a, address b, uint24 fee, int24 spacing, address hooks)
        public pure returns (bytes32 result)
    {
        PoolKey memory key = PoolKey(a, b, fee, spacing, hooks);
        assembly { result := keccak256(key, 0xa0) }
    }

    function marketId(address a, address b, address oracle, address irm, uint256 lltv)
        public pure returns (bytes32 result)
    {
        MarketParams memory params = MarketParams(a, b, oracle, irm, lltv);
        assembly { result := keccak256(params, 160) }
    }

    function scalarWords() public pure returns (Scalars memory p) {
        p = Scalars(1, false, 2, 0, address(0));
        assembly {
            mstore(p, 255)
            mstore(add(p, 32), true)
            mstore(add(p, 64), not(59))
            mstore(add(p, 96), shl(224, 0xaabbccdd))
            mstore(add(p, 128), 0x1234)
        }
    }

    function nested() public pure returns (uint256, uint256, uint8, uint256, uint256) {
        Box memory box;
        box.data = hex"010203";
        box.xs = new uint256[](2);
        assembly {
            mstore(mload(box), 21)
            mstore(add(mload(box), 32), 22)
            mstore8(add(mload(add(box, 32)), 32), 0xaa)
            mstore(add(mload(add(box, 64)), 32), 31)
            mstore(mload(add(box, 96)), 41)
        }
        return (box.pair.a, box.pair.b, uint8(box.data[0]), box.xs[0], box.fixeds[0]);
    }

    function defaultPointers() public pure returns (uint256 a, uint256 b, uint256 c) {
        Box memory box;
        assembly {
            a := mload(mload(add(box, 32)))
            b := mload(mload(add(box, 64)))
            c := mload(mload(box))
        }
    }

    function structArray() public pure returns (uint256, uint256) {
        Pair[] memory pairs = new Pair[](2);
        Pair memory secondPair = pairs[1];
        assembly {
            let second := mload(add(pairs, 64))
            mstore(second, 51)
            mstore(add(second, 32), 52)
        }
        return (secondPair.a, pairs[1].b);
    }

    function allocatePair(uint256 a, uint256 b) public pure returns (Pair memory p, uint256 c) {
        p = Pair(0, 0);
        assembly {
            p := mload(0x40)
            mstore(p, a)
            mstore(add(p, 32), b)
            mstore(0x40, add(p, 64))
        }
        uint256[] memory later = new uint256[](1);
        later[0] = 99;
        c = later[0];
    }

    function booleans(bool input) public pure returns (bool a, bool b, uint256 n) {
        assembly {
            a := true
            b := false
            switch input
            case true { n := 7 }
            case false { n := 8 }
        }
    }
}
