// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

uint256 constant CACHE_LENGTH = 2;
uint256 constant FLAT_LENGTH = CACHE_LENGTH * 3;

struct Cached {
    uint104 value;
    uint48 stamp;
}

struct CachedRecord {
    Cached[CACHE_LENGTH] cache;
    uint256 total;
}

contract ConstantArrayLengths {
    uint256 constant LOCAL_LENGTH = 3;

    CachedRecord internal record;
    uint256[FLAT_LENGTH] internal flat;
    uint8[LOCAL_LENGTH] internal small;

    function store(uint104 a, uint104 b) external {
        record.cache[0] = Cached(a, 1);
        record.cache[1] = Cached(b, 2);
        record.total = uint256(a) + b;
        flat[FLAT_LENGTH - 1] = record.total;
        small[2] = 7;
    }

    function readStorage() external view returns (uint104, uint48, uint104, uint256, uint256) {
        return (record.cache[0].value, record.cache[1].stamp, record.cache[1].value,
                record.total, flat[5]);
    }

    function lengths() external view returns (uint256, uint256, uint256) {
        return (record.cache.length, flat.length, small.length);
    }

    function inMemory(uint104 a) external pure returns (uint256, uint104) {
        CachedRecord memory r;
        r.cache[1].value = a;
        return (r.cache.length, r.cache[1].value);
    }

    function copied() external view returns (uint104, uint256) {
        CachedRecord memory r = record;
        return (r.cache[1].value, r.total);
    }
}
