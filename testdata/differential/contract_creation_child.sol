// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

struct CreationParams {
    uint256 number;
    bytes data;
}

contract CreatedChild {
    uint256 private immutable number;

    constructor(uint256 n) payable {
        require(n != 13, "constructor rejected");
        number = n;
    }

    function read() external view returns (uint256) {
        return number;
    }
}

contract CreatedStructChild {
    uint256 private immutable number;

    constructor(CreationParams memory p) {
        number = p.number + p.data.length;
    }

    function read() external view returns (uint256) {
        return number;
    }
}

contract CreatedImplicitChild {
    function read() external pure returns (uint256) {
        return 42;
    }
}
