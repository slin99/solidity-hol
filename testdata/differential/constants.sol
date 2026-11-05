// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Constants: each reference evaluates the constant's value at the declared
// type, with checked arithmetic, and a public constant has a getter.
contract Units {
    uint256 internal constant RAY = 10 ** 27;
    uint256 internal constant HALF_RAY = RAY / 2;
    string public constant NAME = "Units";
}

contract Constants is Units {
    uint8 public constant DECIMALS = 18;
    int256 public constant NEG = -5;
    uint256 public constant MAX_HALF = type(uint256).max / 2;
    uint8 constant BIG = 200;
    uint8 constant OVER = BIG * 2;
    bytes32 public constant TAG = bytes32(uint256(0xabc));
    string constant GREETING = "hello";
    bytes constant RAW = hex"0102ff";

    uint256 public scaled = 3 * RAY;

    function rmul(uint256 x, uint256 y) public pure returns (uint256) {
        return (x * y + HALF_RAY) / RAY;
    }

    function overflows() public pure returns (uint8) {
        return OVER;
    }

    function negated() public pure returns (int256) {
        return NEG * NEG + (-1);
    }

    function greeting() public pure returns (string memory) {
        return GREETING;
    }

    function rawLength() public pure returns (uint256) {
        return RAW.length * 2;
    }

    function fresh() public pure returns (bytes1) {
        bytes memory a = RAW;
        a[0] = bytes1(uint8(9));
        return RAW[0];
    }

    function folded() public pure returns (uint256) {
        return 2 ** 255 / 2 ** 250 + 21 / 3;
    }

    function scaledPlus(uint256 x) public view returns (uint256) {
        return scaled + x * DECIMALS;
    }
}
