// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract DirtyBits {
    enum Choice { A, B }
    bool flag;
    Choice choice;
    bool[] dynamicSource;
    bool[] dynamicTarget;
    bool[2] fixedSource;
    bool[2] fixedTarget;

    function readBool() public view returns (bool) { return flag; }

    function unusedEnum() public view returns (uint256) {
        Choice unused = choice;
        return 7;
    }

    function encodeBool() public view returns (bytes memory) {
        return abi.encode(flag);
    }

    function encodeEnum() public view returns (bytes memory) {
        return abi.encode(choice);
    }

    function copyDynamic() public returns (uint256 word) {
        dynamicTarget = dynamicSource;
        assembly {
            mstore(0, dynamicTarget.slot)
            word := sload(keccak256(0, 32))
        }
    }

    function copyFixed() public returns (uint256 word) {
        fixedTarget = fixedSource;
        assembly { word := sload(fixedTarget.slot) }
    }

    function encodeBools() public view returns (bytes memory) {
        return abi.encode(fixedSource);
    }

    function canonicalSigned(int8 x) public pure returns (int8 back) {
        assembly { back := signextend(0, add(x, 0x100)) }
    }

    function dirtyBytes() public pure returns (bytes4 back) {
        assembly { back := 1 }
    }
}
