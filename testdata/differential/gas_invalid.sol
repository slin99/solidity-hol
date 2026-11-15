// SPDX-License-Identifier: MIT
pragma solidity ^0.8.37;

contract GasInvalid {
    uint256 public stored;

    function difference() external view returns (uint256) {
        uint256 beforeGas = gasleft();
        return beforeGas - gasleft();
    }

    function assemblyDifference() external view returns (uint256 result) {
        assembly {
            let beforeGas := gas()
            result := sub(beforeGas, gas())
        }
    }

    function budget(address target) external returns (bool success) {
        assembly {
            success := call(gas(), target, 0, 0, 0, 0, 0)
        }
    }

    function mixed(address target) external returns (uint256 used, bool success) {
        uint256 beforeGas = gasleft();
        assembly {
            success := call(gas(), target, 0, 0, 0, 0, 0)
        }
        used = beforeGas - gasleft();
    }

    function abortNow() external {
        stored = 99;
        assembly {
            sstore(1, 123)
            tstore(2, 456)
            log0(0, 0)
            invalid()
        }
    }

    function explicitBudget(address target) external returns (bool success) {
        uint256 remaining = gasleft();
        assembly {
            success := call(remaining, target, 0, 0, 0, 0, 0)
        }
    }
}
