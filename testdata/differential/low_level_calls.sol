// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract LowLevelCalls {
    function raw(address target, bytes memory data) public view returns (bool, bytes memory) {
        return target.staticcall(data);
    }

    function rawPayable(address payable target, bytes memory data) public view returns (bool, bytes memory) {
        return target.staticcall(data);
    }

    function doubled(address target, bytes memory data) public view returns (bool, uint256) {
        (bool ok, bytes memory result) = target.staticcall(data);
        uint256 r;
        if (ok) r = abi.decode(result, (uint256));
        return (ok, r);
    }

    function twice(address target, bytes memory first, bytes memory second)
        public view returns (bytes memory, bytes memory, bytes memory)
    {
        (, bytes memory a) = target.staticcall(first);
        (, bytes memory b) = target.staticcall(second);
        return (a, b, first);
    }
}
