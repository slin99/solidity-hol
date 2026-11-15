// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;
import "./contract_creation_child.sol";

contract ContractCreation {
    address public rawCreated;
    address public sourceCreated;

    constructor() {
        bytes memory code = hex"60016000f3";
        assembly {
            sstore(rawCreated.slot, create(0, add(code, 32), mload(code)))
        }
        CreatedChild child = new CreatedChild(5);
        sourceCreated = address(child);
        require(child.read() == 5);
    }

    function plain(uint256 n) external returns (uint256) {
        CreatedChild child = new CreatedChild(n);
        return child.read();
    }

    function named(uint256 n) external returns (uint256) {
        CreatedChild child = new CreatedChild({n: n});
        return child.read();
    }

    function salted(uint256 n, bytes32 salt) external returns (uint256) {
        CreatedChild child = new CreatedChild{salt: salt}(n);
        return child.read();
    }

    function zeroSalt(uint256 n) external returns (uint256) {
        CreatedChild child = new CreatedChild{salt: 0}(n);
        return child.read();
    }

    function paid(uint256 n, bytes32 salt) external payable returns (uint256, uint256) {
        CreatedChild child = new CreatedChild{salt: salt, value: msg.value}(n);
        return (child.read(), address(child).balance);
    }

    function implicit() external returns (uint256) {
        CreatedImplicitChild child = new CreatedImplicitChild();
        return child.read();
    }

    function structure(uint256 n) external returns (uint256) {
        CreationParams memory p = CreationParams(n, hex"aabbcc");
        CreatedStructChild child = new CreatedStructChild(p);
        return child.read();
    }

    function collision(bytes32 salt) external returns (address) {
        new CreatedChild{salt: salt}(7);
        return address(new CreatedChild{salt: salt}(7));
    }

    function raw(bytes memory code, uint256 value) external payable returns (address created, uint256 size) {
        assembly {
            created := create(value, add(code, 32), mload(code))
            size := returndatasize()
        }
    }

    function rawSalt(bytes memory code, bytes32 salt) external returns (address created, uint256 size) {
        assembly {
            created := create2(0, add(code, 32), mload(code), salt)
            size := returndatasize()
        }
    }

    function rawCollision(bytes memory code, bytes32 salt) external returns (bool failed, uint256 size) {
        assembly {
            pop(create2(0, add(code, 32), mload(code), salt))
            failed := iszero(create2(0, add(code, 32), mload(code), salt))
            size := returndatasize()
        }
    }
}
