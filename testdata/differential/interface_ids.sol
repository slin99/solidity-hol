// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IBase {
    function base() external;
}

// Events, errors and inherited functions are not part of the interface id.
interface IToken is IBase {
    event Moved(uint256 amount);
    error Refused();

    function balanceOf(address owner) external view returns (uint256);
    function move(address to, uint256 amount) external returns (bool);
}

interface IOverloaded {
    function put(uint256 x) external;
    function put(bytes32 x, bool flag) external;
}

interface IEmpty {
    event Ping();
}

// A fallback and a receive function are not part of the interface id either.
interface IPayable {
    function pay() external payable;
    fallback() external;
    receive() external payable;
}

contract InterfaceIds {
    bytes4 constant TOKEN = type(IToken).interfaceId;

    function ids() external pure returns (bytes4, bytes4, bytes4, bytes4) {
        return (type(IToken).interfaceId, type(IBase).interfaceId,
                type(IOverloaded).interfaceId, type(IEmpty).interfaceId);
    }

    function fromConstant() external pure returns (bytes4) {
        return TOKEN;
    }

    function converted() external pure returns (bytes32, uint32) {
        bytes32 w = type(IToken).interfaceId;
        return (w, uint32(type(IBase).interfaceId));
    }

    function payableId() external pure returns (bytes4) {
        return type(IPayable).interfaceId;
    }

    function supportsInterface(bytes4 id) external pure returns (bool) {
        return id == type(IToken).interfaceId || id == type(IBase).interfaceId;
    }
}
