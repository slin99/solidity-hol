// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

contract TypeMembersChild {
    uint256 public value;

    constructor(uint256 v) {
        value = v;
    }

    function read() external view returns (uint256) {
        return value;
    }

    // More code, so that the creation code is a literal long enough to be
    // abbreviated in preparation.
    function add(uint256 x) external returns (uint256) {
        value += x;
        return value;
    }

    function scaled(uint256 x, uint256 y) external view returns (uint256, uint256) {
        return (value * x / (y + 1), value % (x + 1));
    }

    function label(uint256 x) external pure returns (string memory) {
        if (x == 0) return "zero";
        return x % 2 == 0 ? "even" : "odd";
    }
}

interface ISupports {
    function isSupported(bytes4 id) external view returns (bool);
}

// interfaceId of an abstract contract: its own public and external functions,
// overrides and unimplemented ones included, and its public state variables;
// not internal functions, inherited functions, the constructor or a fallback.
abstract contract TypeMembersHandler is ISupports {
    uint256 public handled;
    uint256 internal hidden;

    constructor() {}

    function handle(uint256 x) external virtual returns (uint256);

    function isSupported(bytes4 id) public view virtual override returns (bool) {
        return id == type(TypeMembersHandler).interfaceId;
    }

    function helper() internal pure returns (uint256) {
        return 1;
    }

    fallback() external {}
}

contract TypeMembers {
    function childName() external pure returns (string memory) {
        return type(TypeMembersChild).name;
    }

    function ownNameHash() external pure returns (bytes32, uint256) {
        string memory name = type(TypeMembers).name;
        return (keccak256(bytes(name)), bytes(name).length);
    }

    function codeLength() external pure returns (uint256) {
        return type(TypeMembersChild).creationCode.length;
    }

    function codeHash() external pure returns (bytes32) {
        return keccak256(type(TypeMembersChild).creationCode);
    }

    // The creation code deployed by create next to the same contract created
    // by new: both run and have the same runtime code.
    function deploy(uint256 v) external returns (uint256, uint256, bool) {
        bytes memory code = bytes.concat(type(TypeMembersChild).creationCode, abi.encode(v));
        address created;
        assembly {
            created := create(0, add(code, 32), mload(code))
        }
        TypeMembersChild child = new TypeMembersChild(v);
        return (TypeMembersChild(created).read(), child.read(),
                created.code.length == address(child).code.length);
    }

    function handlerId() external pure returns (bytes4) {
        return type(TypeMembersHandler).interfaceId;
    }

    function isSupportedId() external pure returns (bytes4) {
        return type(ISupports).interfaceId;
    }

    function decodeChild(address a, uint256 n) external pure returns (address, uint256) {
        (TypeMembersChild c, uint256 m) = abi.decode(abi.encode(a, n), (TypeMembersChild, uint256));
        return (address(c), m);
    }

    // A word that is not an address reverts the decode.
    function decodeDirty(uint256 word) external pure returns (address) {
        return address(abi.decode(abi.encode(word), (ISupports)));
    }
}
