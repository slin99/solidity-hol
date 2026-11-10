// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract AbiEncoding {
    enum Kind { A, B, C }

    string public name;
    string public version;
    bytes longData;
    bytes shortData;
    uint256 public counter;

    bytes32 public constant PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

    function pay(uint256 x) external {}

    function tick(uint256 x) internal returns (uint256) {
        counter = counter * 10 + x;
        return x;
    }

    // The EIP-712 domain separator, as a token computes it.
    function domainSeparator(uint256 chainId) external view returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256(bytes(name)),
                keccak256(bytes(version)),
                chainId,
                address(this)
            )
        );
    }

    function permitDigest(bytes32 separator, address owner, address spender, uint256 value,
                          uint256 nonce, uint256 deadline) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(
            "\x19\x01",
            separator,
            keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline))
        ));
    }

    function scalars(uint8 a, int16 b, bool c, address d, bytes3 e) external pure returns (bytes memory) {
        return abi.encode(a, b, c, d, e, Kind.C);
    }

    function literals() external pure returns (bytes memory) {
        return abi.encode(-3, 7, "ab", hex"0102");
    }

    function dynamic(bytes calldata c, string memory m) external view returns (bytes memory) {
        return abi.encode(uint256(1), c, m, shortData, longData);
    }

    function packed(uint8 a, int16 b, bool c, address d, bytes3 e, bytes calldata f, string memory g)
        external view returns (bytes memory)
    {
        return abi.encodePacked(a, b, c, d, e, f, g, "lit", shortData, longData, Kind.B);
    }

    function signature(uint256 x) external pure returns (bytes memory) {
        return abi.encodeWithSignature("pay(uint256)", x);
    }

    function selector(uint256 x, bytes4 s) external pure returns (bytes memory, bytes memory) {
        return (abi.encodeWithSelector(this.pay.selector, x), abi.encodeWithSelector(s, x, "z"));
    }

    function order() external returns (bytes memory, uint256) {
        bytes memory r = abi.encode(tick(1), tick(2), tick(3));
        return (r, counter);
    }

    function length() external pure returns (uint256, uint256) {
        return (abi.encode(uint8(1), "abc").length, abi.encodePacked(uint16(1), "abc").length);
    }
}
