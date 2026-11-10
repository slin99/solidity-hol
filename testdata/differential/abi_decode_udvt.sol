// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.37;

type Account is address;

contract AbiDecodeUDVT {
    function single(bytes memory data) external pure returns (address) {
        return Account.unwrap(abi.decode(data, (Account)));
    }

    function mixed(bytes memory data) external pure returns (address, address) {
        (Account account, address plain) = abi.decode(data, (Account, address));
        return (Account.unwrap(account), plain);
    }

    function conditional(bool first, bytes memory left, bytes memory right)
        external pure returns (address)
    {
        return Account.unwrap(first
            ? abi.decode(left, (Account))
            : abi.decode(right, (Account)));
    }
}
