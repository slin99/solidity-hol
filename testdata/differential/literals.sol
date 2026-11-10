// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Literals {
    address stored;

    function units() public pure returns (uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256) {
        return (7 wei, 2 gwei, 3 ether, 4 seconds, 5 minutes, 6 hours, 7 days, 8 weeks);
    }

    function fractions() public pure returns (uint256, uint256, uint256, uint256) {
        return (0.9 ether, 0.04 ether, 0.5 wei * 2, 0.5 seconds * 2);
    }

    function precision() public pure returns (uint256, uint256) {
        return (0.693147180559945309 ether,
                57716089161558943949701069502944508345128.422502756744429568 ether);
    }

    function scientific() public pure returns (uint256, uint256, uint256, uint256) {
        return (1.5e-3 ether, 2e3 gwei, 1_000e-2, 0x1234_abcd);
    }

    function arithmetic(uint256 x) public pure returns (uint256, int256, bool) {
        return (x + 1 hours, -0.5 ether, x < 2 days);
    }

    function addressValue() public pure returns (address, address, address) {
        return (0x6B175474E89094C44Da98b954EedeAC495271d0F,
                0x0000000000000000000000000000000000000000,
                0x0000000000000000000000000000000000000001);
    }

    function addressEqual(address a) public pure returns (bool) {
        return a == 0x6B175474E89094C44Da98b954EedeAC495271d0F;
    }

    function saveAddress() public returns (address, uint160) {
        stored = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;
        return (stored, uint160(stored));
    }

    function strings() public pure returns (bytes3, bytes2, bytes3) {
        return (hex"0001ff", unicode"π", "a\x00b");
    }

    address public constant DAI = 0x6B175474E89094C44Da98b954EedeAC495271d0F;
    uint256 public constant YEAR = 365 days;
}
