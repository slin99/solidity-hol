// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

library MixedLibrary {
    struct Pair { uint256 a; uint256 b; }

    function externalOnly(Pair memory p) private pure returns (uint256) {
        return p.a + p.b;
    }

    function linkedExternal(uint256 a) external pure returns (uint256) {
        return externalOnly(Pair(a, a));
    }

    function linkedPublic(uint256 a) public pure returns (uint256) {
        return a;
    }

    function safePrivate(uint256 a) private pure returns (uint256) {
        return a + 1;
    }

    function safeInternal(uint256 a) internal pure returns (uint256) {
        return safePrivate(a);
    }

    function indirect(uint256 a) internal pure returns (uint256) {
        return linkedPublic(a);
    }
}

contract ExternalLibrary {
    function supported(uint256 a) external pure returns (uint256) {
        return MixedLibrary.safeInternal(a);
    }

    function callsPublic(uint256 a) external pure returns (uint256) {
        return MixedLibrary.linkedPublic(a);
    }

    function callsExternal(uint256 a) external pure returns (uint256) {
        return MixedLibrary.linkedExternal(a);
    }

    function callsIndirect(uint256 a) public pure returns (uint256) {
        return MixedLibrary.indirect(a);
    }

    function callsCaller(uint256 a) external pure returns (uint256) {
        return callsIndirect(a);
    }
}
