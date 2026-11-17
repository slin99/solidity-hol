pragma solidity 0.8.37;

enum CopyEnum { A, B, C }

contract StorageEnumArrays {
    CopyEnum[] internal source;
    CopyEnum[] public dest;
    CopyEnum[35] internal fixedSource;
    CopyEnum[35] public fixedDest;
    uint256 public sentinel;

    constructor() {
        source.push(CopyEnum.A);
        source.push(CopyEnum.C);
        dest = source;
    }

    function copy() external { dest = source; }

    function copyAndRead() external returns (uint256, CopyEnum, CopyEnum) {
        dest = source;
        if (dest.length == 0) return (0, CopyEnum.A, CopyEnum.A);
        return (dest.length, dest[0], dest[dest.length - 1]);
    }

    function copyFixed() external { fixedDest = fixedSource; }

    function copyFixedAndRead() external returns (CopyEnum, CopyEnum, CopyEnum, CopyEnum, uint256) {
        fixedDest = fixedSource;
        return (fixedDest[0], fixedDest[31], fixedDest[32], fixedDest[34], sentinel);
    }

    function copyToSelf() external { source = source; }

}
