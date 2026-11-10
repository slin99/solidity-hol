// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

library BaseHelpers {
    function increment(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }
}

abstract contract AbstractHook {
    function hook() internal pure virtual returns (uint256);

    function abstractCall() public pure returns (uint256) {
        return hook();
    }
}

abstract contract RedeclaredHook is AbstractHook {
    function hook() internal pure virtual override returns (uint256);
}

abstract contract NamedBase is RedeclaredHook {
    uint256 internal marker;

    struct Cell { uint256 value; }
    Cell internal firstCell;
    Cell internal secondCell;

    function cellRef() internal view virtual returns (Cell storage) {
        return firstCell;
    }

    modifier markBase() {
        marker = NamedBase.modifierValue();
        _;
    }

    function hook() internal pure virtual override returns (uint256) {
        return 3;
    }

    function value() public pure virtual returns (uint256) {
        return 100 + hook();
    }

    function helper() internal pure virtual returns (uint256) {
        return BaseHelpers.increment(40);
    }

    function chain() internal pure virtual returns (uint256) {
        return NamedBase.value() + NamedBase.helper();
    }

    function modifierValue() internal pure virtual returns (uint256) {
        return 17;
    }

    function initialValue() internal pure virtual returns (uint256) {
        return value() + 1;
    }

    function pick(address) internal pure virtual returns (uint256) {
        return 160;
    }

    function pick(uint256) internal pure virtual returns (uint256) {
        return 256;
    }

    function arguments(uint256 left, uint256 right) internal pure virtual returns (uint256) {
        return left * 10 + right;
    }
}

abstract contract NamedMiddle is NamedBase {
    function value() public pure virtual override returns (uint256) {
        return 200 + hook();
    }
}

abstract contract NamedSide is NamedBase {
    function value() public pure virtual override returns (uint256) {
        return super.value() + 10;
    }

    function staticAndSuper() public pure returns (uint256, uint256) {
        return (NamedBase.value(), super.value());
    }
}

contract QualifiedBaseCalls is NamedMiddle, NamedSide {
    uint256 public initialized = NamedBase.initialValue();
    uint256 private ticks;

    constructor() {
        marker = NamedBase.value();
    }

    function hook() internal pure override returns (uint256) {
        return 7;
    }

    function value() public pure override(NamedMiddle, NamedSide) returns (uint256) {
        return 300 + hook();
    }

    function helper() internal pure override returns (uint256) {
        return 999;
    }

    function chain() internal pure override returns (uint256) {
        return 9999;
    }

    function modifierValue() internal pure override returns (uint256) {
        return 777;
    }

    function initialValue() internal pure override returns (uint256) {
        return 888;
    }

    function arguments(uint256, uint256) internal pure override returns (uint256) {
        return 999;
    }

    function cellRef() internal view override returns (Cell storage) {
        return secondCell;
    }

    function storagePointer() public returns (uint256, uint256) {
        Cell storage saved = NamedBase.cellRef();
        saved.value = 7;
        NamedBase.cellRef().value += 5;
        cellRef().value = 19;
        return (firstCell.value, secondCell.value);
    }

    function fromBase() public pure returns (uint256) {
        return NamedBase.value();
    }

    function fromSuper() public pure returns (uint256) {
        return super.value();
    }

    function nestedStatic() public pure returns (uint256) {
        return NamedBase.chain();
    }

    function overloads() public pure returns (uint256, uint256) {
        return (NamedBase.pick(address(1)), NamedBase.pick(uint256(1)));
    }

    function next() internal returns (uint256) {
        return ++ticks;
    }

    function orderedArguments() public returns (uint256) {
        return NamedBase.arguments({right: next(), left: next()});
    }

    function viaModifier() public markBase returns (uint256) {
        return marker;
    }
}
