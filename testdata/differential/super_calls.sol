// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// super calls run the next implementation along the deployed contract's
// linearization: SuperCalls, PickNarrow, PickWide, Three, Two, Digits,
// Capped, Pausable, Ledger.
contract Ledger {
    mapping(address => uint256) balances;
    uint256 updates;

    modifier counted() {
        updates += 1;
        _;
    }

    function _update(address from, address to, uint256 amount) internal virtual counted {
        if (from != address(0)) {
            balances[from] -= amount;
        }
        balances[to] += amount;
    }
}

abstract contract Pausable is Ledger {
    bool paused;

    function _update(address from, address to, uint256 amount) internal virtual override {
        require(!paused, "paused");
        super._update(from, to, amount);
    }
}

abstract contract Capped is Ledger {
    uint256 total;

    function _update(address from, address to, uint256 amount) internal virtual override {
        super._update(from, to, amount);
        if (from == address(0)) {
            total += amount;
            require(total <= 1000);
        }
    }
}

abstract contract Digits {
    function digits() public pure virtual returns (uint256) {
        return 1;
    }
}

abstract contract Two is Digits {
    function digits() public pure virtual override returns (uint256) {
        return super.digits() * 10 + 2;
    }
}

// Three's super is Two in SuperCalls, though Three derives only from Digits.
abstract contract Three is Digits {
    function digits() public pure virtual override returns (uint256) {
        return super.digits() * 10 + 3;
    }
}

abstract contract PickWide {
    function pick(uint256) internal pure virtual returns (uint256) {
        return 256;
    }
}

abstract contract PickNarrow {
    function pick(uint8) internal pure virtual returns (uint256) {
        return 8;
    }
}

// The first base after SuperCalls with a pick is PickNarrow, whose pick takes
// a uint8, so super.pick(uint256) runs PickWide's.
contract SuperCalls is Pausable, Capped, Two, Three, PickWide, PickNarrow {
    uint256 last;

    // Skips this contract's own _update: from the constructor, super starts
    // after SuperCalls.
    constructor() {
        super._update(address(0), msg.sender, 5);
    }

    function _update(address from, address to, uint256 amount) internal override(Pausable, Capped) {
        super._update(from, to, amount);
        last = amount;
    }

    function digits() public pure override(Two, Three) returns (uint256) {
        return super.digits() * 10 + 4;
    }

    function pick(uint256 x) internal pure override returns (uint256) {
        return super.pick(x) + 1;
    }

    function picked() public pure returns (uint256) {
        return pick(uint256(1));
    }

    function mint(address to, uint256 amount) public {
        _update(address(0), to, amount);
    }

    function transfer(address to, uint256 amount) public {
        _update(msg.sender, to, amount);
    }

    function pauseAndMint(address to, uint256 amount) public {
        paused = true;
        _update(address(0), to, amount);
    }

    function mintTwice(address to, uint256 amount) public returns (uint256, uint256) {
        _update(address(0), to, amount);
        super._update(address(0), to, amount);
        return (balances[to], updates);
    }
}
