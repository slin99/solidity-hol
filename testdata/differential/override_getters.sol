// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

interface IGetter {
    function value() external view returns (uint256);
    function limit() external view returns (uint256);
    function identity() external view returns (address);
    function balances(address account) external view returns (uint256);
}

interface IRefinedGetter is IGetter {
    function value() external view override returns (uint256);
}

contract GetterImplementation {
    function value() external view virtual returns (uint256) { return 999; }
    function limit() external pure virtual returns (uint256) { return 998; }
}

contract OverrideGetters is GetterImplementation, IRefinedGetter {
    uint256 public override(GetterImplementation, IRefinedGetter) value = 17;
    uint256 public constant override(GetterImplementation, IGetter) limit = 29;
    address public immutable override identity;
    mapping(address => uint256) public override balances;

    constructor(address owner) {
        identity = owner;
        balances[owner] = 23;
    }

    function setValue(uint256 next) external { value = next; }
    function readValue() external view returns (uint256) { return value; }
}
