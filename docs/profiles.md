# Compiler and execution profiles

Solidity-HOL separates its canonical source semantics from concrete compiler
compatibility profiles. A compatibility profile fixes all compiler and EVM
choices needed to reproduce compiled executions. The initial implementation
supports one profile only; additional profiles must not silently change the
meaning of existing fixtures.

## Initial profile

The initial profile is `solc-0.8.37-via-ir-osaka`:

| Component | Selection |
| --- | --- |
| Solidity | `f401782df49be312ea4ef52a2d467cf5183b5906` (`v0.8.37`) |
| pipeline | via IR |
| optimizer | disabled, with `runs = 200` recorded explicitly |
| EVM revision | Osaka |
| revert strings | compiler default |
| bytecode metadata | CBOR trailer disabled and bytecode hash absent |
| Verifereum | `1b6508cefacfd54f78437fb72d7962503ddbe96c` |

The machine-readable settings are in
[`profiles/solc-0.8.37-via-ir-osaka.json`](../profiles/solc-0.8.37-via-ir-osaka.json).
The Solidity commit is independently pinned in [`SOLIDITY_PIN`](../SOLIDITY_PIN).
Disabling the optimizer does not disable mandatory lowering or all compiler
transformations.

Via IR is the forward-looking primary pipeline. The legacy code generator is
outside the initial supported profile and may be added later as a separate
compatibility profile. It does not define the canonical Solidity-HOL semantics.

## Evaluation order

Solidity 0.8.37 does not specify a general expression evaluation order. Its IR
pipeline tries to preserve left-to-right source order but does not guarantee it.
The canonical semantics may choose a deterministic order, while profile-specific
elaboration must encode the actual schedule of each construct rather than assume
a global compiler guarantee.

## Profile discipline

Every generated fixture must record:

- the full Solidity commit and reported compiler version;
- the exact profile settings;
- the source names and contents supplied through Standard JSON;
- compiler diagnostics and requested output kinds; and
- enough output to reproduce the claimed source/EVM observation.

Changing the compiler revision, pipeline, optimizer configuration, EVM revision,
or other observation-relevant settings creates a new profile. Unknown settings
or output forms must fail closed rather than being attributed to this profile.

The compiler input may additionally specify `settings.remappings` to resolve
import prefixes to source names without editing the source contents. This field
must occur at most once and contain an array of strings, each containing `=`;
it is retained in the artifact. All other input settings must still match the
pinned profile and output selection exactly.
