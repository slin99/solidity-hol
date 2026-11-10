# Compiler and execution profiles

Solidity-HOL separates its canonical source semantics from concrete compiler
compatibility profiles. A compatibility profile fixes all compiler and EVM
choices needed to reproduce compiled executions. The source artifact exporter uses an unoptimized default profile and a
restricted optimized fallback. Each artifact records the profile that produced
its output, so optimization never silently changes existing fixtures.

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

## Stack-depth fallback

Some contracts cannot generate bytecode with the unoptimized via-IR pipeline:
solc reports `YulException` or `CompilerError` with `stack too deep` or
`too deep in the stack`. The source artifact exporter retries those inputs with
[`profiles/solc-0.8.37-via-ir-osaka-optimized.json`](../profiles/solc-0.8.37-via-ir-osaka-optimized.json).
This profile differs only in `optimizer.enabled = true`; it keeps `runs = 200`.
The retry uses the same source names, contents, output selection and import
remappings. Every error must be a stack-depth error; other failures are returned
without retrying. A failed optimized retry is also a compilation failure.

A fallback artifact records the successful optimized settings in `profile` and
`input`, the optimized compiler output in `output`, and an `unoptimizedFailure`
object with the original unoptimized `profile` and its error diagnostics.
`solidityPrepareLib.read_artifact` and the differential runner require this
record before accepting an optimized source artifact. Unoptimized artifacts
must not carry it. The source exporter rejects explicit optimized-profile
requests: it always tries the unoptimized profile first. Metadata checks do not
prove that solc produced the recorded output; reproduction with the pinned
compiler checks that provenance.

The source importer uses the analyzed AST and storage layouts, which the
optimizer setting does not change. The optimized bytecode remains the concrete
execution oracle. This fallback does not broaden the supported source language
or admit AST-only artifacts. The separate Yul exporter continues to accept
explicit profiles for comparisons of optimizer stages.

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
