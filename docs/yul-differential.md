# Yul three-way corpus report

The differential corpus through the Yul the pinned compiler emitted for the same sources, at the three stages the design separates, held to the same expectation the core evaluator and the deployed bytecode are held to.

- corpus: `testdata/differential/corpus.json`
- compiler: `~/.local/opt/solc-0.8.37/solc`

The HOL corpus was not run (--no-hol).

## Totals

- stages admitted: 0/0
- cases run: 0/2370
- agreements: 0

| stage | admitted | cases run | agreements |
| --- | ---: | ---: | ---: |
| ir | 0/0 | 0 | 0 |
| ir-optimized | 0/0 | 0 | 0 |
| optimized | 0/0 | 0 | 0 |

## Admissions

A stage the importer does not admit is reported here rather than worked around, and its cases are not run at that stage.

| suite | stage | admitted | status |
| --- | --- | --- | --- |

## Kernel-checked witnesses

Theorems of yulDifferentialCorpusTheory, proved by the HOL kernel (with cv_compute) when the theory was built. Each relates the Yul run to the bytecode run and to the case's expectation, and says what the run left in
storage and in the log.

| theorem | outcome |
| --- | --- |

## External checks

Performed by this driver outside the kernel.

| check | subject | status |
| --- | --- | --- |
| yul-artifact-generated | `testdata/yul/generated/pure_core.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/pure_core.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/pure_core.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/scalars.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/scalars.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/scalars.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/control.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/control.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/control.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/calls.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/calls.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/calls.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/storage.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/mappings.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/mappings.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/mappings.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_arrays.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/storage_arrays.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_arrays.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/dynamic_storage_arrays.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/dynamic_storage_arrays.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/dynamic_storage_arrays.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/builtins.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/builtins.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/builtins.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/shadowed_builtins.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/shadowed_builtins.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/shadowed_builtins.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_structs.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/storage_structs.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_structs.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_structs_top_level.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/storage_structs_top_level.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_structs_top_level.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/token.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/token.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/token.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/context.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/context.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/context.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/fallback.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/fallback.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/fallback.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/receive.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/receive.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/receive.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/external.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/external.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/external.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/inheritance.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/inheritance.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/inheritance.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/inheritance_diamond.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/inheritance_diamond.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/inheritance_diamond.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/constructors.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/constructors.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/constructors.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/inherited_payable.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/inherited_payable.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/inherited_payable.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/initializers_only.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/initializers_only.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/initializers_only.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/imports.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/imports.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/imports.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/errors.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/errors.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/errors.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/type_bounds.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/type_bounds.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/type_bounds.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/calldata_bytes.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/calldata_bytes.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/calldata_bytes.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/memory_bytes.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/memory_bytes.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/memory_bytes.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/memory_arrays.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/memory_arrays.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/memory_arrays.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/calldata_arrays.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/calldata_arrays.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/calldata_arrays.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_array_values.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/storage_array_values.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_array_values.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_array_growth.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/storage_array_growth.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_array_growth.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/super_calls.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/super_calls.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/super_calls.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/constants.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/constants.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/constants.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/immutables.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/immutables.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/immutables.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_bytes.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/storage_bytes.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_bytes.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_bytes_aliases.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/storage_bytes_aliases.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/storage_bytes_aliases.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/dynamic_bytes.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/dynamic_bytes.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/dynamic_bytes.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/oz_erc20.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/oz_erc20.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/oz_erc20.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/public_getters.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/public_getters.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/public_getters.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/modifiers.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/modifiers.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/modifiers.optimized.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/inline_assembly.ir.json` | pass |
| yul-artifact-is-the-same-program | `testdata/yul/generated/inline_assembly.ir.json` | pass |
| yul-artifact-generated | `testdata/yul/generated/inline_assembly.optimized.json` | pass |
| yul-artifacts-staged | `tests/yulDifferentialCorpusScript.sml` | pass |

## What is not an agreement

Each case's status is one of agree, mismatch, unexpected, storage-mismatch, storage-unexpected, log-mismatch, log-unexpected, inconclusive or error; only agree is an agreement, and the rest are listed here with the status that classifies them. An inconclusive is a diagnostic on one side, not a disagreement. A case at a stage the importer did not admit is not a disagreement either: it is counted above as an admission. Failures of another kind -- a suite that would not prepare, an external check, the HOL build -- are listed here too.

None.
