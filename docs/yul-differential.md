# Yul three-way corpus report

The differential corpus through the Yul the pinned compiler emitted for the same sources, at the three stages the design separates, held to the same expectation the core evaluator and the deployed bytecode are held to.

- corpus: `testdata/differential/corpus.json`
- compiler: `~/.local/opt/solc-0.8.37/solc`

HOL command: `holbuild -j 4 build --force=theory yulDifferentialCorpusTheory` (status 1).

## Totals

- stages admitted: 57/57
- cases run: 1059/1059
- agreements: 1026
- cases that are not agreements: 33 inconclusive

| stage | admitted | cases run | agreements |
| --- | ---: | ---: | ---: |
| ir | 19/19 | 353 | 342 |
| ir-optimized | 19/19 | 353 | 342 |
| optimized | 19/19 | 353 | 342 |

## Admissions

A stage the importer does not admit is reported here rather than worked around, and its cases are not run at that stage.

| suite | stage | admitted | status |
| --- | --- | --- | --- |
| pure_core | ir | yes |  |
| pure_core | ir-optimized | yes |  |
| pure_core | optimized | yes |  |
| scalars | ir | yes |  |
| scalars | ir-optimized | yes |  |
| scalars | optimized | yes |  |
| control | ir | yes |  |
| control | ir-optimized | yes |  |
| control | optimized | yes |  |
| calls | ir | yes |  |
| calls | ir-optimized | yes |  |
| calls | optimized | yes |  |
| storage | ir | yes |  |
| storage | ir-optimized | yes |  |
| storage | optimized | yes |  |
| mappings | ir | yes |  |
| mappings | ir-optimized | yes |  |
| mappings | optimized | yes |  |
| storage_arrays | ir | yes |  |
| storage_arrays | ir-optimized | yes |  |
| storage_arrays | optimized | yes |  |
| dynamic_storage_arrays | ir | yes |  |
| dynamic_storage_arrays | ir-optimized | yes |  |
| dynamic_storage_arrays | optimized | yes |  |
| builtins | ir | yes |  |
| builtins | ir-optimized | yes |  |
| builtins | optimized | yes |  |
| shadowed_builtins | ir | yes |  |
| shadowed_builtins | ir-optimized | yes |  |
| shadowed_builtins | optimized | yes |  |
| storage_structs | ir | yes |  |
| storage_structs | ir-optimized | yes |  |
| storage_structs | optimized | yes |  |
| storage_structs_top_level | ir | yes |  |
| storage_structs_top_level | ir-optimized | yes |  |
| storage_structs_top_level | optimized | yes |  |
| token | ir | yes |  |
| token | ir-optimized | yes |  |
| token | optimized | yes |  |
| context | ir | yes |  |
| context | ir-optimized | yes |  |
| context | optimized | yes |  |
| fallback | ir | yes |  |
| fallback | ir-optimized | yes |  |
| fallback | optimized | yes |  |
| receive | ir | yes |  |
| receive | ir-optimized | yes |  |
| receive | optimized | yes |  |
| external | ir | yes |  |
| external | ir-optimized | yes |  |
| external | optimized | yes |  |
| inheritance | ir | yes |  |
| inheritance | ir-optimized | yes |  |
| inheritance | optimized | yes |  |
| inheritance_diamond | ir | yes |  |
| inheritance_diamond | ir-optimized | yes |  |
| inheritance_diamond | optimized | yes |  |

## Kernel-checked witnesses

Theorems of yulDifferentialCorpusTheory, proved by the HOL kernel (with cv_compute) when the theory was built. Each relates the Yul run to the bytecode run and to the case's expectation, and says what the run left in
storage and in the log.

| theorem | outcome |
| --- | --- |
| `yul_pure_core_checked_branch_overwrite_returns_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_checked_branch_overwrite_returns_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_checked_branch_overwrite_returns_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_checked_branch_overwrite_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_checked_branch_overwrite_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_checked_branch_overwrite_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_add_returns_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_pure_core_add_returns_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_pure_core_add_returns_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_pure_core_add_boundary_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ff"} |
| `yul_pure_core_add_boundary_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ff"} |
| `yul_pure_core_add_boundary_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ff"} |
| `yul_pure_core_add_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_add_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_add_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_unchecked_add_wraps_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002c"} |
| `yul_pure_core_unchecked_add_wraps_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002c"} |
| `yul_pure_core_unchecked_add_wraps_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002c"} |
| `yul_pure_core_while_prelude_continue_exit_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_pure_core_while_prelude_continue_exit_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_pure_core_while_prelude_continue_exit_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_pure_core_while_break_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_pure_core_while_break_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_pure_core_while_break_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_pure_core_for_continue_increments_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_for_continue_increments_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_for_continue_increments_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_do_while_runs_once_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_pure_core_do_while_runs_once_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_pure_core_do_while_runs_once_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_pure_core_do_while_loops_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_do_while_loops_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_do_while_loops_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_pure_core_recursion_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000078"} |
| `yul_pure_core_recursion_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000078"} |
| `yul_pure_core_recursion_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000078"} |
| `yul_pure_core_recursion_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_recursion_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_recursion_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_multiple_returns_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_pure_core_multiple_returns_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_pure_core_multiple_returns_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_pure_core_division_by_zero_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_pure_core_division_by_zero_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_pure_core_division_by_zero_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_pure_core_tuple_assignment_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_pure_core_tuple_assignment_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_pure_core_tuple_assignment_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_pure_core_locals_and_tuple_declarations_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_pure_core_locals_and_tuple_declarations_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_pure_core_locals_and_tuple_declarations_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_pure_core_narrowing_conversion_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002c0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_narrowing_conversion_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002c0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_narrowing_conversion_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002c0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_negate_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_negate_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_negate_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_negate_returns_ir` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb"} |
| `yul_pure_core_negate_returns_ir_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb"} |
| `yul_pure_core_negate_returns_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb"} |
| `yul_pure_core_address_and_bytes_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234f0f0f0f000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_address_and_bytes_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234f0f0f0f000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_address_and_bytes_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234f0f0f0f000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_address_as_bytes_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beefffffffff00000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_address_as_bytes_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beefffffffff00000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_address_as_bytes_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beefffffffff00000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_and_skips_division_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_and_skips_division_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_and_skips_division_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_and_evaluates_division_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_pure_core_and_evaluates_division_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_pure_core_and_evaluates_division_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_pure_core_and_division_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_pure_core_and_division_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_pure_core_and_division_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_pure_core_or_skips_increment_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_or_skips_increment_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_or_skips_increment_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_pure_core_or_runs_increment_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_pure_core_or_runs_increment_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_pure_core_or_runs_increment_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_pure_core_left_operand_panics_first_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_left_operand_panics_first_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_left_operand_panics_first_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_left_argument_panics_first_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_left_argument_panics_first_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_left_argument_panics_first_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_pure_core_compound_assignment_reads_after_rhs_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_pure_core_compound_assignment_reads_after_rhs_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_pure_core_compound_assignment_reads_after_rhs_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_scalars_increment_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_scalars_increment_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_scalars_increment_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_scalars_increment_max_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_increment_max_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_increment_max_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_subtract_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_scalars_subtract_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_scalars_subtract_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_scalars_subtract_underflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_subtract_underflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_subtract_underflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_wrapping_subtract_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fe"} |
| `yul_scalars_wrapping_subtract_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fe"} |
| `yul_scalars_wrapping_subtract_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fe"} |
| `yul_scalars_multiply_minimum_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_multiply_minimum_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_multiply_minimum_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_multiply_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_multiply_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_multiply_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_multiply_minimum_by_minus_one_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_multiply_minimum_by_minus_one_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_multiply_minimum_by_minus_one_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_wrapping_multiply_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_wrapping_multiply_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_wrapping_multiply_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_wrapping_multiply_minimum_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_wrapping_multiply_minimum_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_wrapping_multiply_minimum_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_divide_truncates_ir` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd"} |
| `yul_scalars_divide_truncates_ir_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd"} |
| `yul_scalars_divide_truncates_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd"} |
| `yul_scalars_divide_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_divide_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_divide_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_divide_by_zero_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_divide_by_zero_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_divide_by_zero_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_wrapping_divide_minimum_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_wrapping_divide_minimum_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_wrapping_divide_minimum_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_wrapping_divide_by_zero_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_wrapping_divide_by_zero_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_wrapping_divide_by_zero_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_remainder_dividend_sign_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_remainder_dividend_sign_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_remainder_dividend_sign_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_remainder_divisor_sign_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_remainder_divisor_sign_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_remainder_divisor_sign_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_remainder_minimum_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_remainder_minimum_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_remainder_minimum_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_remainder_by_zero_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_remainder_by_zero_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_remainder_by_zero_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_scalars_power_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000080"} |
| `yul_scalars_power_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000080"} |
| `yul_scalars_power_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000080"} |
| `yul_scalars_power_zero_zero_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_power_zero_zero_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_power_zero_zero_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_power_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_power_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_power_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_wrapping_power_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_wrapping_power_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_wrapping_power_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_wrapping_power_in_range_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000f3"} |
| `yul_scalars_wrapping_power_in_range_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000f3"} |
| `yul_scalars_wrapping_power_in_range_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000f3"} |
| `yul_scalars_signed_power_minimum_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_signed_power_minimum_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_signed_power_minimum_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_signed_power_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_signed_power_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_signed_power_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_signed_power_odd_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe5"} |
| `yul_scalars_signed_power_odd_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe5"} |
| `yul_scalars_signed_power_odd_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe5"} |
| `yul_scalars_signed_power_minus_one_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_power_minus_one_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_power_minus_one_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_shift_truncates_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000040"} |
| `yul_scalars_shift_truncates_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000040"} |
| `yul_scalars_shift_truncates_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000040"} |
| `yul_scalars_shift_by_width_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_shift_by_width_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_shift_by_width_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_shift_beyond_width_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_shift_beyond_width_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_shift_beyond_width_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_signed_shift_minimum_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0"} |
| `yul_scalars_signed_shift_minimum_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0"} |
| `yul_scalars_signed_shift_minimum_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0"} |
| `yul_scalars_signed_shift_rounds_down_ir` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc"} |
| `yul_scalars_signed_shift_rounds_down_ir_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc"} |
| `yul_scalars_signed_shift_rounds_down_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc"} |
| `yul_scalars_signed_shift_minus_one_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_shift_minus_one_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_shift_minus_one_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_bitwise_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000f3"} |
| `yul_scalars_bitwise_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000f3"} |
| `yul_scalars_bitwise_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000f3"} |
| `yul_scalars_signed_not_zero_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_not_zero_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_not_zero_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_not_minimum_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000007f"} |
| `yul_scalars_signed_not_minimum_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000007f"} |
| `yul_scalars_signed_not_minimum_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000007f"} |
| `yul_scalars_signed_less_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_signed_less_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_signed_less_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_signed_less_equal_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_signed_less_equal_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_signed_less_equal_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_widen_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_widen_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_widen_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_reinterpret_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_reinterpret_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_reinterpret_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_reinterpret_minimum_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000080ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_reinterpret_minimum_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000080ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_reinterpret_minimum_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000080ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80"} |
| `yul_scalars_truncate_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_truncate_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_truncate_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_truncate_sign_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000008000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_scalars_truncate_sign_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000008000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_scalars_truncate_sign_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000008000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_scalars_signed_to_unsigned_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_to_unsigned_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_signed_to_unsigned_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_scalars_implicit_widening_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000fde8"} |
| `yul_scalars_implicit_widening_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000fde8"} |
| `yul_scalars_implicit_widening_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000fde8"} |
| `yul_scalars_implicit_widening_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_implicit_widening_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_implicit_widening_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_scalars_bool_logic_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_bool_logic_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_bool_logic_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_scalars_bool_logic_both_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_bool_logic_both_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_scalars_bool_logic_both_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_inner_break_outer_continue_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_control_inner_break_outer_continue_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_control_inner_break_outer_continue_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_control_inner_break_outer_continue_empty_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_inner_break_outer_continue_empty_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_inner_break_outer_continue_empty_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_inner_continue_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_control_inner_continue_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_control_inner_continue_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_control_outer_break_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_outer_break_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_outer_break_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_return_from_nested_loops_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_return_from_nested_loops_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_return_from_nested_loops_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_return_after_nested_loops_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_return_after_nested_loops_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_return_after_nested_loops_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_return_at_first_iteration_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_return_at_first_iteration_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_return_at_first_iteration_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_do_while_continue_reaches_condition_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_do_while_continue_reaches_condition_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_do_while_continue_reaches_condition_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_do_while_continue_exits_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_control_do_while_continue_exits_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_control_do_while_continue_exits_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_control_do_while_body_once_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_control_do_while_body_once_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_control_do_while_body_once_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_control_break_in_nested_do_while_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_control_break_in_nested_do_while_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_control_break_in_nested_do_while_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_control_for_without_condition_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_control_for_without_condition_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_control_for_without_condition_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_control_for_without_condition_immediate_break_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_for_without_condition_immediate_break_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_for_without_condition_immediate_break_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_else_if_negative_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_else_if_negative_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_else_if_negative_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_else_if_zero_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_control_else_if_zero_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_control_else_if_zero_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_control_else_if_small_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_control_else_if_small_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_control_else_if_small_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_control_fall_through_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_fall_through_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_fall_through_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_control_loop_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_control_loop_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_control_loop_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_control_loop_without_overflow_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_loop_without_overflow_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_control_loop_without_overflow_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_calls_mutual_recursion_even_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_mutual_recursion_even_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_mutual_recursion_even_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_mutual_recursion_odd_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_mutual_recursion_odd_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_mutual_recursion_odd_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_mutual_recursion_not_even_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_calls_mutual_recursion_not_even_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_calls_mutual_recursion_not_even_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_calls_tree_recursion_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000037"} |
| `yul_calls_tree_recursion_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000037"} |
| `yul_calls_tree_recursion_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000037"} |
| `yul_calls_nested_recursion_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_calls_nested_recursion_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_calls_nested_recursion_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_calls_multiple_returns_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_calls_multiple_returns_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_calls_multiple_returns_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_calls_tuple_from_call_ordered_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_calls_tuple_from_call_ordered_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_calls_tuple_from_call_ordered_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_calls_tuple_from_call_swapped_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_calls_tuple_from_call_swapped_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_calls_tuple_from_call_swapped_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_calls_checked_call_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8"} |
| `yul_calls_checked_call_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8"} |
| `yul_calls_checked_call_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8"} |
| `yul_calls_checked_call_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_checked_call_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_checked_call_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_arguments_left_to_right_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_calls_arguments_left_to_right_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_calls_arguments_left_to_right_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_calls_operands_left_to_right_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_operands_left_to_right_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_operands_left_to_right_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_tuple_writes_right_to_left_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_tuple_writes_right_to_left_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_tuple_writes_right_to_left_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_rotate_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_rotate_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_rotate_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_swap_through_call_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_swap_through_call_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_swap_through_call_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_calls_tuple_holes_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_calls_tuple_holes_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_calls_tuple_holes_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_calls_result_widened_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8"} |
| `yul_calls_result_widened_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8"} |
| `yul_calls_result_widened_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8"} |
| `yul_calls_result_widened_after_panic_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_result_widened_after_panic_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_result_widened_after_panic_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_prefix_and_postfix_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000d"} |
| `yul_calls_prefix_and_postfix_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000d"} |
| `yul_calls_prefix_and_postfix_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000d"} |
| `yul_calls_decrement_underflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_decrement_underflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_decrement_underflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_calls_decrement_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_calls_decrement_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_calls_decrement_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_calls_wrapping_decrement_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_calls_wrapping_decrement_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_calls_wrapping_decrement_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_storage_set_total_ir` | {"returned": "0x"} |
| `yul_storage_set_total_ir_optimized` | {"returned": "0x"} |
| `yul_storage_set_total_optimized` | {"returned": "0x"} |
| `yul_storage_get_total_reads_storage_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002a"} |
| `yul_storage_get_total_reads_storage_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002a"} |
| `yul_storage_get_total_reads_storage_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000002a"} |
| `yul_storage_dirty_bool_reads_true_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_dirty_bool_reads_true_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_dirty_bool_reads_true_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_packed_slot_keeps_neighbours_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000010000000000000000000000001234567890abcdef1234567890abcdef12345678"} |
| `yul_storage_packed_slot_keeps_neighbours_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000010000000000000000000000001234567890abcdef1234567890abcdef12345678"} |
| `yul_storage_packed_slot_keeps_neighbours_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000c8fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000010000000000000000000000001234567890abcdef1234567890abcdef12345678"} |
| `yul_storage_fixed_bytes_ir` | {"returned": "0x1234567800000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_fixed_bytes_ir_optimized` | {"returned": "0x1234567800000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_fixed_bytes_optimized` | {"returned": "0x1234567800000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_halves_share_slot_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_storage_halves_share_slot_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_storage_halves_share_slot_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_storage_writes_seen_across_calls_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_storage_writes_seen_across_calls_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_storage_writes_seen_across_calls_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_storage_increments_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fd00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_storage_increments_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fd00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_storage_increments_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fd00000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_storage_increments_dirty_slot_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fd00000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_storage_increments_dirty_slot_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fd00000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_storage_increments_dirty_slot_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fd00000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_storage_overflow_discards_writes_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_overflow_discards_writes_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_overflow_discards_writes_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_revert_discards_writes_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_storage_revert_discards_writes_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_storage_revert_discards_writes_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_storage_no_revert_keeps_writes_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_storage_no_revert_keeps_writes_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_storage_no_revert_keeps_writes_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_storage_tuple_swap_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_storage_tuple_swap_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_storage_tuple_swap_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_storage_read_before_call_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_storage_read_before_call_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_storage_read_before_call_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"} |
| `yul_storage_compound_signed_ir` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb"} |
| `yul_storage_compound_signed_ir_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb"} |
| `yul_storage_compound_signed_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb"} |
| `yul_mappings_default_zero_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_default_zero_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_default_zero_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_seeded_read_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000025"} |
| `yul_mappings_seeded_read_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000025"} |
| `yul_mappings_seeded_read_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000025"} |
| `yul_mappings_set_zero_key_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000013"} |
| `yul_mappings_set_zero_key_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000013"} |
| `yul_mappings_set_zero_key_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000013"} |
| `yul_mappings_set_max_key_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ff"} |
| `yul_mappings_set_max_key_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ff"} |
| `yul_mappings_set_max_key_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000ff"} |
| `yul_mappings_distinct_keys_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000001d"} |
| `yul_mappings_distinct_keys_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000001d"} |
| `yul_mappings_distinct_keys_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000001d"} |
| `yul_mappings_same_key_alias_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000001d000000000000000000000000000000000000000000000000000000000000001d"} |
| `yul_mappings_same_key_alias_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000001d000000000000000000000000000000000000000000000000000000000000001d"} |
| `yul_mappings_same_key_alias_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000001d000000000000000000000000000000000000000000000000000000000000001d"} |
| `yul_mappings_compound_prefix_postfix_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_mappings_compound_prefix_postfix_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_mappings_compound_prefix_postfix_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_mappings_signed_negative_key_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff85"} |
| `yul_mappings_signed_negative_key_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff85"} |
| `yul_mappings_signed_negative_key_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff85"} |
| `yul_mappings_signed_min_key_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_mappings_signed_min_key_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_mappings_signed_min_key_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_mappings_signed_positive_key_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000007fff"} |
| `yul_mappings_signed_positive_key_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000007fff"} |
| `yul_mappings_signed_positive_key_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000007fff"} |
| `yul_mappings_address_key_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_mappings_address_key_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_mappings_address_key_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_mappings_clear_address_key_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_clear_address_key_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_clear_address_key_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_bytes_left_aligned_key_ir` | {"returned": "0x89abcdef00000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_bytes_left_aligned_key_ir_optimized` | {"returned": "0x89abcdef00000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_bytes_left_aligned_key_optimized` | {"returned": "0x89abcdef00000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_bytes_zero_key_ir` | {"returned": "0x0000000100000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_bytes_zero_key_ir_optimized` | {"returned": "0x0000000100000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_bytes_zero_key_optimized` | {"returned": "0x0000000100000000000000000000000000000000000000000000000000000000"} |
| `yul_mappings_nested_mapping_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_mappings_nested_mapping_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_mappings_nested_mapping_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_mappings_nested_distinct_paths_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000020"} |
| `yul_mappings_nested_distinct_paths_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000020"} |
| `yul_mappings_nested_distinct_paths_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000020"} |
| `yul_mappings_keys_evaluated_once_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_keys_evaluated_once_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_keys_evaluated_once_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_assignment_rhs_before_key_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_assignment_rhs_before_key_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_assignment_rhs_before_key_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_compound_rhs_before_key_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_compound_rhs_before_key_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_compound_rhs_before_key_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_nested_keys_once_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_nested_keys_once_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_nested_keys_once_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_mappings_bool_true_key_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234"} |
| `yul_mappings_bool_true_key_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234"} |
| `yul_mappings_bool_true_key_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234"} |
| `yul_mappings_bool_false_key_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beef"} |
| `yul_mappings_bool_false_key_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beef"} |
| `yul_mappings_bool_false_key_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beef"} |
| `yul_mappings_internal_visibility_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_mappings_internal_visibility_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_mappings_internal_visibility_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_mappings_rollback_internal_write_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_mappings_rollback_internal_write_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_mappings_rollback_internal_write_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_mappings_rollback_key_side_effect_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_mappings_rollback_key_side_effect_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_mappings_rollback_key_side_effect_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_mappings_compound_reads_after_rhs_write_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_mappings_compound_reads_after_rhs_write_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_mappings_compound_reads_after_rhs_write_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_mappings_preserve_upper_bytes_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_mappings_preserve_upper_bytes_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_mappings_preserve_upper_bytes_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_storage_arrays_fixed_lengths_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000230000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_arrays_fixed_lengths_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000230000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_arrays_fixed_lengths_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000230000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_arrays_packed_neighbour_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_arrays_packed_neighbour_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_arrays_packed_neighbour_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_arrays_last_in_first_slot_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_last_in_first_slot_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_last_in_first_slot_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_first_in_second_slot_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_first_in_second_slot_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_first_in_second_slot_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_last_element_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_last_element_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_last_element_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_arrays_signed_packed_ir` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_storage_arrays_signed_packed_ir_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_storage_arrays_signed_packed_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_storage_arrays_signed_second_slot_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_arrays_signed_second_slot_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_arrays_signed_second_slot_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_arrays_bytes_neighbours_ir` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_bytes_neighbours_ir_optimized` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_bytes_neighbours_optimized` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_bytes_second_slot_ir` | {"returned": "0xabcdef0000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_bytes_second_slot_ir_optimized` | {"returned": "0xabcdef0000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_bytes_second_slot_optimized` | {"returned": "0xabcdef0000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_nested_row_alignment_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000123456"} |
| `yul_storage_arrays_nested_row_alignment_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000123456"} |
| `yul_storage_arrays_nested_row_alignment_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000123456"} |
| `yul_storage_arrays_nested_row_tail_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000abcdef"} |
| `yul_storage_arrays_nested_row_tail_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000abcdef"} |
| `yul_storage_arrays_nested_row_tail_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000abcdef"} |
| `yul_storage_arrays_indices_evaluated_once_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_storage_arrays_indices_evaluated_once_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_storage_arrays_indices_evaluated_once_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000a"} |
| `yul_storage_arrays_writes_across_calls_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_storage_arrays_writes_across_calls_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_storage_arrays_writes_across_calls_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_storage_arrays_bounds_rolls_back_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_bounds_rolls_back_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_bounds_rolls_back_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_large_index_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_large_index_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_large_index_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_outer_bounds_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_outer_bounds_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_outer_bounds_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_inner_bounds_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_inner_bounds_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_inner_bounds_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_overflow_rolls_back_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_arrays_overflow_rolls_back_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_arrays_overflow_rolls_back_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_arrays_rhs_before_index_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_storage_arrays_rhs_before_index_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_storage_arrays_rhs_before_index_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_storage_arrays_nested_indices_evaluated_once_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_arrays_nested_indices_evaluated_once_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_arrays_nested_indices_evaluated_once_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_arrays_length_evaluates_prefix_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_arrays_length_evaluates_prefix_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_arrays_length_evaluates_prefix_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_arrays_length_checks_prefix_bounds_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_length_checks_prefix_bounds_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_length_checks_prefix_bounds_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_arrays_unwritten_element_is_zero_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_unwritten_element_is_zero_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_unwritten_element_is_zero_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_dirty_bool_reads_true_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_arrays_dirty_bool_reads_true_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_arrays_dirty_bool_reads_true_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_arrays_bool_neighbour_preserved_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_bool_neighbour_preserved_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_bool_neighbour_preserved_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_arrays_address_does_not_straddle_slot_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234"} |
| `yul_storage_arrays_address_does_not_straddle_slot_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234"} |
| `yul_storage_arrays_address_does_not_straddle_slot_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001234"} |
| `yul_storage_arrays_full_width_element_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000017"} |
| `yul_storage_arrays_full_width_element_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000017"} |
| `yul_storage_arrays_full_width_element_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000017"} |
| `yul_storage_arrays_length_prefix_preserves_earlier_locals_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_arrays_length_prefix_preserves_earlier_locals_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_arrays_length_prefix_preserves_earlier_locals_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_empty_length_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_empty_length_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_empty_length_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_corrupt_full_length_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_dynamic_storage_arrays_corrupt_full_length_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_dynamic_storage_arrays_corrupt_full_length_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} |
| `yul_dynamic_storage_arrays_empty_bounds_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_empty_bounds_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_empty_bounds_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_append_first_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_dynamic_storage_arrays_append_first_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_dynamic_storage_arrays_append_first_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_dynamic_storage_arrays_append_preserves_packed_neighbour_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_dynamic_storage_arrays_append_preserves_packed_neighbour_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_dynamic_storage_arrays_append_preserves_packed_neighbour_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_dynamic_storage_arrays_append_crosses_slot_boundary_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000021000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_append_crosses_slot_boundary_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000021000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_append_crosses_slot_boundary_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000021000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_default_append_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_default_append_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_default_append_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_default_append_preserves_dirty_element_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000081"} |
| `yul_dynamic_storage_arrays_default_append_preserves_dirty_element_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000081"} |
| `yul_dynamic_storage_arrays_default_append_preserves_dirty_element_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000081"} |
| `yul_dynamic_storage_arrays_append_lvalue_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000013"} |
| `yul_dynamic_storage_arrays_append_lvalue_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000013"} |
| `yul_dynamic_storage_arrays_append_lvalue_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000013"} |
| `yul_dynamic_storage_arrays_append_lvalue_update_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_append_lvalue_update_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_append_lvalue_update_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_scalar_assignment_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_dynamic_storage_arrays_scalar_assignment_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_dynamic_storage_arrays_scalar_assignment_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_dynamic_storage_arrays_scalar_update_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_scalar_update_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_scalar_update_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_index_equal_length_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_index_equal_length_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_index_equal_length_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_index_max_uint256_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_index_max_uint256_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_index_max_uint256_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_huge_index_has_no_host_limit_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000005d"} |
| `yul_dynamic_storage_arrays_huge_index_has_no_host_limit_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000005d"} |
| `yul_dynamic_storage_arrays_huge_index_has_no_host_limit_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000005d"} |
| `yul_dynamic_storage_arrays_pop_clears_only_removed_byte_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_pop_clears_only_removed_byte_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_pop_clears_only_removed_byte_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_pop_last_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_pop_last_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_pop_last_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_pop_slot_boundary_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000020"} |
| `yul_dynamic_storage_arrays_pop_slot_boundary_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000020"} |
| `yul_dynamic_storage_arrays_pop_slot_boundary_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000020"} |
| `yul_dynamic_storage_arrays_empty_pop_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000031"} |
| `yul_dynamic_storage_arrays_empty_pop_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000031"} |
| `yul_dynamic_storage_arrays_empty_pop_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000031"} |
| `yul_dynamic_storage_arrays_pop_and_default_regrowth_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_pop_and_default_regrowth_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_pop_and_default_regrowth_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_append_resource_boundary_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_append_resource_boundary_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_append_resource_boundary_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_append_corrupt_max_length_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_append_corrupt_max_length_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_append_corrupt_max_length_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_appendDefault_resource_boundary_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_appendDefault_resource_boundary_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_appendDefault_resource_boundary_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_appendDefault_corrupt_max_length_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_appendDefault_corrupt_max_length_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_appendDefault_corrupt_max_length_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000041"} |
| `yul_dynamic_storage_arrays_last_admissible_push_ir` | {"returned": "0x00000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_dynamic_storage_arrays_last_admissible_push_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_dynamic_storage_arrays_last_admissible_push_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_dynamic_storage_arrays_corrupt_max_length_pop_ir` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_dynamic_storage_arrays_corrupt_max_length_pop_ir_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_dynamic_storage_arrays_corrupt_max_length_pop_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"} |
| `yul_dynamic_storage_arrays_signed_append_preserves_neighbour_ir` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_signed_append_preserves_neighbour_ir_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_signed_append_preserves_neighbour_optimized` | {"returned": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_signed_pop_clears_bytes_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_signed_pop_clears_bytes_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_signed_pop_clears_bytes_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_fixed_bytes_append_ir` | {"returned": "0x12345600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_fixed_bytes_append_ir_optimized` | {"returned": "0x12345600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_fixed_bytes_append_optimized` | {"returned": "0x12345600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_fixed_bytes_pop_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_fixed_bytes_pop_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_fixed_bytes_pop_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_fixed_bytes_slot_boundary_ir` | {"returned": "0x6543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_fixed_bytes_slot_boundary_ir_optimized` | {"returned": "0x6543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_fixed_bytes_slot_boundary_optimized` | {"returned": "0x6543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_dynamic_storage_arrays_boolean_append_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_boolean_append_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_boolean_append_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_address_append_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beef0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_address_append_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beef0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_address_append_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000beef0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_full_word_append_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_full_word_append_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_full_word_append_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_dynamic_storage_arrays_mutation_bases_arguments_once_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_dynamic_storage_arrays_mutation_bases_arguments_once_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_dynamic_storage_arrays_mutation_bases_arguments_once_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_dynamic_storage_arrays_rhs_before_index_once_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_dynamic_storage_arrays_rhs_before_index_once_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_dynamic_storage_arrays_rhs_before_index_once_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_dynamic_storage_arrays_length_prefix_snapshots_earlier_local_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_length_prefix_snapshots_earlier_local_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_length_prefix_snapshots_earlier_local_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_internal_call_visibility_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000290000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_internal_call_visibility_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000290000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_internal_call_visibility_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000290000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_bounds_rolls_back_earlier_mutations_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_bounds_rolls_back_earlier_mutations_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_bounds_rolls_back_earlier_mutations_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_dynamic_storage_arrays_empty_pop_rolls_back_earlier_mutations_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000031"} |
| `yul_dynamic_storage_arrays_empty_pop_rolls_back_earlier_mutations_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000031"} |
| `yul_dynamic_storage_arrays_empty_pop_rolls_back_earlier_mutations_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000031"} |
| `yul_dynamic_storage_arrays_overflow_rolls_back_push_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_dynamic_storage_arrays_overflow_rolls_back_push_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_dynamic_storage_arrays_overflow_rolls_back_push_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_dynamic_storage_arrays_mutation_prefix_snapshots_earlier_local_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_mutation_prefix_snapshots_earlier_local_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_mutation_prefix_snapshots_earlier_local_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_dynamic_storage_arrays_argument_mutation_updates_current_length_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_dynamic_storage_arrays_argument_mutation_updates_current_length_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_dynamic_storage_arrays_argument_mutation_updates_current_length_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_dynamic_storage_arrays_pop_base_evaluated_once_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_pop_base_evaluated_once_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_dynamic_storage_arrays_pop_base_evaluated_once_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_require_true_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_builtins_require_true_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_builtins_require_true_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000016"} |
| `yul_builtins_require_false_ir` | {"reverted": "0x"} |
| `yul_builtins_require_false_ir_optimized` | {"reverted": "0x"} |
| `yul_builtins_require_false_optimized` | {"reverted": "0x"} |
| `yul_builtins_requireMessage_true_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_builtins_requireMessage_true_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_builtins_requireMessage_true_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_builtins_requireMessage_false_ir` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f6c69746572616c206d6573736167650000000000000000000000000000000000"} |
| `yul_builtins_requireMessage_false_ir_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f6c69746572616c206d6573736167650000000000000000000000000000000000"} |
| `yul_builtins_requireMessage_false_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f6c69746572616c206d6573736167650000000000000000000000000000000000"} |
| `yul_builtins_requireEmpty_true_ir` | {"returned": "0x"} |
| `yul_builtins_requireEmpty_true_ir_optimized` | {"returned": "0x"} |
| `yul_builtins_requireEmpty_true_optimized` | {"returned": "0x"} |
| `yul_builtins_requireEmpty_false_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_requireEmpty_false_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_requireEmpty_false_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_requireUnicode_true_ir` | {"returned": "0x"} |
| `yul_builtins_requireUnicode_true_ir_optimized` | {"returned": "0x"} |
| `yul_builtins_requireUnicode_true_optimized` | {"returned": "0x"} |
| `yul_builtins_requireUnicode_false_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000006c3a9f09f99820000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_requireUnicode_false_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000006c3a9f09f99820000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_requireUnicode_false_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000006c3a9f09f99820000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_requireLong_true_ir` | {"returned": "0x"} |
| `yul_builtins_requireLong_true_ir_optimized` | {"returned": "0x"} |
| `yul_builtins_requireLong_true_optimized` | {"returned": "0x"} |
| `yul_builtins_requireLong_false_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000041303132333435363738393031323334353637383930313233343536373839303132333435363738393031323334353637383930313233343536373839303132333400000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_requireLong_false_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000041303132333435363738393031323334353637383930313233343536373839303132333435363738393031323334353637383930313233343536373839303132333400000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_requireLong_false_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000041303132333435363738393031323334353637383930313233343536373839303132333435363738393031323334353637383930313233343536373839303132333400000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_assert_true_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_builtins_assert_true_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_builtins_assert_true_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_builtins_assert_false_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_builtins_assert_false_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_builtins_assert_false_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_builtins_bareRevert_ir` | {"reverted": "0x"} |
| `yul_builtins_bareRevert_ir_optimized` | {"reverted": "0x"} |
| `yul_builtins_bareRevert_optimized` | {"reverted": "0x"} |
| `yul_builtins_emptyRevert_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_emptyRevert_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_emptyRevert_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_messageRevert_ir` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f6c69746572616c206d6573736167650000000000000000000000000000000000"} |
| `yul_builtins_messageRevert_ir_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f6c69746572616c206d6573736167650000000000000000000000000000000000"} |
| `yul_builtins_messageRevert_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f6c69746572616c206d6573736167650000000000000000000000000000000000"} |
| `yul_builtins_unicodeRevert_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000006c3a9f09f99820000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_unicodeRevert_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000006c3a9f09f99820000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_unicodeRevert_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000006c3a9f09f99820000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_boundaryRevert_ir` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000203031323334353637383930313233343536373839303132333435363738393031"} |
| `yul_builtins_boundaryRevert_ir_optimized` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000203031323334353637383930313233343536373839303132333435363738393031"} |
| `yul_builtins_boundaryRevert_optimized` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000203031323334353637383930313233343536373839303132333435363738393031"} |
| `yul_builtins_longRevert_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000041303132333435363738393031323334353637383930313233343536373839303132333435363738393031323334353637383930313233343536373839303132333400000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_longRevert_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000041303132333435363738393031323334353637383930313233343536373839303132333435363738393031323334353637383930313233343536373839303132333400000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_longRevert_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000041303132333435363738393031323334353637383930313233343536373839303132333435363738393031323334353637383930313233343536373839303132333400000000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_nulRevert_ir` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000036100620000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_nulRevert_ir_optimized` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000036100620000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_nulRevert_optimized` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000036100620000000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_hexRevert_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000004c3a9006100000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_hexRevert_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000004c3a9006100000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_hexRevert_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000004c3a9006100000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_internal_require_success_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000043"} |
| `yul_builtins_internal_require_success_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000043"} |
| `yul_builtins_internal_require_success_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000043"} |
| `yul_builtins_internal_require_rollback_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000005696e6e6572000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_internal_require_rollback_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000005696e6e6572000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_internal_require_rollback_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000005696e6e6572000000000000000000000000000000000000000000000000000000"} |
| `yul_builtins_internal_assert_rollback_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_builtins_internal_assert_rollback_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_builtins_internal_assert_rollback_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_builtins_internal_revert_rollback_ir` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c696e6e6572207265766572740000000000000000000000000000000000000000"} |
| `yul_builtins_internal_revert_rollback_ir_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c696e6e6572207265766572740000000000000000000000000000000000000000"} |
| `yul_builtins_internal_revert_rollback_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c696e6e6572207265766572740000000000000000000000000000000000000000"} |
| `yul_builtins_condition_panic_before_require_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_builtins_condition_panic_before_require_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_builtins_condition_panic_before_require_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000012"} |
| `yul_builtins_condition_failure_ir` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f636f6e646974696f6e2066616c73650000000000000000000000000000000000"} |
| `yul_builtins_condition_failure_ir_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f636f6e646974696f6e2066616c73650000000000000000000000000000000000"} |
| `yul_builtins_condition_failure_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000f636f6e646974696f6e2066616c73650000000000000000000000000000000000"} |
| `yul_builtins_condition_success_ir` | {"returned": "0x"} |
| `yul_builtins_condition_success_ir_optimized` | {"returned": "0x"} |
| `yul_builtins_condition_success_optimized` | {"returned": "0x"} |
| `yul_builtins_local_condition_once_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_builtins_local_condition_once_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_builtins_local_condition_once_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_shadowed_builtins_shadowed_true_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_shadowed_builtins_shadowed_true_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_shadowed_builtins_shadowed_true_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_shadowed_builtins_shadowed_false_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_shadowed_builtins_shadowed_false_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_shadowed_builtins_shadowed_false_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000005"} |
| `yul_storage_structs_packed_fields_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe12345600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_structs_packed_fields_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe12345600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_structs_packed_fields_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe12345600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_storage_structs_scalar_neighbours_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_scalar_neighbours_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_scalar_neighbours_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_nested_alignment_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_structs_nested_alignment_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_structs_nested_alignment_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000b"} |
| `yul_storage_structs_mapped_signed_0_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_mapped_signed_0_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_mapped_signed_0_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_mapped_signed_7_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_mapped_signed_7_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_mapped_signed_7_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_mapped_signed_115792089237316195423570985008687907853269984665640564039457584007913129639935_ir` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_mapped_signed_115792089237316195423570985008687907853269984665640564039457584007913129639935_ir_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_mapped_signed_115792089237316195423570985008687907853269984665640564039457584007913129639935_optimized` | {"returned": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000"} |
| `yul_storage_structs_fixed_struct_element_ir` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_fixed_struct_element_ir_optimized` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_fixed_struct_element_optimized` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_dynamic_struct_element_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_dynamic_struct_element_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_dynamic_struct_element_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_struct_stride_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_struct_stride_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_struct_stride_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_mapped_nested_alignment_ir` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_mapped_nested_alignment_ir_optimized` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_mapped_nested_alignment_optimized` | {"returned": "0x1234560000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_array_mapping_struct_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_array_mapping_struct_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_array_mapping_struct_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_struct_container_fields_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_struct_container_fields_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_struct_container_fields_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_member_lengths_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_storage_structs_member_lengths_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_storage_structs_member_lengths_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_storage_structs_captured_indices_once_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_captured_indices_once_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_captured_indices_once_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_storage_structs_rhs_before_member_base_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_storage_structs_rhs_before_member_base_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_storage_structs_rhs_before_member_base_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000002"} |
| `yul_storage_structs_internal_visibility_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_storage_structs_internal_visibility_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_storage_structs_internal_visibility_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_storage_structs_overflow_rollback_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_structs_overflow_rollback_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_structs_overflow_rollback_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_structs_fixed_bounds_rollback_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_fixed_bounds_rollback_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_fixed_bounds_rollback_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_dynamic_bounds_rollback_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_dynamic_bounds_rollback_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_dynamic_bounds_rollback_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_dynamic_empty_rollback_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_dynamic_empty_rollback_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_dynamic_empty_rollback_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_length_is_a_declared_field_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_length_is_a_declared_field_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_length_is_a_declared_field_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_storage_structs_container_scalar_push_pop_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_container_scalar_push_pop_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_container_scalar_push_pop_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_storage_structs_top_level_file_scope_escaped_name_and_unused_declarations_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_storage_structs_top_level_file_scope_escaped_name_and_unused_declarations_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_storage_structs_top_level_file_scope_escaped_name_and_unused_declarations_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_storage_structs_top_level_field_overflow_rollback_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_structs_top_level_field_overflow_rollback_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_structs_top_level_field_overflow_rollback_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_storage_structs_top_level_field_bounds_rollback_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_top_level_field_bounds_rollback_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_storage_structs_top_level_field_bounds_rollback_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"} |
| `yul_token_mint_logs_transfer_ir` | {"returned": "0x"} |
| `yul_token_mint_logs_transfer_ir_optimized` | {"returned": "0x"} |
| `yul_token_mint_logs_transfer_optimized` | {"returned": "0x"} |
| `yul_token_mint_to_zero_reverts_ir` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"} |
| `yul_token_mint_to_zero_reverts_ir_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"} |
| `yul_token_mint_to_zero_reverts_optimized` | {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"} |
| `yul_token_transfer_moves_balance_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_moves_balance_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_moves_balance_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_from_other_sender_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_from_other_sender_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_from_other_sender_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_insufficient_reverts_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"} |
| `yul_token_transfer_insufficient_reverts_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"} |
| `yul_token_transfer_insufficient_reverts_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"} |
| `yul_token_transfer_to_zero_reverts_ir` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000107472616e7366657220746f207a65726f00000000000000000000000000000000"} |
| `yul_token_transfer_to_zero_reverts_ir_optimized` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000107472616e7366657220746f207a65726f00000000000000000000000000000000"} |
| `yul_token_transfer_to_zero_reverts_optimized` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000107472616e7366657220746f207a65726f00000000000000000000000000000000"} |
| `yul_token_approve_logs_approval_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_approve_logs_approval_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_approve_logs_approval_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_from_spends_allowance_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_from_spends_allowance_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_from_spends_allowance_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000001"} |
| `yul_token_transfer_from_over_allowance_reverts_ir` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000016696e73756666696369656e7420616c6c6f77616e636500000000000000000000"} |
| `yul_token_transfer_from_over_allowance_reverts_ir_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000016696e73756666696369656e7420616c6c6f77616e636500000000000000000000"} |
| `yul_token_transfer_from_over_allowance_reverts_optimized` | {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000016696e73756666696369656e7420616c6c6f77616e636500000000000000000000"} |
| `yul_token_balance_of_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_token_balance_of_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_token_balance_of_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_token_allowance_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_token_allowance_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_token_allowance_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_token_nonpayable_with_value_reverts_ir` | {"reverted": "0x"} |
| `yul_token_nonpayable_with_value_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_token_nonpayable_with_value_reverts_optimized` | {"reverted": "0x"} |
| `yul_token_unknown_selector_reverts_ir` | {"reverted": "0x"} |
| `yul_token_unknown_selector_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_token_unknown_selector_reverts_optimized` | {"reverted": "0x"} |
| `yul_token_empty_calldata_reverts_ir` | {"reverted": "0x"} |
| `yul_token_empty_calldata_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_token_empty_calldata_reverts_optimized` | {"reverted": "0x"} |
| `yul_token_short_calldata_reverts_ir` | {"reverted": "0x"} |
| `yul_token_short_calldata_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_token_short_calldata_reverts_optimized` | {"reverted": "0x"} |
| `yul_token_dirty_address_reverts_ir` | {"reverted": "0x"} |
| `yul_token_dirty_address_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_token_dirty_address_reverts_optimized` | {"reverted": "0x"} |
| `yul_context_receive_with_value_ir` | {"returned": "0x"} |
| `yul_context_receive_with_value_ir_optimized` | {"returned": "0x"} |
| `yul_context_receive_with_value_optimized` | {"returned": "0x"} |
| `yul_context_receive_without_value_ir` | {"returned": "0x"} |
| `yul_context_receive_without_value_ir_optimized` | {"returned": "0x"} |
| `yul_context_receive_without_value_optimized` | {"returned": "0x"} |
| `yul_context_fallback_logs_anonymous_ir` | {"returned": "0x"} |
| `yul_context_fallback_logs_anonymous_ir_optimized` | {"returned": "0x"} |
| `yul_context_fallback_logs_anonymous_optimized` | {"returned": "0x"} |
| `yul_context_fallback_on_short_calldata_ir` | {"returned": "0x"} |
| `yul_context_fallback_on_short_calldata_ir_optimized` | {"returned": "0x"} |
| `yul_context_fallback_on_short_calldata_optimized` | {"returned": "0x"} |
| `yul_context_deposit_payable_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_context_deposit_payable_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_context_deposit_payable_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000008"} |
| `yul_context_self_address_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001000"} |
| `yul_context_self_address_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001000"} |
| `yul_context_self_address_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000001000"} |
| `yul_context_sender_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000004000"} |
| `yul_context_sender_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000004000"} |
| `yul_context_sender_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000004000"} |
| `yul_context_origin_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000004000"} |
| `yul_context_origin_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000004000"} |
| `yul_context_origin_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000004000"} |
| `yul_context_block_info_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000006553f10000000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000c0ffee"} |
| `yul_context_block_info_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000006553f10000000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000c0ffee"} |
| `yul_context_block_info_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000006553f10000000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000c0ffee"} |
| `yul_context_fee_info_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000001c9c380"} |
| `yul_context_fee_info_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000001c9c380"} |
| `yul_context_fee_info_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000001c9c380"} |
| `yul_context_typed_topics_ir` | {"returned": "0x"} |
| `yul_context_typed_topics_ir_optimized` | {"returned": "0x"} |
| `yul_context_typed_topics_optimized` | {"returned": "0x"} |
| `yul_context_four_topics_anonymous_ir` | {"returned": "0x"} |
| `yul_context_four_topics_anonymous_ir_optimized` | {"returned": "0x"} |
| `yul_context_four_topics_anonymous_optimized` | {"returned": "0x"} |
| `yul_context_emit_then_succeed_ir` | {"returned": "0x"} |
| `yul_context_emit_then_succeed_ir_optimized` | {"returned": "0x"} |
| `yul_context_emit_then_succeed_optimized` | {"returned": "0x"} |
| `yul_context_revert_discards_logs_ir` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000076e6f6e7a65726f00000000000000000000000000000000000000000000000000"} |
| `yul_context_revert_discards_logs_ir_optimized` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000076e6f6e7a65726f00000000000000000000000000000000000000000000000000"} |
| `yul_context_revert_discards_logs_optimized` | {"reverted": "0x08c379a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000076e6f6e7a65726f00000000000000000000000000000000000000000000000000"} |
| `yul_context_view_with_value_reverts_ir` | {"reverted": "0x"} |
| `yul_context_view_with_value_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_context_view_with_value_reverts_optimized` | {"reverted": "0x"} |
| `yul_context_note_logs_indexed_tag_ir` | {"returned": "0x"} |
| `yul_context_note_logs_indexed_tag_ir_optimized` | {"returned": "0x"} |
| `yul_context_note_logs_indexed_tag_optimized` | {"returned": "0x"} |
| `yul_context_narrow_round_trip_ir` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeabcd0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_context_narrow_round_trip_ir_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeabcd0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_context_narrow_round_trip_optimized` | {"returned": "0x00000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeabcd0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"} |
| `yul_context_trailing_calldata_ignored_ir` | {"returned": "0x"} |
| `yul_context_trailing_calldata_ignored_ir_optimized` | {"returned": "0x"} |
| `yul_context_trailing_calldata_ignored_optimized` | {"returned": "0x"} |
| `yul_context_narrow_dirty_uint8_reverts_ir` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_uint8_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_uint8_reverts_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_int16_reverts_ir` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_int16_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_int16_reverts_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_bytes2_reverts_ir` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_bytes2_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_bytes2_reverts_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_bool_reverts_ir` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_bool_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_dirty_bool_reverts_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_short_calldata_reverts_ir` | {"reverted": "0x"} |
| `yul_context_narrow_short_calldata_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_context_narrow_short_calldata_reverts_optimized` | {"reverted": "0x"} |
| `yul_fallback_empty_calldata_runs_fallback_ir` | {"returned": "0x"} |
| `yul_fallback_empty_calldata_runs_fallback_ir_optimized` | {"returned": "0x"} |
| `yul_fallback_empty_calldata_runs_fallback_optimized` | {"returned": "0x"} |
| `yul_fallback_selector_runs_fallback_ir` | {"returned": "0x"} |
| `yul_fallback_selector_runs_fallback_ir_optimized` | {"returned": "0x"} |
| `yul_fallback_selector_runs_fallback_optimized` | {"returned": "0x"} |
| `yul_fallback_value_reverts_ir` | {"reverted": "0x"} |
| `yul_fallback_value_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_fallback_value_reverts_optimized` | {"reverted": "0x"} |
| `yul_receive_empty_calldata_runs_receive_ir` | {"returned": "0x"} |
| `yul_receive_empty_calldata_runs_receive_ir_optimized` | {"returned": "0x"} |
| `yul_receive_empty_calldata_runs_receive_optimized` | {"returned": "0x"} |
| `yul_receive_short_calldata_reverts_ir` | {"reverted": "0x"} |
| `yul_receive_short_calldata_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_receive_short_calldata_reverts_optimized` | {"reverted": "0x"} |
| `yul_receive_selector_reverts_ir` | {"reverted": "0x"} |
| `yul_receive_selector_reverts_ir_optimized` | {"reverted": "0x"} |
| `yul_receive_selector_reverts_optimized` | {"reverted": "0x"} |
| `yul_inheritance_base_calls_run_overrides_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_inheritance_base_calls_run_overrides_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_inheritance_base_calls_run_overrides_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000006"} |
| `yul_inheritance_inherited_state_accumulates_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"} |
| `yul_inheritance_inherited_state_accumulates_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"} |
| `yul_inheritance_inherited_state_accumulates_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"} |
| `yul_inheritance_base_update_overflow_panics_ir` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_inheritance_base_update_overflow_panics_ir_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_inheritance_base_update_overflow_panics_optimized` | {"reverted": "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"} |
| `yul_inheritance_dispatch_reaches_override_ir` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_inheritance_dispatch_reaches_override_ir_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_inheritance_dispatch_reaches_override_optimized` | {"returned": "0x000000000000000000000000000000000000000000000000000000000000000c"} |
| `yul_inheritance_diamond_base_call_reaches_diamond_override_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_inheritance_diamond_base_call_reaches_diamond_override_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_inheritance_diamond_base_call_reaches_diamond_override_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000004"} |
| `yul_inheritance_diamond_diamond_override_reads_state_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_inheritance_diamond_diamond_override_reads_state_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_inheritance_diamond_diamond_override_reads_state_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"} |
| `yul_inheritance_diamond_fallback_override_runs_ir` | {"returned": "0x"} |
| `yul_inheritance_diamond_fallback_override_runs_ir_optimized` | {"returned": "0x"} |
| `yul_inheritance_diamond_fallback_override_runs_optimized` | {"returned": "0x"} |
| `yul_inheritance_diamond_call_reaches_implementation_through_redeclaration_ir` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_inheritance_diamond_call_reaches_implementation_through_redeclaration_ir_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |
| `yul_inheritance_diamond_call_reaches_implementation_through_redeclaration_optimized` | {"returned": "0x0000000000000000000000000000000000000000000000000000000000000007"} |

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
| yul-artifacts-staged | `tests/yulDifferentialCorpusScript.sml` | pass |

## What is not an agreement

Each case's status is one of agree, mismatch, unexpected, storage-mismatch, storage-unexpected, log-mismatch, log-unexpected, inconclusive or error; only agree is an agreement, and the rest are listed here with the status that classifies them. An inconclusive is a diagnostic on one side, not a disagreement. A case at a stage the importer did not admit is not a disagreement either: it is counted above as an admission. Failures of another kind -- a suite that would not prepare, an external check, the HOL build -- are listed here too.

- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"}, "case": "pay_transfers_then_reads_balance", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_transfers_then_reads_balance_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"}, "case": "pay_transfers_then_reads_balance", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_transfers_then_reads_balance_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"}, "case": "pay_transfers_then_reads_balance", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000014"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_transfers_then_reads_balance_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"}, "case": "pay_bubbles_callee_revert", "expected": {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_bubbles_callee_revert_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"}, "case": "pay_bubbles_callee_revert", "expected": {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_bubbles_callee_revert_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"}, "case": "pay_bubbles_callee_revert", "expected": {"reverted": "0x08c379a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000014696e73756666696369656e742062616c616e6365000000000000000000000000"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_bubbles_callee_revert_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "pay_without_code_fails_decoding", "expected": {"reverted": "0x"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_without_code_fails_decoding_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "pay_without_code_fails_decoding", "expected": {"reverted": "0x"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_without_code_fails_decoding_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "pay_without_code_fails_decoding", "expected": {"reverted": "0x"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_pay_without_code_fails_decoding_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x"}, "case": "mint_via_calls_token", "expected": {"returned": "0x"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_calls_token_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x"}, "case": "mint_via_calls_token", "expected": {"returned": "0x"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_calls_token_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x"}, "case": "mint_via_calls_token", "expected": {"returned": "0x"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_calls_token_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"}, "case": "mint_via_bubbles_callee_revert", "expected": {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_bubbles_callee_revert_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"}, "case": "mint_via_bubbles_callee_revert", "expected": {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_bubbles_callee_revert_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"}, "case": "mint_via_bubbles_callee_revert", "expected": {"reverted": "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c6d696e7420746f207a65726f0000000000000000000000000000000000000000"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_bubbles_callee_revert_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "mint_via_without_code_reverts", "expected": {"reverted": "0x"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_without_code_reverts_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "mint_via_without_code_reverts", "expected": {"reverted": "0x"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_without_code_reverts_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "mint_via_without_code_reverts", "expected": {"reverted": "0x"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_mint_via_without_code_reverts_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"}, "case": "balance_via_static_call", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_balance_via_static_call_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"}, "case": "balance_via_static_call", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_balance_via_static_call_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"}, "case": "balance_via_static_call", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000009"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_balance_via_static_call_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e"}, "case": "bump_self_sees_callee_write", "expected": {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_bump_self_sees_callee_write_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e"}, "case": "bump_self_sees_callee_write", "expected": {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_bump_self_sees_callee_write_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e"}, "case": "bump_self_sees_callee_write", "expected": {"returned": "0x000000000000000000000000000000000000000000000000000000000000000e"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_bump_self_sees_callee_write_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "bump_static_halts_on_write", "expected": {"reverted": "0x"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_bump_static_halts_on_write_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "bump_static_halts_on_write", "expected": {"reverted": "0x"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_bump_static_halts_on_write_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "bump_static_halts_on_write", "expected": {"reverted": "0x"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_bump_static_halts_on_write_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"}, "case": "forward_passes_value", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_forward_passes_value_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"}, "case": "forward_passes_value", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_forward_passes_value_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"}, "case": "forward_passes_value", "expected": {"returned": "0x0000000000000000000000000000000000000000000000000000000000000003"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_forward_passes_value_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "forward_without_balance_reverts", "expected": {"reverted": "0x"}, "kind": "case", "stage": "ir", "status": "inconclusive", "suite": "external", "theorem": "yul_external_forward_without_balance_reverts_ir", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "forward_without_balance_reverts", "expected": {"reverted": "0x"}, "kind": "case", "stage": "ir-optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_forward_without_balance_reverts_ir_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
- {"bytecode": {"reverted": "0x"}, "case": "forward_without_balance_reverts", "expected": {"reverted": "0x"}, "kind": "case", "stage": "optimized", "status": "inconclusive", "suite": "external", "theorem": "yul_external_forward_without_balance_reverts_optimized", "yul": {"diagnostic": "InvalidCompletion"}}
