(*
 * Project build roll-up.
 *
 * Project theories should be added as ancestors here as they are introduced so
 * that building solidityHolTheory builds the complete development.
 *)
Theory solidityHol
Ancestors
  solidityAST solidityCore solidityCoreWf solidityScalar solidityState
  solidityEVMCall solidityScalarTest
  solidityEVMBoundaryProps solidityCoreWfTest
  solidityEVMCallTest solidityEVMCreateTest solidityCreateCallTest solidityEVMFrameTest
  solidityEVMReentryTest solidityEVMBookkeepingTest
  externalCall solidityMemory solidityEvaluator solidityABI solidityEntry solidityEvaluatorProps solidityEvaluatorTest
  solidityCoreProgramsTest solidityImport solidityImportTest
  solidityElaborate solidityElaborateTest solidityPrepareTest solidityPartialTest
  solidityDifferential solidityDifferentialCorpus_zero_reset
  solidityDifferentialCorpus solidityDifferentialTest solidityDirtyBitsTest
  yulAST yulDialect yulState yulEvaluator yulEvaluatorProps yulEvaluatorTest
  yulImportTest yulContractTest yulConvTest yulDifferential yulDifferentialTest
  verifereum
