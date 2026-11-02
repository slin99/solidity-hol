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
  solidityEVMCallTest solidityEVMCreateTest solidityEVMFrameTest
  solidityEVMReentryTest solidityEVMBookkeepingTest
  externalCall solidityEvaluator solidityABI solidityEntry solidityEvaluatorProps solidityEvaluatorTest
  solidityCoreProgramsTest solidityImport solidityImportTest
  solidityElaborate solidityElaborateTest solidityPrepareTest solidityDifferential
  solidityDifferentialCorpus solidityDifferentialTest
  yulAST yulDialect yulState yulEvaluator yulEvaluatorProps yulEvaluatorTest
  yulImportTest yulDifferential
  verifereum
