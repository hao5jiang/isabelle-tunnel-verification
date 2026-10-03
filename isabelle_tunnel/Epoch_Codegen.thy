theory Epoch_Codegen
  imports Encoded_Activation "HOL-Library.Code_Target_Nat"
begin

text \<open>Generate the checked field functions directly from their existing
  logical definitions. The standard target-natural-number implementation uses
  unbounded target integers rather than unary constructors or machine words.
  The exported conversion from integer to natural truncates negative integers
  to zero; external input must reject negative values before calling it.
  The command-line wrapper and execution tests are separate from the proof.
  Compiler, runtime, input/output, and code generator remain trusted components.\<close>

export_code epoch_encode epoch_decode epoch_checked_successor
  nat_of_integer integer_of_nat
  in SML module_name EpochCodec file_prefix EpochCodec

end
