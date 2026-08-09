import Pgx.Typed.Composite

open Pgx.Typed

private def isError (result : Except String α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def okEq [BEq α] (result : Except String α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def syntaxTests : IO Unit := do
  assert! okEq (parseCompositeText "()") #[none]
  assert! okEq (parseCompositeText "(,)") #[none, none]
  assert! okEq (parseCompositeText "(alpha,,omega)")
    #[some "alpha", none, some "omega"]
  assert! okEq (parseCompositeText "(NULL,\"\")") #[some "NULL", some ""]
  assert! okEq (parseCompositeText "  (alpha,beta)\t")
    #[some "alpha", some "beta"]
  assert! okEq (parseCompositeTextArity 0 "()") #[]
  assert! okEq (parseCompositeTextArity 1 "()") #[none]
  assert! isError (parseCompositeTextArity 2 "()")
  assert! isError (parseCompositeTextArity 2 "(only_one)")

  -- PostgreSQL accepts backslash escapes in both quoted and unquoted fields.
  assert! okEq (parseCompositeText "(a\\,b,c\\)d,e\\\\f)")
    #[some "a,b", some "c)d", some "e\\f"]
  assert! okEq (parseCompositeText "(\"a,b\",\"c)d\",\"e\\\\f\")")
    #[some "a,b", some "c)d", some "e\\f"]

  -- A quote can be escaped by a backslash or by PostgreSQL's doubled form.
  assert! okEq (parseCompositeText "(\"a\\\"b\",\"c\"\"d\")")
    #[some "a\"b", some "c\"d"]
  assert! okEq (parseCompositeText "(\" spaced \"   , unquoted )")
    #[some " spaced    ", some " unquoted "]
  -- Quoted and unquoted fragments concatenate, as in PostgreSQL record_in.
  assert! okEq (parseCompositeText "(\"a\"b,a\"b\",a(b)")
    #[some "ab", some "ab", some "a(b"]

private def roundTripTests : IO Unit := do
  let adversarial : CompositeTextFields := #[
    none,
    some "",
    some "NULL",
    some "plain",
    some " leading and trailing ",
    some "comma,paren()",
    some "quote\"and\\backslash",
    some "line one\nline two\t",
    some "héλλο 🚀 東京"
  ]
  let rendered := renderCompositeText adversarial
  assert! okEq (parseCompositeText rendered) adversarial
  assert! rendered.startsWith "(,\"\",\"NULL\""

  let nulls : CompositeTextFields := #[none, none, none]
  assert! renderCompositeText nulls == "(,,)"
  assert! okEq (parseCompositeText (renderCompositeText nulls)) nulls

  let empty : CompositeTextFields := #[]
  assert! renderCompositeText empty == "()"
  assert! okEq (parseCompositeTextArity 0 (renderCompositeText empty)) empty

private def malformedTests : IO Unit := do
  assert! isError (parseCompositeText "")
  assert! isError (parseCompositeText "alpha")
  assert! isError (parseCompositeText "(alpha")
  assert! isError (parseCompositeText "alpha)")
  assert! isError (parseCompositeText "(alpha))")
  assert! isError (parseCompositeText "(alpha) trailing")
  assert! isError (parseCompositeText "((nested))")
  assert! isError (parseCompositeText "(a\"b)")
  assert! isError (parseCompositeText "(\"unterminated)")
  assert! isError (parseCompositeText "(dangling\\)")
  assert! isError (parseCompositeText "(\"dangling\\")

def main : IO UInt32 := do
  syntaxTests
  roundTripTests
  malformedTests
  return 0
