import Pgx.Typed.Descriptors

/-!
Deterministic paired benchmark for generated prepared-parameter encoders.

The legacy side mirrors generated code that first wraps every built-in value
in `EncodedValue`; the direct side constructs the final value and format arrays
without those intermediate records.  Five cases match the parameter shapes in
the Acme Widgets application.  Semantic controls compare the complete encoded
results before the selected path is repeated for instruction/branch counters.
-/

open Pgx.Typed

private structure Params where
  widgetId : Int64
  ownerId : Int64
  pageSize : Int64
  name : String
  sku : String
  quantity : Int64
  description : String
  deriving Inhabited

private inductive Shape where
  | getWidget
  | listWidgets
  | insertWidget
  | updateWidget
  | deleteWidget
  deriving BEq

private def legacyGetWidget (params : Params) : Except Error EncodedParams := do
  let encoded0 ← encodePlannedBuiltin (Pg.binaryInt64 params.widgetId)
  pure {
    values := #[encoded0.value]
    formats := #[encoded0.format]
  }

private def directGetWidget (params : Params) : Except Error EncodedParams :=
  pure {
    values := #[Pg.PgEncode.encode (Pg.binaryInt64 params.widgetId)]
    formats := #[plannedBuiltinFormat (Pg.binaryInt64 params.widgetId)]
  }

private def legacyListWidgets (params : Params) : Except Error EncodedParams := do
  let encoded0 ← encodePlannedBuiltin (Pg.binaryInt64 params.ownerId)
  let encoded1 ← encodePlannedBuiltin (Pg.binaryInt64 params.pageSize)
  pure {
    values := #[encoded0.value, encoded1.value]
    formats := #[encoded0.format, encoded1.format]
  }

private def directListWidgets (params : Params) : Except Error EncodedParams :=
  pure {
    values := #[
      Pg.PgEncode.encode (Pg.binaryInt64 params.ownerId),
      Pg.PgEncode.encode (Pg.binaryInt64 params.pageSize)
    ]
    formats := #[
      plannedBuiltinFormat (Pg.binaryInt64 params.ownerId),
      plannedBuiltinFormat (Pg.binaryInt64 params.pageSize)
    ]
  }

@[noinline, export pgx_benchmark_prepared_legacy_insert]
private def legacyInsertWidget (params : Params) : Except Error EncodedParams := do
  let encoded0 ← encodePlannedBuiltin (Pg.binaryInt64 params.ownerId)
  let encoded1 ← encodePlannedBuiltin params.name
  let encoded2 ← encodePlannedBuiltin params.sku
  let encoded3 ← encodePlannedBuiltin (Pg.binaryInt64 params.quantity)
  let encoded4 ← encodePlannedBuiltin params.description
  pure {
    values := #[encoded0.value, encoded1.value, encoded2.value, encoded3.value,
      encoded4.value]
    formats := #[encoded0.format, encoded1.format, encoded2.format,
      encoded3.format, encoded4.format]
  }

@[noinline, export pgx_benchmark_prepared_direct_insert]
private def directInsertWidget (params : Params) : Except Error EncodedParams :=
  pure {
    values := #[
      Pg.PgEncode.encode (Pg.binaryInt64 params.ownerId),
      Pg.PgEncode.encode params.name,
      Pg.PgEncode.encode params.sku,
      Pg.PgEncode.encode (Pg.binaryInt64 params.quantity),
      Pg.PgEncode.encode params.description
    ]
    formats := #[
      plannedBuiltinFormat (Pg.binaryInt64 params.ownerId),
      plannedBuiltinFormat params.name,
      plannedBuiltinFormat params.sku,
      plannedBuiltinFormat (Pg.binaryInt64 params.quantity),
      plannedBuiltinFormat params.description
    ]
  }

private def legacyUpdateWidget (params : Params) : Except Error EncodedParams := do
  let encoded0 ← encodePlannedBuiltin (Pg.binaryInt64 params.widgetId)
  let encoded1 ← encodePlannedBuiltin (Pg.binaryInt64 params.ownerId)
  let encoded2 ← encodePlannedBuiltin params.name
  let encoded3 ← encodePlannedBuiltin params.sku
  let encoded4 ← encodePlannedBuiltin (Pg.binaryInt64 params.quantity)
  let encoded5 ← encodePlannedBuiltin params.description
  pure {
    values := #[encoded0.value, encoded1.value, encoded2.value, encoded3.value,
      encoded4.value, encoded5.value]
    formats := #[encoded0.format, encoded1.format, encoded2.format,
      encoded3.format, encoded4.format, encoded5.format]
  }

private def directUpdateWidget (params : Params) : Except Error EncodedParams :=
  pure {
    values := #[
      Pg.PgEncode.encode (Pg.binaryInt64 params.widgetId),
      Pg.PgEncode.encode (Pg.binaryInt64 params.ownerId),
      Pg.PgEncode.encode params.name,
      Pg.PgEncode.encode params.sku,
      Pg.PgEncode.encode (Pg.binaryInt64 params.quantity),
      Pg.PgEncode.encode params.description
    ]
    formats := #[
      plannedBuiltinFormat (Pg.binaryInt64 params.widgetId),
      plannedBuiltinFormat (Pg.binaryInt64 params.ownerId),
      plannedBuiltinFormat params.name,
      plannedBuiltinFormat params.sku,
      plannedBuiltinFormat (Pg.binaryInt64 params.quantity),
      plannedBuiltinFormat params.description
    ]
  }

private def legacyDeleteWidget (params : Params) : Except Error EncodedParams := do
  let encoded0 ← encodePlannedBuiltin (Pg.binaryInt64 params.widgetId)
  let encoded1 ← encodePlannedBuiltin (Pg.binaryInt64 params.ownerId)
  pure {
    values := #[encoded0.value, encoded1.value]
    formats := #[encoded0.format, encoded1.format]
  }

private def directDeleteWidget (params : Params) : Except Error EncodedParams :=
  pure {
    values := #[
      Pg.PgEncode.encode (Pg.binaryInt64 params.widgetId),
      Pg.PgEncode.encode (Pg.binaryInt64 params.ownerId)
    ]
    formats := #[
      plannedBuiltinFormat (Pg.binaryInt64 params.widgetId),
      plannedBuiltinFormat (Pg.binaryInt64 params.ownerId)
    ]
  }

private def encodeLegacy : Shape → Params → Except Error EncodedParams
  | .getWidget => legacyGetWidget
  | .listWidgets => legacyListWidgets
  | .insertWidget => legacyInsertWidget
  | .updateWidget => legacyUpdateWidget
  | .deleteWidget => legacyDeleteWidget

private def encodeDirect : Shape → Params → Except Error EncodedParams
  | .getWidget => directGetWidget
  | .listWidgets => directListWidgets
  | .insertWidget => directInsertWidget
  | .updateWidget => directUpdateWidget
  | .deleteWidget => directDeleteWidget

private def shapeName : Shape → String
  | .getWidget => "get"
  | .listWidgets => "list"
  | .insertWidget => "insert"
  | .updateWidget => "update"
  | .deleteWidget => "delete"

private def allShapes : Array Shape := #[
  .getWidget, .listWidgets, .insertWidget, .updateWidget, .deleteWidget
]

private def fixtures : Array Params := #[
  {
    widgetId := 123456789
    ownerId := 7
    pageSize := 55
    name := "widget-name"
    sku := "SKU-12345"
    quantity := 42
    description := "representative widget description"
  },
  {
    widgetId := -9223372036854775807
    ownerId := 9223372036854775807
    pageSize := 1
    name := ""
    sku := "nul\u0000sku"
    quantity := -1
    description := "café 한국어 🚀"
  }
]

private def semanticControls : IO Unit := do
  for params in fixtures do
    for shape in allShapes do
      let legacy := encodeLegacy shape params
      let direct := encodeDirect shape params
      match legacy, direct with
      | .ok legacy, .ok direct =>
          unless legacy == direct do
            throw (IO.userError s!"{shapeName shape} prepared encoders differ")
      | .error error, _ | _, .error error =>
          throw (IO.userError s!"{shapeName shape} encoder failed: {error.toMessage}")

private def checksum (encoded : @& EncodedParams) : Nat :=
  let valueBytes := encoded.values.foldl (fun total value =>
    total + (value.map fun bytes =>
      bytes.foldl (fun n byte => n + byte.toNat) 0).getD 17) 0
  encoded.formats.foldl (fun total format => total + format.toNat) valueBytes

private def run (encode : Params → Except Error EncodedParams)
    (params : @& Params) (iterations : Nat) : IO Nat := do
  let mut total := 0
  for _ in [0:iterations] do
    match encode params with
    | .ok encoded => total := total + checksum encoded
    | .error error => throw (IO.userError error.toMessage)
  pure total

private def parseShape : String → Option Shape
  | "get" => some .getWidget
  | "list" => some .listWidgets
  | "insert" => some .insertWidget
  | "update" => some .updateWidget
  | "delete" => some .deleteWidget
  | _ => none

def main (args : List String) : IO Unit := do
  semanticControls
  let mode := args.head?.getD "direct"
  let shapeText := (args.drop 1).head?.getD "insert"
  let some shape := parseShape shapeText
    | throw (IO.userError s!"unknown prepared-encoder shape: {shapeText}")
  let iterations := ((args.drop 2).head? >>= String.toNat?).getD 100000
  let params := fixtures[0]!
  let encode ← if mode == "legacy" then
      pure (encodeLegacy shape)
    else if mode == "direct" then
      pure (encodeDirect shape)
    else
      throw (IO.userError s!"unknown prepared-encoder mode: {mode}")
  let result ← run encode params iterations
  IO.println s!"mode={mode} shape={shapeText} iterations={iterations} checksum={result}"
