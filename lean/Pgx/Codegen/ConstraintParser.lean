import Pgx.Constraint.IR
import Pgx.IR

/-!
# Parser for normalized PostgreSQL check definitions

The probe feeds this parser `pg_get_constraintdef(..., true)` output.  It is a
strict parser for the local, deterministic subset used by generated Lean
predicates; accepting a construct here is a commitment to model its semantics.
-/

namespace Pgx.Codegen.ConstraintParser

open Pgx.Constraint

private inductive TokenKind where
  | word (value : String) (quoted : Bool)
  | string (value : String)
  | number (value : String)
  | lparen | rparen | comma | dot | cast
  | plus | minus
  | eq | ne | lt | le | gt | ge
  | operator (value : String)
  deriving Repr, BEq

private structure Token where
  kind : TokenKind
  start : Nat
  stop : Nat
  deriving Repr, BEq

private def diagnostic (category : DiagnosticCategory) (offset : Nat)
    (message : String) : Diagnostic := { category, offset, message }

private def isIdentStart (char : Char) : Bool :=
  char.isAlpha || char == '_'

private def isIdentRest (char : Char) : Bool :=
  char.isAlphanum || char == '_' || char == '$'

private def charsToString (chars : Array Char) (start stop : Nat) : String :=
  String.ofList (chars.toList.drop start |>.take (stop - start))

private def scanWhile (chars : Array Char) (start : Nat) (predicate : Char → Bool) : Nat := Id.run do
  let mut index := start
  while index < chars.size && predicate chars[index]! do
    index := index + 1
  return index

private def lexQuotedIdentifier (chars : Array Char) (start : Nat) :
    Except Diagnostic (String × Nat) := do
  let mut index := start + 1
  let mut value : Array Char := #[]
  while index < chars.size do
    let char := chars[index]!
    if char == '"' then
      if index + 1 < chars.size && chars[index + 1]! == '"' then
        value := value.push '"'
        index := index + 2
      else
        return (String.ofList value.toList, index + 1)
    else
      value := value.push char
      index := index + 1
  throw (diagnostic .syntax start "unterminated quoted identifier")

private def lexString (chars : Array Char) (start : Nat) :
    Except Diagnostic (String × Nat) := do
  let mut index := start + 1
  let mut value : Array Char := #[]
  while index < chars.size do
    let char := chars[index]!
    if char == '\'' then
      if index + 1 < chars.size && chars[index + 1]! == '\'' then
        value := value.push '\''
        index := index + 2
      else
        return (String.ofList value.toList, index + 1)
    else
      value := value.push char
      index := index + 1
  throw (diagnostic .syntax start "unterminated string literal")

private def lexNumber (chars : Array Char) (start : Nat) : Nat := Id.run do
  let mut index := scanWhile chars start Char.isDigit
  if index < chars.size && chars[index]! == '.' &&
      index + 1 < chars.size && chars[index + 1]!.isDigit then
    index := scanWhile chars (index + 1) Char.isDigit
  if index < chars.size && (chars[index]! == 'e' || chars[index]! == 'E') then
    let exponent := index
    index := index + 1
    if index < chars.size && (chars[index]! == '+' || chars[index]! == '-') then
      index := index + 1
    let digits := scanWhile chars index Char.isDigit
    if digits == index then
      return exponent
    index := digits
  return index

private def tokenize (source : String) : Except Diagnostic (Array Token) := do
  let chars := source.toList.toArray
  let mut result : Array Token := #[]
  let mut index := 0
  while index < chars.size do
    let char := chars[index]!
    if char.isWhitespace then
      index := index + 1
    else if isIdentStart char then
      let stop := scanWhile chars (index + 1) isIdentRest
      let value := (charsToString chars index stop).toLower
      result := result.push { kind := .word value false, start := index, stop }
      index := stop
    else if char == '"' then
      let (value, stop) ← lexQuotedIdentifier chars index
      result := result.push { kind := .word value true, start := index, stop }
      index := stop
    else if char == '\'' then
      let (value, stop) ← lexString chars index
      result := result.push { kind := .string value, start := index, stop }
      index := stop
    else if char.isDigit then
      let stop := lexNumber chars index
      result := result.push {
        kind := .number (charsToString chars index stop), start := index, stop
      }
      index := stop
    else
      let next? := chars[index + 1]?
      match char, next? with
      | ':', some ':' =>
          result := result.push { kind := .cast, start := index, stop := index + 2 }
          index := index + 2
      | '<', some '=' =>
          result := result.push { kind := .le, start := index, stop := index + 2 }
          index := index + 2
      | '>', some '=' =>
          result := result.push { kind := .ge, start := index, stop := index + 2 }
          index := index + 2
      | '<', some '>' | '!', some '=' =>
          result := result.push { kind := .ne, start := index, stop := index + 2 }
          index := index + 2
      | '|', some '|' =>
          result := result.push {
            kind := .operator "||", start := index, stop := index + 2
          }
          index := index + 2
      | '&', some '&' =>
          result := result.push {
            kind := .operator "&&", start := index, stop := index + 2
          }
          index := index + 2
      | '-', some '-' =>
          throw (diagnostic .syntax index
            "comments are not part of normalized constraint definitions")
      | '/', some '*' =>
          throw (diagnostic .syntax index
            "comments are not part of normalized constraint definitions")
      | '(', _ =>
          result := result.push { kind := .lparen, start := index, stop := index + 1 }
          index := index + 1
      | ')', _ =>
          result := result.push { kind := .rparen, start := index, stop := index + 1 }
          index := index + 1
      | ',', _ =>
          result := result.push { kind := .comma, start := index, stop := index + 1 }
          index := index + 1
      | '.', _ =>
          result := result.push { kind := .dot, start := index, stop := index + 1 }
          index := index + 1
      | '+', _ =>
          result := result.push { kind := .plus, start := index, stop := index + 1 }
          index := index + 1
      | '-', _ =>
          result := result.push { kind := .minus, start := index, stop := index + 1 }
          index := index + 1
      | '=', _ =>
          result := result.push { kind := .eq, start := index, stop := index + 1 }
          index := index + 1
      | '<', _ =>
          result := result.push { kind := .lt, start := index, stop := index + 1 }
          index := index + 1
      | '>', _ =>
          result := result.push { kind := .gt, start := index, stop := index + 1 }
          index := index + 1
      | '*', _ | '/', _ | '%', _ | '~', _ | '!', _ | '|', _ | '&', _ | '^', _ =>
          result := result.push {
            kind := .operator (String.singleton char), start := index, stop := index + 1
          }
          index := index + 1
      | _, _ => throw (diagnostic .syntax index s!"unexpected character {repr char}")
  pure result

private inductive RawUnary where
  | plus | minus | not
  deriving Repr, BEq

private inductive RawBinary where
  | add | sub
  | eq | ne | lt | le | gt | ge
  | and | or
  deriving Repr, BEq

private structure TypeSyntax where
  offset : Nat
  parts : Array String
  modifiers : Array String := #[]
  deriving Repr, BEq

private inductive RawExpr where
  | identifier (offset : Nat) (parts : Array String)
  | string (offset : Nat) (value : String)
  | number (offset : Nat) (value : String)
  | null (offset : Nat)
  | boolean (offset : Nat) (value : Bool)
  | call (offset : Nat) (name : Array String) (arguments : Array RawExpr)
  | cast (offset : Nat) (value : RawExpr) (target : TypeSyntax)
  | unary (offset : Nat) (op : RawUnary) (value : RawExpr)
  | binary (offset : Nat) (op : RawBinary) (left right : RawExpr)
  | isNull (offset : Nat) (negated : Bool) (value : RawExpr)
  deriving Repr, BEq

namespace RawExpr

private def offset : RawExpr → Nat
  | .identifier offset _ | .string offset _ | .number offset _ | .null offset
  | .boolean offset _ | .call offset _ _ | .cast offset _ _ | .unary offset _ _
  | .binary offset _ _ _ | .isNull offset _ _ => offset

end RawExpr

private structure ParserState where
  tokens : Array Token
  index : Nat := 0

private abbrev ParseM := StateT ParserState (Except Diagnostic)

private def parseFailure (category : DiagnosticCategory) (offset : Nat)
    (message : String) : ParseM α :=
  fun _ => .error (diagnostic category offset message)

private def peek : ParseM (Option Token) := do
  pure (← get).tokens[(← get).index]?

private def take : ParseM Token := do
  let state ← get
  let some token := state.tokens[state.index]?
    | parseFailure .syntax
        (state.tokens.back?.map (fun token => token.stop) |>.getD 0)
        "unexpected end of constraint expression"
  set { state with index := state.index + 1 }
  pure token

private def tokenWord? (token : Token) (wanted : String) : Bool :=
  match token.kind with
  | .word value false => value == wanted
  | _ => false

private def consumeKind (wanted : TokenKind) : ParseM (Option Token) := do
  match ← peek with
  | some token =>
      if token.kind == wanted then
        let _ ← take
        pure (some token)
      else pure none
  | none => pure none

private def consumeWord (wanted : String) : ParseM (Option Token) := do
  match ← peek with
  | some token =>
      if tokenWord? token wanted then
        let _ ← take
        pure (some token)
      else pure none
  | none => pure none

private def expectKind (wanted : TokenKind) (description : String) : ParseM Token := do
  let state ← get
  match ← consumeKind wanted with
  | some token => pure token
  | none =>
      let offset := state.tokens[state.index]?.map (fun token => token.start)
        |>.getD (state.tokens.back?.map (fun token => token.stop) |>.getD 0)
      match state.tokens[state.index]? with
      | some { kind := .operator value, .. } =>
          parseFailure .unsupportedOperator offset
            s!"operator {value} is not supported in local constraints"
      | _ => parseFailure .syntax offset s!"expected {description}"

private def parseWord : ParseM (String × Nat) := do
  let token ← take
  match token.kind with
  | .word value _ => pure (value, token.start)
  | _ => parseFailure .syntax token.start "expected an identifier"

private def parseNameParts : ParseM (Array String × Nat) := do
  let (first, offset) ← parseWord
  let mut parts := #[first]
  while (← consumeKind .dot).isSome do
    let (part, _) ← parseWord
    parts := parts.push part
  pure (parts, offset)

private def parseTypeSyntax : ParseM TypeSyntax := do
  let (initialParts, offset) ← parseNameParts
  let mut parts := initialParts
  if parts.size == 1 && parts[0]! == "character" then
    if (← consumeWord "varying").isSome then
      parts := #["pg_catalog", "varchar"]
    else
      parts := #["pg_catalog", "bpchar"]
  else if parts.size == 1 && parts[0]! == "double" then
    if (← consumeWord "precision").isSome then
      parts := #["pg_catalog", "float8"]
  let mut modifiers : Array String := #[]
  if (← consumeKind .lparen).isSome then
    let mut done := false
    while !done do
      let token ← take
      match token.kind with
      | .number value => modifiers := modifiers.push value
      | _ => parseFailure .syntax token.start "type modifiers must be numeric literals"
      if (← consumeKind .comma).isSome then
        pure ()
      else
        let _ ← expectKind .rparen "')' after type modifier"
        done := true
  pure { offset, parts, modifiers }

mutual

private partial def parseOr : ParseM RawExpr := do
  let mut left ← parseAnd
  while true do
    let some token ← consumeWord "or" | break
    let right ← parseAnd
    left := .binary token.start .or left right
  pure left

private partial def parseAnd : ParseM RawExpr := do
  let mut left ← parseNot
  while true do
    let some token ← consumeWord "and" | break
    let right ← parseNot
    left := .binary token.start .and left right
  pure left

private partial def parseNot : ParseM RawExpr := do
  match ← consumeWord "not" with
  | some token => pure (.unary token.start .not (← parseNot))
  | none => parseComparison

private partial def parseComparison : ParseM RawExpr := do
  let left ← parseAdditive
  match ← peek with
  | some token =>
      let comparison? := match token.kind with
        | .eq => some RawBinary.eq
        | .ne => some .ne
        | .lt => some .lt
        | .le => some .le
        | .gt => some .gt
        | .ge => some .ge
        | _ => none
      match comparison? with
      | some op =>
          let _ ← take
          pure (.binary token.start op left (← parseAdditive))
      | none =>
          if tokenWord? token "is" then
            let _ ← take
            let negated := (← consumeWord "not").isSome
            match ← consumeWord "null" with
            | some _ => pure (.isNull token.start negated left)
            | none =>
                parseFailure .unsupportedOperator token.start
                  "only IS NULL and IS NOT NULL are supported"
          else pure left
  | none => pure left

private partial def parseAdditive : ParseM RawExpr := do
  let mut left ← parseUnary
  while true do
    match ← peek with
    | some token =>
        match token.kind with
        | .plus =>
            let _ ← take
            left := .binary token.start .add left (← parseUnary)
        | .minus =>
            let _ ← take
            left := .binary token.start .sub left (← parseUnary)
        | _ => break
    | none => break
  pure left

private partial def parseUnary : ParseM RawExpr := do
  match ← peek with
  | some token =>
      match token.kind with
      | .plus =>
          let _ ← take
          pure (.unary token.start .plus (← parseUnary))
      | .minus =>
          let _ ← take
          pure (.unary token.start .minus (← parseUnary))
      | _ => parsePostfix
  | none => parsePostfix

private partial def parsePostfix : ParseM RawExpr := do
  let mut value ← parsePrimary
  while true do
    let some token ← consumeKind .cast | break
    value := .cast token.start value (← parseTypeSyntax)
  pure value

private partial def parsePrimary : ParseM RawExpr := do
  let token ← take
  match token.kind with
  | .lparen =>
      let value ← parseOr
      let _ ← expectKind .rparen "')'"
      pure value
  | .string value => pure (.string token.start value)
  | .number value => pure (.number token.start value)
  | .word value quoted =>
      if !quoted && value == "null" then pure (.null token.start)
      else if !quoted && value == "true" then pure (.boolean token.start true)
      else if !quoted && value == "false" then pure (.boolean token.start false)
      else
        let mut parts := #[value]
        while (← consumeKind .dot).isSome do
          let (part, _) ← parseWord
          parts := parts.push part
        if (← consumeKind .lparen).isSome then
          if parts == #["position"] || parts == #["pg_catalog", "position"] then
            let substring ← parseOr
            unless (← consumeWord "in").isSome do
              parseFailure .syntax token.start
                "POSITION requires POSITION(substring IN string) syntax"
            let string ← parseOr
            let _ ← expectKind .rparen "')' after POSITION"
            pure (.call token.start parts #[substring, string])
          else
            let mut arguments : Array RawExpr := #[]
            unless (← consumeKind .rparen).isSome do
              let mut done := false
              while !done do
                arguments := arguments.push (← parseOr)
                if (← consumeKind .comma).isSome then pure ()
                else
                  let _ ← expectKind .rparen "')' after function arguments"
                  done := true
            pure (.call token.start parts arguments)
        else pure (.identifier token.start parts)
  | .operator value =>
      parseFailure .unsupportedOperator token.start
        s!"operator {value} is not supported in local constraints"
  | _ => parseFailure .syntax token.start "expected a constraint operand"

end

private def parseRaw (source : String) : Except Diagnostic RawExpr := do
  let tokens ← tokenize source
  let initial : ParserState := { tokens }
  let (hasCheck, state) ← (do
    let hasCheck := (← consumeWord "check").isSome
    pure hasCheck).run initial
  let parseBody : ParseM RawExpr := do
    if hasCheck then
      let _ ← expectKind .lparen "'(' after CHECK"
      let value ← parseOr
      let _ ← expectKind .rparen "')' closing CHECK"
      pure value
    else
      parseFailure .syntax
        (tokens[0]?.map (fun token => token.start) |>.getD 0)
        "expected normalized CHECK (...) definition"
  let (value, finalState) ← parseBody.run state
  if let some token := finalState.tokens[finalState.index]? then
    match token.kind with
    | .operator value =>
        throw (diagnostic .unsupportedOperator token.start
          s!"operator {value} is not supported in local constraints")
    | .word value _ =>
        throw (diagnostic .unsupportedOperator token.start
          s!"construct {value} is not supported after the check expression")
    | _ => throw (diagnostic .trailingInput token.start
        "unexpected input after the check expression")
  pure value

/-! ## Symbolic type resolution and typechecking -/

private structure Scope where
  columns : Array Pgx.RelationColumnIR := #[]
  relation : Option Pgx.RelationKey := none
  domainValue : Option Pgx.TypeRef := none
  enums : Array Pgx.EnumIR := #[]
  domains : Array Pgx.DomainIR := #[]
  deterministicTextEquality : Bool := false

/-- Capabilities which must be established from catalog/session metadata rather
than guessed from SQL spelling. -/
structure Options where
  deterministicTextEquality : Bool := false
  deriving Repr, BEq, Inhabited

private def builtinRef (name : String) : Pgx.TypeRef := {
  key := { schema := "pg_catalog", name, kind := .base }
}

private def builtinScalar (name : String) (base : ScalarKind) : ScalarType := {
  declared := builtinRef name
  base
}

private def boolType : ScalarType := builtinScalar "bool" .boolean
private def int2Type : ScalarType := builtinScalar "int2" .int16
private def int4Type : ScalarType := builtinScalar "int4" .int32
private def int8Type : ScalarType := builtinScalar "int8" .int64
private def numericType : ScalarType := builtinScalar "numeric" .numeric
private def textType : ScalarType := builtinScalar "text" .text

private def canonicalBaseType : ScalarKind → ScalarType
  | .boolean => boolType
  | .int16 => int2Type
  | .int32 => int4Type
  | .int64 => int8Type
  | .numeric => numericType
  | .text => textType
  | .enumeration key => { declared := { key }, base := .enumeration key }

private partial def resolveScalarType (scope : Scope) (offset : Nat) (ref : Pgx.TypeRef)
    (seen : Array Pgx.TypeKey := #[]) : Except Diagnostic ScalarType := do
  if seen.contains ref.key then
    throw (diagnostic .unsupportedType offset
      s!"domain type cycle reaches {ref.key.display}")
  match ref.key.kind with
  | .domain =>
      let some domain := scope.domains.find? (fun domain => domain.key == ref.key)
        | throw (diagnostic .unsupportedType offset
            s!"domain metadata is missing for {ref.key.display}")
      let base ← resolveScalarType scope offset domain.base (seen.push ref.key)
      pure {
        declared := ref
        base := base.base
        domains := #[ref.key] ++ base.domains
      }
  | .enum =>
      let some _ := scope.enums.find? (fun value => value.key == ref.key)
        | throw (diagnostic .unsupportedType offset
            s!"enum metadata is missing for {ref.key.display}")
      pure { declared := ref, base := .enumeration ref.key }
  | .base =>
      if ref.key.schema != "pg_catalog" then
        throw (diagnostic .unsupportedType offset
          s!"base type {ref.key.display} has no local constraint semantics")
      let base ← match ref.key.name with
        | "bool" => pure .boolean
        | "int2" => pure .int16
        | "int4" => pure .int32
        | "int8" => pure .int64
        | "numeric" => pure .numeric
        | "text" | "varchar" | "bpchar" => pure .text
        | name => throw (diagnostic .unsupportedType offset
            s!"pg_catalog.{name} has no local constraint semantics")
      pure { declared := ref, base }
  | _ => throw (diagnostic .unsupportedType offset
      s!"type {ref.key.display} is outside the local scalar subset")

private def aliasTypeName (parts : Array String) : Array String :=
  if parts.size != 1 then parts else
  match parts[0]! with
  | "boolean" => #["pg_catalog", "bool"]
  | "smallint" => #["pg_catalog", "int2"]
  | "integer" | "int" => #["pg_catalog", "int4"]
  | "bigint" => #["pg_catalog", "int8"]
  | "decimal" => #["pg_catalog", "numeric"]
  | "varchar" => #["pg_catalog", "varchar"]
  | "text" | "bool" | "int2" | "int4" | "int8" | "numeric" | "bpchar" =>
      #["pg_catalog", parts[0]!]
  | _ => parts

private def resolveTypeSyntax (scope : Scope) (typeSyntax : TypeSyntax) :
    Except Diagnostic ScalarType := do
  if !typeSyntax.modifiers.isEmpty then
    throw (diagnostic .unsafeCast typeSyntax.offset
      "casts with type modifiers can truncate or round values")
  let parts := aliasTypeName typeSyntax.parts
  let candidates : Array Pgx.TypeKey :=
    if parts.size == 2 then
      let schema := parts[0]!
      let name := parts[1]!
      let builtin : Array Pgx.TypeKey :=
        if schema == "pg_catalog" then
          #[{ schema, name, kind := .base }]
        else #[]
      builtin ++
        (scope.enums.filter (fun value =>
          value.key.schema == schema && value.key.name == name) |>.map (·.key)) ++
        (scope.domains.filter (fun value =>
          value.key.schema == schema && value.key.name == name) |>.map (·.key))
    else if parts.size == 1 then
      let name := parts[0]!
      (scope.enums.filter (fun value => value.key.name == name) |>.map (·.key)) ++
        (scope.domains.filter (fun value => value.key.name == name) |>.map (·.key))
    else #[]
  if candidates.isEmpty then
    throw (diagnostic .unsupportedType typeSyntax.offset
      s!"cast target {String.intercalate "." parts.toList} is not a supported scalar type")
  if candidates.size != 1 then
    throw (diagnostic .ambiguousIdentifier typeSyntax.offset
      s!"cast target {String.intercalate "." parts.toList} is ambiguous; qualify it")
  resolveScalarType scope typeSyntax.offset { key := candidates[0]! }

private def sameSemanticBase (left right : ScalarType) : Bool :=
  left.base == right.base

private def integerRank (ty : ScalarType) : Option Nat :=
  match ty.base with
  | .int16 => some 0
  | .int32 => some 1
  | .int64 => some 2
  | _ => none

private def castPreservation? (source target : ScalarType) : Option CastPreservation :=
  if source == target then some .identity
  else if source.base == target.base &&
      (!source.domains.isEmpty || !target.domains.isEmpty) then some .domain
  else if source.isText && target.isText && target.declared.typmod.isNone then
    some .textRepresentation
  else match integerRank source, integerRank target with
    | some left, some right => if left ≤ right then some .integerWiden else none
    | some _, none => if target.base matches .numeric then some .exactNumeric else none
    | _, _ => none

private def preservingCast (offset : Nat) (value : ValueExpr) (target : ScalarType) :
    Except Diagnostic ValueExpr := do
  let some preservation := castPreservation? value.type target
    | throw (diagnostic .unsafeCast offset
        s!"cast from {value.type.display} to {target.display} is not known to preserve modeled values")
  pure (.cast preservation value target)

private def columnFromParts (scope : Scope) (offset : Nat) (parts : Array String) :
    Except Diagnostic Pgx.RelationColumnIR := do
  if parts.isEmpty || parts.size > 3 then
    throw (diagnostic .unknownIdentifier offset
      s!"invalid column reference {String.intercalate "." parts.toList}")
  let name := parts.back!
  if parts.size ≥ 2 then
    let some relation := scope.relation
      | throw (diagnostic .unknownIdentifier offset
          "qualified column references are unavailable in a domain check")
    let qualifier := parts[parts.size - 2]!
    unless qualifier == relation.name do
      throw (diagnostic .unknownIdentifier offset
        s!"column qualifier {qualifier} does not name {relation.name}")
    if parts.size == 3 && parts[0]! != relation.schema then
      throw (diagnostic .unknownIdentifier offset
        s!"schema qualifier {parts[0]!} does not name {relation.schema}")
  let found := scope.columns.filter (fun column => column.name == name)
  if found.isEmpty then
    throw (diagnostic .unknownIdentifier offset s!"unknown constraint column {name}")
  if found.size != 1 then
    throw (diagnostic .ambiguousIdentifier offset s!"constraint column {name} is ambiguous")
  pure found[0]!

private def parseIntegerLiteral (offset : Nat) (value : String) :
    Except Diagnostic Int :=
  match value.toInt? with
  | some parsed => pure parsed
  | none => throw (diagnostic .invalidLiteral offset
      s!"integer literal {value} is outside the modeled range")

private def literalTypeForInt (value : Int) : ScalarType :=
  if (-2147483648 : Int) ≤ value && value ≤ 2147483647 then int4Type
  else if (-9223372036854775808 : Int) ≤ value && value ≤ 9223372036854775807 then int8Type
  else numericType

private def integerFits (value : Int) (ty : ScalarType) : Bool :=
  match ty.base with
  | .int16 => (-32768 : Int) ≤ value && value ≤ 32767
  | .int32 => (-2147483648 : Int) ≤ value && value ≤ 2147483647
  | .int64 =>
      (-9223372036854775808 : Int) ≤ value && value ≤ 9223372036854775807
  | .numeric => true
  | _ => false

private def compatibleLiteralType (expected : ScalarType) (predicate : ScalarType → Bool)
    (fallback : ScalarType) : ScalarType :=
  if predicate expected then expected else fallback

private partial def resolveValue (scope : Scope) (raw : RawExpr)
    (expected : Option ScalarType := none) : Except Diagnostic ValueExpr := do
  match raw with
  | .identifier offset parts =>
      if parts.size == 1 && parts[0]! == "value" && scope.domainValue.isSome then
        let ty ← resolveScalarType scope offset scope.domainValue.get!
        pure (.domainValue ty true)
      else
        let column ← columnFromParts scope offset parts
        let ty ← resolveScalarType scope offset column.ty
        pure (.column column.name ty column.nullable)
  | .string _ value =>
      match expected with
      | some ty =>
          match ty.base with
          | .enumeration key =>
              let some enum := scope.enums.find? (fun enum => enum.key == key)
                | throw (diagnostic .unsupportedType raw.offset
                    s!"enum metadata is missing for {key.display}")
              unless enum.labels.contains value do
                throw (diagnostic .invalidLiteral raw.offset
                  s!"{repr value} is not a label of {key.display}")
              pure (.literal (.enumeration key value) ty)
          | .text => pure (.literal (.text value) ty)
          | _ => throw (diagnostic .typeMismatch raw.offset
              s!"text literal cannot have type {ty.display}")
      | none => pure (.literal (.text value) textType)
  | .number offset value =>
      if value.any (fun char => char == '.' || char == 'e' || char == 'E') then
        let ty := expected.map (fun ty => compatibleLiteralType ty
          (fun ty => ty.base matches .numeric) numericType) |>.getD numericType
        pure (.literal (.numeric value) ty)
      else
        let parsed ← parseIntegerLiteral offset value
        let fallback := literalTypeForInt parsed
        let ty := expected.map (fun ty => compatibleLiteralType ty
          (fun ty => ty.isExactNumeric && integerFits parsed ty) fallback) |>.getD fallback
        pure (.literal (.integer parsed) ty)
  | .null offset =>
      let some ty := expected
        | throw (diagnostic .typeMismatch offset
            "NULL requires a typed operand or an explicit preserving cast")
      pure (.literal .null ty)
  | .boolean _ value => pure (.literal (.boolean value) boolType)
  | .cast offset rawValue typeSyntax =>
      let target ← resolveTypeSyntax scope typeSyntax
      match rawValue, target.base with
      | .string literalOffset label, .enumeration key =>
          let some enum := scope.enums.find? (fun enum => enum.key == key)
            | throw (diagnostic .unsupportedType literalOffset
                s!"enum metadata is missing for {key.display}")
          unless enum.labels.contains label do
            throw (diagnostic .invalidLiteral literalOffset
              s!"{repr label} is not a label of {key.display}")
          pure (.cast .enumLiteral (.literal (.text label) textType) target)
      | _, _ =>
          let value ← resolveValue scope rawValue (some target)
          preservingCast offset value target
  | .unary offset .plus value =>
      let value ← resolveValue scope value expected
      unless value.type.isExactNumeric do
        throw (diagnostic .typeMismatch offset "unary + requires an exact numeric operand")
      pure value
  | .unary offset .minus (.number _ value) =>
      resolveValue scope (.number offset ("-" ++ value)) expected
  | .unary offset .minus _ =>
      throw (diagnostic .unsupportedOperator offset
        "unary negation is disabled except for literals until overflow is modeled")
  | .binary offset op _ _ =>
      match op with
      | .add | .sub => throw (diagnostic .unsupportedOperator offset
          "exact arithmetic is disabled until validation models PostgreSQL overflow errors")
      | _ => throw (diagnostic .typeMismatch offset
          "Boolean or comparison expression used where a scalar was required")
  | .call offset name arguments =>
      let qualified := String.intercalate "." name.toList
      if name == #["char_length"] || name == #["pg_catalog", "char_length"] then
        unless arguments.size == 1 do
          throw (diagnostic .typeMismatch offset "char_length requires exactly one argument")
        let some argument := arguments[0]?
          | throw (diagnostic .typeMismatch offset "char_length requires an argument")
        let value ← resolveValue scope argument (some textType)
        unless value.type.isText do
          throw (diagnostic .typeMismatch argument.offset
            "char_length requires a text, varchar, or char operand")
        pure (.charLength value int4Type)
      else if name == #["btrim"] || name == #["pg_catalog", "btrim"] then
        unless arguments.size == 1 do
          throw (diagnostic .typeMismatch offset
            "the supported btrim form requires exactly one argument")
        let some argument := arguments[0]?
          | throw (diagnostic .typeMismatch offset "btrim requires an argument")
        let value ← resolveValue scope argument (some textType)
        unless value.type.isText do
          throw (diagnostic .typeMismatch argument.offset
            "btrim requires a text, varchar, or char operand")
        pure (.btrim value textType)
      else if name == #["position"] || name == #["pg_catalog", "position"] then
        unless arguments.size == 2 do
          throw (diagnostic .typeMismatch offset
            "POSITION requires a substring and a string")
        let some substringArg := arguments[0]?
          | throw (diagnostic .typeMismatch offset "POSITION requires a substring")
        let some stringArg := arguments[1]?
          | throw (diagnostic .typeMismatch offset "POSITION requires a string")
        let substring ← resolveValue scope substringArg (some textType)
        let string ← resolveValue scope stringArg (some textType)
        unless substring.type.isText && string.type.isText do
          throw (diagnostic .typeMismatch offset "POSITION operands must be text values")
        pure (.position substring string int4Type)
      else
        throw (diagnostic .unsupportedFunction offset
          s!"function {qualified} is not supported in local constraints")
  | .isNull offset _ _ => throw (diagnostic .typeMismatch offset
      "null test used where a scalar was required")
  | .unary offset .not _ => throw (diagnostic .typeMismatch offset
      "Boolean NOT used where a scalar was required")

private def comparisonOfRaw : RawBinary → Option Comparison
  | .eq => some .eq
  | .ne => some .ne
  | .lt => some .lt
  | .le => some .le
  | .gt => some .gt
  | .ge => some .ge
  | _ => none

private def chooseCommonType (offset : Nat) (left right : ScalarType) :
    Except Diagnostic ScalarType := do
  if left == right then pure left
  else if sameSemanticBase left right then
    match left.base with
    | .text => pure textType
    | .enumeration key =>
        if right.base == .enumeration key then pure left
        else throw (diagnostic .typeMismatch offset "different enum types cannot be compared")
    | _ =>
        if left.domains.isEmpty then pure left
        else if right.domains.isEmpty then pure right
        else pure (canonicalBaseType left.base)
  else if left.isExactNumeric && right.isExactNumeric then
    if left.base matches .numeric then pure numericType
    else if right.base matches .numeric then pure numericType
    else
      match integerRank left, integerRank right with
      | some leftRank, some rightRank =>
          pure (if leftRank ≥ rightRank then left else right)
      | _, _ => throw (diagnostic .typeMismatch offset "incompatible numeric operands")
  else throw (diagnostic .typeMismatch offset
    s!"incompatible operand types {left.display} and {right.display}")

private partial def resolveComparison (scope : Scope) (offset : Nat)
    (op : Comparison) (rawLeft rawRight : RawExpr) : Except Diagnostic TruthExpr := do
  let leftFirst := resolveValue scope rawLeft
  let (left, right) ← match leftFirst with
    | .ok left => pure (left, ← resolveValue scope rawRight (some left.type))
    | .error firstError =>
        match resolveValue scope rawRight with
        | .error _ => throw firstError
        | .ok right => pure (← resolveValue scope rawLeft (some right.type), right)
  let common ← chooseCommonType offset left.type right.type
  if common.base matches .numeric then
    throw (diagnostic .unsupportedType offset
      "pg_catalog.numeric comparisons are unsupported because exact ordering is not modeled")
  if common.isText && op != .eq && op != .ne then
    throw (diagnostic .unsupportedOperator offset
      "text ordering is collation-sensitive and is not modeled")
  if common.isText && !scope.deterministicTextEquality then
    throw (diagnostic .unsupportedOperator offset
      "text equality requires catalog proof of deterministic bytewise comparison")
  if (common.base matches .boolean) && op != .eq && op != .ne then
    throw (diagnostic .unsupportedOperator offset
      "Boolean ordering is outside the local constraint subset")
  if (common.base matches .enumeration _) && op != .eq && op != .ne then
    throw (diagnostic .unsupportedOperator offset
      "enum ordering is outside the local constraint subset")
  let left ← preservingCast offset left common
  let right ← preservingCast offset right common
  pure (.compare op left right)

private partial def resolveTruth (scope : Scope) (raw : RawExpr) :
    Except Diagnostic TruthExpr := do
  match raw with
  | .boolean _ value => pure (.constant (some value))
  | .null _ => pure (.constant none)
  | .unary _ .not value => pure (.not (← resolveTruth scope value))
  | .binary _ .and left right =>
      pure (.and (← resolveTruth scope left) (← resolveTruth scope right))
  | .binary _ .or left right =>
      pure (.or (← resolveTruth scope left) (← resolveTruth scope right))
  | .binary offset op left right =>
      let some comparison := comparisonOfRaw op
        | throw (diagnostic .nonBooleanCheck offset
            "arithmetic expression is not a Boolean check")
      resolveComparison scope offset comparison left right
  | .isNull _ negated value =>
      let value ← resolveValue scope value
      pure (if negated then .isNotNull value else .isNull value)
  | _ =>
      let value ← resolveValue scope raw
      unless value.type.isBoolean do
        throw (diagnostic .nonBooleanCheck raw.offset
          s!"check expression has scalar type {value.type.display}, not Boolean")
      pure (.fromBoolean value)

private def invariantFailure (message : String) : Except Diagnostic α :=
  throw (diagnostic .typeMismatch 0 s!"invalid typed constraint IR: {message}")

private def validateScalar (scope : Scope) (ty : ScalarType) : Except Diagnostic Unit := do
  let resolved ← resolveScalarType scope 0 ty.declared
  unless resolved == ty do
    invariantFailure s!"annotation for {ty.display} does not match catalog semantics"

private partial def validateValue (scope : Scope) : ValueExpr → Except Diagnostic Unit
  | .column name ty nullable => do
      validateScalar scope ty
      let found := scope.columns.filter (fun column => column.name == name)
      unless found.size == 1 do
        invariantFailure s!"column {name} does not resolve uniquely"
      let resolved ← resolveScalarType scope 0 found[0]!.ty
      unless resolved == ty && found[0]!.nullable == nullable do
        invariantFailure s!"column {name} annotation differs from relation metadata"
  | .domainValue ty nullable => do
      validateScalar scope ty
      let some ref := scope.domainValue
        | invariantFailure "VALUE appears outside a domain check"
      let resolved ← resolveScalarType scope 0 ref
      unless resolved == ty && nullable do
        invariantFailure "VALUE annotation differs from its domain metadata"
  | .literal literal ty => do
      validateScalar scope ty
      match literal, ty.base with
      | .null, _ => pure ()
      | .boolean _, .boolean => pure ()
      | .integer value, .int16 | .integer value, .int32 | .integer value, .int64
      | .integer value, .numeric =>
          unless integerFits value ty do
            invariantFailure s!"integer literal is outside {ty.display}"
      | .numeric _, .numeric | .text _, .text => pure ()
      | .enumeration key label, .enumeration actual =>
          unless key == actual do invariantFailure "enum literal type key differs from its annotation"
          let some enum := scope.enums.find? (fun enum => enum.key == key)
            | invariantFailure s!"enum metadata is missing for {key.display}"
          unless enum.labels.contains label do
            invariantFailure s!"{repr label} is not a label of {key.display}"
      | _, _ => invariantFailure s!"literal payload does not have type {ty.display}"
  | .cast preservation value target => do
      validateValue scope value
      validateScalar scope target
      if preservation == .enumLiteral then
        match value, target.base with
        | .literal (.text label) source, .enumeration key =>
            unless source == textType do
              invariantFailure "enum literal cast source is not pg_catalog.text"
            let some enum := scope.enums.find? (fun enum => enum.key == key)
              | invariantFailure s!"enum metadata is missing for {key.display}"
            unless enum.labels.contains label do
              invariantFailure s!"{repr label} is not a label of {key.display}"
        | _, _ => invariantFailure "enum-literal cast has incompatible operands"
      else
        unless castPreservation? value.type target == some preservation do
          invariantFailure s!"cast from {value.type.display} to {target.display} is not preserving"
  | .neg value result => do
      validateValue scope value
      validateScalar scope result
      invariantFailure "arithmetic nodes require overflow-aware evaluation"
  | .add left right result | .sub left right result => do
      validateValue scope left
      validateValue scope right
      validateScalar scope result
      invariantFailure "arithmetic nodes require overflow-aware evaluation"
  | .charLength value result => do
      validateValue scope value
      validateScalar scope result
      unless value.type.isText && result == int4Type do
        invariantFailure "char_length has incompatible operand or result annotations"
  | .btrim value result => do
      validateValue scope value
      validateScalar scope result
      unless value.type.isText && result == textType do
        invariantFailure "btrim has incompatible operand or result annotations"
  | .position substring string result => do
      validateValue scope substring
      validateValue scope string
      validateScalar scope result
      unless substring.type.isText && string.type.isText && result == int4Type do
        invariantFailure "POSITION has incompatible operand or result annotations"

private partial def validateTruth (scope : Scope) : TruthExpr → Except Diagnostic Unit
  | .constant _ => pure ()
  | .fromBoolean value => do
      validateValue scope value
      unless value.type.isBoolean do
        invariantFailure "fromBoolean operand is not Boolean"
  | .compare op left right => do
      validateValue scope left
      validateValue scope right
      unless left.type == right.type do
        invariantFailure "comparison operands do not have a common type"
      match left.type.base with
      | .text =>
          unless (op == .eq || op == .ne) && scope.deterministicTextEquality do
            invariantFailure "text comparison lacks deterministic equality semantics"
      | .enumeration _ | .boolean =>
          unless op == .eq || op == .ne do
            invariantFailure "enum and Boolean values support equality only"
      | .int16 | .int32 | .int64 | .numeric => pure ()
  | .isNull value | .isNotNull value => validateValue scope value
  | .and left right | .or left right => do
      validateTruth scope left
      validateTruth scope right
  | .not value => validateTruth scope value

private def parseInScope (scope : Scope) (source : String) :
    Except Diagnostic Parsed := do
  let raw ← parseRaw source
  let expression ← resolveTruth scope raw
  validateTruth scope expression
  pure { source, expression }

/-- Parse and typecheck a relation-local `CHECK` definition. -/
def parseTableCheck (relation : Pgx.RelationIR) (enums : Array Pgx.EnumIR)
    (domains : Array Pgx.DomainIR) (source : String) (options : Options := {}) :
    Except Diagnostic Parsed :=
  parseInScope {
    columns := relation.columns
    relation := some relation.key
    enums
    domains
    deterministicTextEquality := options.deterministicTextEquality
  } source

/-- Parse and typecheck a domain `CHECK` definition.  `VALUE` is bound to the
domain, and nested domain metadata is resolved recursively. -/
def parseDomainCheck (domain : Pgx.DomainIR) (enums : Array Pgx.EnumIR)
    (domains : Array Pgx.DomainIR) (source : String) (options : Options := {}) :
    Except Diagnostic Parsed :=
  parseInScope {
    domainValue := some { key := domain.key }
    enums
    domains
    deterministicTextEquality := options.deterministicTextEquality
  } source

end Pgx.Codegen.ConstraintParser
