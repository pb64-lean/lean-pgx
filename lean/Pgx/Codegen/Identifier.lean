/-!
# Lean source identifiers

Small, pure helpers used by the PostgreSQL source emitter.  Database names are
not assumed to be Lean identifiers: punctuation and non-ASCII characters are
encoded, keywords are avoided, and a scope can allocate deterministic suffixes
when two source names normalize to the same spelling.
-/

namespace Pgx.Codegen.Identifier

private def isAsciiLower (c : Char) : Bool :=
  'a' <= c && c <= 'z'

private def isAsciiUpper (c : Char) : Bool :=
  'A' <= c && c <= 'Z'

private def isAsciiDigit (c : Char) : Bool :=
  '0' <= c && c <= '9'

private def isAsciiAlpha (c : Char) : Bool :=
  isAsciiLower c || isAsciiUpper c

private def asciiUpper (c : Char) : Char :=
  if isAsciiLower c then Char.ofNat (c.toNat - 'a'.toNat + 'A'.toNat) else c

private def asciiLower (c : Char) : Char :=
  if isAsciiUpper c then Char.ofNat (c.toNat - 'A'.toNat + 'a'.toNat) else c

private def encodedChar (c : Char) : String :=
  if isAsciiAlpha c || isAsciiDigit c then
    String.singleton c
  else if c == '_' then
    "_"
  else
    "_u" ++ toString c.toNat ++ "_"

/-- An injective-enough ASCII spelling before case styling.  The final scope
allocator remains the authority for collisions (including a literal source
name that already resembles an encoded character). -/
def ascii (source : String) : String :=
  String.join (source.toList.map encodedChar)

private def capitalizeWordsAux : List Char → Bool → List Char
  | [], _ => []
  | '_' :: rest, _ => capitalizeWordsAux rest true
  | c :: rest, capitalize =>
      (if capitalize then asciiUpper c else c) :: capitalizeWordsAux rest false

private def capitalizeWords (source : String) : String :=
  String.ofList (capitalizeWordsAux (ascii source).toList true)

private def startsWithDigit (source : String) : Bool :=
  match source.toList with
  | c :: _ => isAsciiDigit c
  | [] => false

/-- Lean parser keywords and common command tokens.  Generated spellings that
hit this list receive a readable suffix rather than relying on quoted names. -/
def reserved : Array String := #[
  "abbrev", "axiom", "by", "class", "def", "deriving", "do", "else",
  "end", "example", "export", "extends", "for", "forall", "from", "fun",
  "if", "import", "in", "include", "inductive", "infix", "infixl",
  "infixr", "instance", "let", "macro", "match", "mutual", "namespace",
  "notation", "opaque", "open", "partial", "private", "protected",
  "public", "section", "set_option", "structure", "syntax", "termination_by",
  "theorem", "then", "universe", "variable", "where", "with"
]

private def avoidReserved (fallback source : String) : String :=
  let source := if source.isEmpty then fallback else source
  let source := if startsWithDigit source then "n" ++ source else source
  if reserved.contains source then source ++ "_value" else source

/-- Produce a declaration/module-style identifier. -/
def upperCamel (source : String) (fallback : String := "Generated") : String :=
  avoidReserved fallback (capitalizeWords source)

/-- Produce a field/case-style identifier. -/
def lowerCamel (source : String) (fallback : String := "value") : String :=
  let value := capitalizeWords source
  let value := match value.toList with
    | [] => ""
    | c :: rest => String.ofList (asciiLower c :: rest)
  avoidReserved fallback value

/-- A deterministic allocator for one Lean namespace. -/
structure Scope where
  used : Array String := #[]
  deriving Repr, BEq, Inhabited

namespace Scope

private def candidate (preferred : String) (suffix : Nat) : String :=
  if suffix == 1 then preferred else preferred ++ "_" ++ toString suffix

private def firstFree (scope : Scope) (preferred : String) : String := Id.run do
  -- Among `used.size + 1` candidates at least one is absent.
  for offset in [0:scope.used.size + 1] do
    let value := candidate preferred (offset + 1)
    unless scope.used.contains value do return value
  -- Unreachable, but keeps the executable allocator independent of a proof
  -- about the `for` range implementation.
  return preferred ++ "_" ++ toString (scope.used.size + 2)

/-- Claim `preferred`, adding `_2`, `_3`, ... when needed. -/
def claim (scope : Scope) (preferred : String) : String × Scope :=
  let value := firstFree scope preferred
  (value, { used := scope.used.push value })

end Scope

/-- Lean's own `Repr String` implementation is the most robust spelling of a
Lean string literal and tracks the compiler's accepted escapes. -/
def stringLiteral (value : String) : String :=
  reprStr value

end Pgx.Codegen.Identifier
