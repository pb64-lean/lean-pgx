import Pg

/-!
# PostgreSQL composite text values

PostgreSQL's composite text format represents SQL NULL as an empty field.  A
quoted empty field is instead the non-NULL empty string.  This module exposes
that distinction directly and leaves conversion of each non-NULL field to the
generated type-specific codec.
-/

namespace Pgx.Typed

/-- The raw fields of a PostgreSQL composite value.  `none` is SQL NULL;
`some ""` is a present empty string. -/
abbrev CompositeTextFields := Array (Option String)

private structure CompositeTextScan where
  fields : CompositeTextFields := #[]
  buffer : List Char := []
  tokenStarted : Bool := false
  inQuotes : Bool := false
  justClosedQuote : Bool := false
  escaped : Bool := false
  closed : Bool := false

private def finishCompositeField (state : CompositeTextScan) : Option String :=
  if state.tokenStarted then
    some (String.ofList state.buffer.reverse)
  else
    none

private def nextCompositeField (state : CompositeTextScan) : CompositeTextScan :=
  { fields := state.fields.push (finishCompositeField state) }

private def closeComposite (state : CompositeTextScan) : CompositeTextScan :=
  { state with
    fields := state.fields.push (finishCompositeField state)
    closed := true }

/-- Scan a composite after its opening parenthesis.

Backslash escapes are accepted both inside and outside quotes.  Within quotes,
PostgreSQL's doubled-quote spelling is accepted as well. -/
private def scanCompositeText (source : String) :
    CompositeTextScan → List Char → Except String CompositeTextScan
  | state, [] => .ok state
  | state, c :: rest =>
      if state.closed then
        .error s!"composite: trailing characters in {source}"
      else if state.escaped then
        scanCompositeText source
          { state with
            buffer := c :: state.buffer
            tokenStarted := true
            escaped := false }
          rest
      else if c == '\\' then
        scanCompositeText source
          { state with
            tokenStarted := true
            justClosedQuote := false
            escaped := true }
          rest
      else if c == '"' then
        if state.inQuotes then
          scanCompositeText source
            { state with inQuotes := false, justClosedQuote := true }
            rest
        else if state.justClosedQuote then
          -- Two adjacent quotes within a quoted fragment spell one quote.
          scanCompositeText source
            { state with
              buffer := '"' :: state.buffer
              inQuotes := true
              justClosedQuote := false }
            rest
        else
          -- PostgreSQL permits quoted and unquoted fragments to be
          -- concatenated within one field.
          scanCompositeText source
            { state with
              tokenStarted := true
              inQuotes := true
              justClosedQuote := false }
            rest
      else if !state.inQuotes && c == ',' then
        scanCompositeText source (nextCompositeField state) rest
      else if !state.inQuotes && c == ')' then
        scanCompositeText source (closeComposite state) rest
      else
        scanCompositeText source
          { state with
            buffer := c :: state.buffer
            tokenStarted := true
            justClosedQuote := false }
          rest
termination_by _ chars => chars.length
decreasing_by all_goals simp_wf

/-- Parse PostgreSQL's text representation of one composite value.

Outer ASCII whitespace is accepted and field whitespace is preserved.
PostgreSQL composite types have at least one logical field, so `()` is
represented as one NULL field. -/
def parseCompositeText (source : String) : Except String CompositeTextFields :=
  match Pg.trimAsciiChars source.toList with
  | '(' :: rest =>
      match scanCompositeText source {} rest with
      | .error message => .error message
      | .ok state =>
          if state.closed && !state.inQuotes && !state.escaped then
            .ok state.fields
          else
            .error s!"composite: unterminated literal {source}"
  | _ => .error s!"not a composite literal: {source}"

private def escapeCompositeField : List Char → List Char
  | [] => []
  | c :: rest =>
      if c == '"' || c == '\\' then
        '\\' :: c :: escapeCompositeField rest
      else
        c :: escapeCompositeField rest

private def renderCompositeField : Option String → String
  | none => ""
  | some value =>
      String.ofList ('"' :: (escapeCompositeField value.toList ++ ['"']))

/-- Render raw composite fields in a canonical, lossless text form.

Every present field is quoted.  This intentionally avoids relying on the
lexical rules of the field's concrete PostgreSQL type. -/
def renderCompositeText (fields : CompositeTextFields) : String :=
  "(" ++ String.intercalate "," (fields.toList.map renderCompositeField) ++ ")"

end Pgx.Typed
