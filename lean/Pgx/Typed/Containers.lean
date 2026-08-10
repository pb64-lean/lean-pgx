module

public import Pg

public section

/-!
# PostgreSQL container codecs

Pure, callback-driven codecs for the container types whose concrete element
types are resolved by generated code at runtime.  These functions deliberately
do not consult a catalog: callers prove the relevant OIDs before supplying the
element callbacks.

Only one-dimensional PostgreSQL arrays are represented.  Binary array lower
bounds must be one, so decoding never silently loses PostgreSQL dimension
metadata that Lean's `Array` cannot represent.
-/

namespace Pgx.Typed

/-- A one-dimensional PostgreSQL array.  PostgreSQL NULL elements are kept
distinct from non-NULL values. -/
abbrev PgArray (α : Type) := Array (Option α)

/-- A finite range bound.  An absent `RangeBound` means an infinite bound. -/
structure RangeBound (α : Type) where
  value : α
  inclusive : Bool
  deriving Repr, BEq

/-- A PostgreSQL range, including its distinguished empty value. -/
inductive PgRange (α : Type) where
  | empty
  | span (lower upper : Option (RangeBound α))
  deriving Repr, BEq, Inhabited

/-- PostgreSQL canonicalizes a multirange to an ordered collection of
non-overlapping ranges.  The codec preserves the order received on the wire. -/
abbrev PgMultirange (α : Type) := Array (PgRange α)

private def contextual (context : String) : Except String α → Except String α
  | .ok value => .ok value
  | .error message => .error s!"{context}: {message}"

private def escapedQuotedChars : List Char → List Char
  | [] => []
  | c :: rest =>
      if c == '"' || c == '\\' then
        '\\' :: c :: escapedQuotedChars rest
      else
        c :: escapedQuotedChars rest

private def quotedChars (value : String) : List Char :=
  '"' :: (escapedQuotedChars value.toList ++ ['"'])

private def commaSeparatedChars : List String → List Char
  | [] => []
  | [value] => value.toList
  | value :: rest => value.toList ++ ',' :: commaSeparatedChars rest

private structure ArrayTextScan where
  elements : Array (Option String) := #[]
  buffer : List Char := []
  quoted : Bool := false
  inQuotes : Bool := false
  escaped : Bool := false
  tokenStarted : Bool := false
  expectElement : Bool := true
  closed : Bool := false

private def finishArrayElement (source : String) (state : ArrayTextScan) :
    Except String (Option String) := do
  unless state.tokenStarted do
    throw s!"array: empty element in {source}"
  let chars := if state.quoted then state.buffer.reverse
    else Pg.trimAsciiChars state.buffer.reverse
  let value := String.ofList chars
  unless state.quoted || !value.isEmpty do
    throw s!"array: empty unquoted element in {source}"
  pure (if !state.quoted && value == "NULL" then none else some value)

/-- Strict scanner for one-dimensional array text.  In particular, braces
inside an unquoted element are rejected instead of being mistaken for a
flattened or partially consumed nested array. -/
private def scanArrayText (source : String) : ArrayTextScan → List Char →
    Except String ArrayTextScan
  | state, [] => .ok state
  | state, c :: rest =>
      if state.closed then
        .error s!"array: trailing characters in {source}"
      else if state.escaped then
        scanArrayText source
          { state with
            buffer := c :: state.buffer
            escaped := false
            tokenStarted := true }
          rest
      else if state.inQuotes then
        if c == '\\' then
          scanArrayText source { state with escaped := true } rest
        else if c == '"' then
          scanArrayText source { state with inQuotes := false } rest
        else
          scanArrayText source { state with buffer := c :: state.buffer } rest
      else if c == ',' then
        if state.expectElement then
          .error s!"array: empty element in {source}"
        else
          match finishArrayElement source state with
          | .error message => .error message
          | .ok value =>
              scanArrayText source
                { state with
                  elements := state.elements.push value
                  buffer := []
                  quoted := false
                  tokenStarted := false
                  expectElement := true }
                rest
      else if c == '}' then
        if state.expectElement then
          if state.elements.isEmpty && !state.tokenStarted then
            scanArrayText source { state with closed := true } rest
          else
            .error s!"array: trailing comma in {source}"
        else
          match finishArrayElement source state with
          | .error message => .error message
          | .ok value =>
              scanArrayText source
                { state with
                  elements := state.elements.push value
                  buffer := []
                  closed := true }
                rest
      else if c == '{' then
        .error s!"array: nested arrays are unsupported in {source}"
      else if c == '"' then
        if state.tokenStarted then
          .error s!"array: quote inside unquoted element in {source}"
        else
          scanArrayText source
            { state with
              quoted := true
              inQuotes := true
              tokenStarted := true
              expectElement := false }
            rest
      else if c == '\\' then
        if state.quoted then
          .error s!"array: characters after quoted element in {source}"
        else
          scanArrayText source
            { state with
              escaped := true
              tokenStarted := true
              expectElement := false }
            rest
      else if state.quoted then
        if Pg.isAsciiSpace c then
          scanArrayText source state rest
        else
          .error s!"array: characters after quoted element in {source}"
      else
        scanArrayText source
          { state with
            buffer := c :: state.buffer
            tokenStarted := true
            expectElement := false }
          rest

private def rawArrayText (source : String) : Except String (Array (Option String)) :=
  match Pg.trimAsciiChars source.toList with
  | '{' :: rest =>
      match scanArrayText source {} rest with
      | .error message => .error message
      | .ok state =>
          if state.closed && !state.inQuotes && !state.escaped then
            .ok state.elements
          else
            .error s!"array: unterminated literal {source}"
  | _ => .error s!"not an array literal: {source}"

/-- Decode one-dimensional array text through a non-NULL element callback. -/
def decodeArrayText (decodeElement : String → Except String α) (source : String) :
    Except String (PgArray α) := do
  let raw ← rawArrayText source
  raw.mapIdxM fun index value =>
    match value with
    | none => pure none
    | some text =>
        some <$> contextual s!"array element {index}" (decodeElement text)

/-- Encode one-dimensional array text.  Every non-NULL element is quoted, so
literal `NULL`, delimiters, braces, whitespace, quotes, and backslashes all
round-trip without depending on subtype-specific lexical rules. -/
def encodeArrayText (encodeElement : α → Except String String) (values : PgArray α) :
    Except String String := do
  let encoded ← values.mapIdxM fun index value =>
    match value with
    | none => pure "NULL"
    | some value => do
        let text ← contextual s!"array element {index}" (encodeElement value)
        pure (String.ofList (quotedChars text))
  pure (String.ofList ('{' :: (commaSeparatedChars encoded.toList ++ ['}'])))

private structure RawRange where
  lower : Option String
  upper : Option String
  lowerInclusive : Bool
  upperInclusive : Bool

private structure RangeTextScan where
  lower : Option (Option String) := none
  buffer : List Char := []
  quoted : Bool := false
  inQuotes : Bool := false
  escaped : Bool := false
  tokenStarted : Bool := false

private def finishRangeBound (state : RangeTextScan) : Option String :=
  if !state.tokenStarted then none
  else
    let chars := if state.quoted then state.buffer.reverse
      else Pg.trimAsciiChars state.buffer.reverse
    let value := String.ofList chars
    if !state.quoted && value.isEmpty then none else some value

private def scanRangeText (source : String) (lowerInclusive : Bool) :
    RangeTextScan → List Char → Except String RawRange
  | _, [] => .error s!"range: unterminated literal {source}"
  | state, c :: rest =>
      if state.escaped then
        scanRangeText source lowerInclusive
          { state with
            buffer := c :: state.buffer
            escaped := false
            tokenStarted := true }
          rest
      else if state.inQuotes then
        if c == '\\' then
          scanRangeText source lowerInclusive { state with escaped := true } rest
        else if c == '"' then
          scanRangeText source lowerInclusive { state with inQuotes := false } rest
        else
          scanRangeText source lowerInclusive { state with buffer := c :: state.buffer } rest
      else if c == ',' then
        match state.lower with
        | some _ => .error s!"range: more than one separator in {source}"
        | none =>
            scanRangeText source lowerInclusive
              { state with
                lower := some (finishRangeBound state)
                buffer := []
                quoted := false
                tokenStarted := false }
              rest
      else if c == ')' || c == ']' then
        match state.lower with
        | none => .error s!"range: missing separator in {source}"
        | some lower =>
            if rest.isEmpty then
              let upper := finishRangeBound state
              let upperInclusive := c == ']'
              if lower.isNone && lowerInclusive then
                .error s!"range: an infinite lower bound cannot be inclusive in {source}"
              else if upper.isNone && upperInclusive then
                .error s!"range: an infinite upper bound cannot be inclusive in {source}"
              else
                .ok { lower, upper, lowerInclusive, upperInclusive }
            else
              .error s!"range: trailing characters in {source}"
      else if c == '[' || c == '(' || c == '{' || c == '}' then
        .error s!"range: unquoted delimiter in a bound in {source}"
      else if c == '"' then
        if state.tokenStarted then
          .error s!"range: quote inside unquoted bound in {source}"
        else
          scanRangeText source lowerInclusive
            { state with quoted := true, inQuotes := true, tokenStarted := true }
            rest
      else if c == '\\' then
        if state.quoted then
          .error s!"range: characters after quoted bound in {source}"
        else
          scanRangeText source lowerInclusive
            { state with escaped := true, tokenStarted := true }
            rest
      else if state.quoted then
        if Pg.isAsciiSpace c then
          scanRangeText source lowerInclusive state rest
        else
          .error s!"range: characters after quoted bound in {source}"
      else
        scanRangeText source lowerInclusive
          { state with buffer := c :: state.buffer, tokenStarted := true }
          rest

private def rawRangeText (source : String) : Except String (Option RawRange) :=
  let chars := Pg.trimAsciiChars source.toList
  if chars == "empty".toList then
    .ok none
  else
    match chars with
    | '[' :: rest => some <$> scanRangeText source true {} rest
    | '(' :: rest => some <$> scanRangeText source false {} rest
    | _ => .error s!"not a range literal: {source}"

private def decodeOptionalBound (context : String) (inclusive : Bool)
    (decodeElement : String → Except String α) : Option String →
    Except String (Option (RangeBound α))
  | none => pure none
  | some text => do
      let value ← contextual context (decodeElement text)
      pure (some { value, inclusive })

/-- Decode range text through a subtype callback. -/
def decodeRangeText (decodeElement : String → Except String α) (source : String) :
    Except String (PgRange α) := do
  match ← rawRangeText source with
  | none => pure .empty
  | some raw =>
      let lower ← decodeOptionalBound "range lower bound" raw.lowerInclusive decodeElement raw.lower
      let upper ← decodeOptionalBound "range upper bound" raw.upperInclusive decodeElement raw.upper
      pure (.span lower upper)

private def encodeOptionalBound (context : String)
    (encodeElement : α → Except String String) : Option (RangeBound α) →
    Except String String
  | none => pure ""
  | some bound => do
      let text ← contextual context (encodeElement bound.value)
      pure (String.ofList (quotedChars text))

/-- Encode range text with quoted finite bounds. -/
def encodeRangeText (encodeElement : α → Except String String) : PgRange α →
    Except String String
  | .empty => pure "empty"
  | .span lower upper => do
      let lowerText ← encodeOptionalBound "range lower bound" encodeElement lower
      let upperText ← encodeOptionalBound "range upper bound" encodeElement upper
      let openChar := match lower with
        | some bound => if bound.inclusive then '[' else '('
        | none => '('
      let closeChar := match upper with
        | some bound => if bound.inclusive then ']' else ')'
        | none => ')'
      pure (String.ofList (openChar :: (lowerText.toList ++ ',' :: (upperText.toList ++ [closeChar]))))

private structure MultirangeTextScan where
  ranges : Array String := #[]
  buffer : List Char := []
  inQuotes : Bool := false
  escaped : Bool := false
  inRange : Bool := false
  afterComma : Bool := false
  closed : Bool := false

private def finishMultirangeItem (source : String) (state : MultirangeTextScan) :
    Except String String := do
  let value := String.ofList (Pg.trimAsciiChars state.buffer.reverse)
  unless !value.isEmpty do
    throw s!"multirange: empty item in {source}"
  pure value

private def scanMultirangeText (source : String) : MultirangeTextScan → List Char →
    Except String MultirangeTextScan
  | state, [] => .ok state
  | state, c :: rest =>
      if state.closed then
        .error s!"multirange: trailing characters in {source}"
      else if state.escaped then
        scanMultirangeText source
          { state with buffer := c :: state.buffer, escaped := false }
          rest
      else if state.inQuotes then
        if c == '\\' then
          scanMultirangeText source
            { state with buffer := c :: state.buffer, escaped := true }
            rest
        else if c == '"' then
          scanMultirangeText source
            { state with buffer := c :: state.buffer, inQuotes := false }
            rest
        else
          scanMultirangeText source { state with buffer := c :: state.buffer } rest
      else if c == '\\' && state.inRange then
        scanMultirangeText source
          { state with buffer := c :: state.buffer, escaped := true }
          rest
      else if c == '"' then
        if state.inRange then
          scanMultirangeText source
            { state with buffer := c :: state.buffer, inQuotes := true }
            rest
        else
          .error s!"multirange: quote outside a range in {source}"
      else if c == '{' then
        .error s!"multirange: nested braces are unsupported in {source}"
      else if c == '[' || c == '(' then
        if state.inRange || !(Pg.trimAsciiChars state.buffer.reverse).isEmpty then
          .error s!"multirange: nested or misplaced range opener in {source}"
        else
          scanMultirangeText source
            { state with buffer := c :: state.buffer, inRange := true, afterComma := false }
            rest
      else if c == ']' || c == ')' then
        if state.inRange then
          scanMultirangeText source
            { state with buffer := c :: state.buffer, inRange := false }
            rest
        else
          .error s!"multirange: range closer without opener in {source}"
      else if c == ',' then
        if state.inRange then
          scanMultirangeText source { state with buffer := c :: state.buffer } rest
        else
          match finishMultirangeItem source state with
          | .error message => .error message
          | .ok value =>
              scanMultirangeText source
                { state with
                  ranges := state.ranges.push value
                  buffer := []
                  afterComma := true }
                rest
      else if c == '}' then
        if state.inRange then
          .error s!"multirange: unterminated range in {source}"
        else if (Pg.trimAsciiChars state.buffer.reverse).isEmpty then
          if state.ranges.isEmpty && !state.afterComma then
            scanMultirangeText source { state with closed := true } rest
          else
            .error s!"multirange: trailing comma in {source}"
        else
          match finishMultirangeItem source state with
          | .error message => .error message
          | .ok value =>
              scanMultirangeText source
                { state with ranges := state.ranges.push value, buffer := [], closed := true }
                rest
      else
        scanMultirangeText source
          { state with buffer := c :: state.buffer, afterComma := false }
          rest

private def rawMultirangeText (source : String) : Except String (Array String) :=
  match Pg.trimAsciiChars source.toList with
  | '{' :: rest =>
      match scanMultirangeText source {} rest with
      | .error message => .error message
      | .ok state =>
          if state.closed && !state.inQuotes && !state.escaped && !state.inRange then
            .ok state.ranges
          else
            .error s!"multirange: unterminated literal {source}"
  | _ => .error s!"not a multirange literal: {source}"

/-- Decode multirange text. -/
def decodeMultirangeText (decodeElement : String → Except String α) (source : String) :
    Except String (PgMultirange α) := do
  let ranges ← rawMultirangeText source
  ranges.mapIdxM fun index text =>
    contextual s!"multirange item {index}" (decodeRangeText decodeElement text)

/-- Encode multirange text. -/
def encodeMultirangeText (encodeElement : α → Except String String)
    (ranges : PgMultirange α) : Except String String := do
  let encoded ← ranges.mapIdxM fun index range =>
    contextual s!"multirange item {index}" (encodeRangeText encodeElement range)
  pure (String.ofList ('{' :: (commaSeparatedChars encoded.toList ++ ['}'])))

private def readInt32 (context : String) (bytes : ByteArray) (offset : Nat) :
    Except String Int :=
  match Pg.Protocol.getInt32? bytes offset with
  | some value => .ok value.toInt
  | none => .error s!"{context}: truncated int32 at byte {offset}"

private def readUInt32 (context : String) (bytes : ByteArray) (offset : Nat) :
    Except String UInt32 :=
  match Pg.Protocol.getUInt32? bytes offset with
  | some value => .ok value
  | none => .error s!"{context}: truncated uint32 at byte {offset}"

private structure ArrayBinaryResult (α : Type) where
  values : PgArray α
  offset : Nat
  sawNull : Bool

private def decodeArrayBinaryElements (expectedElementOid : UInt32)
    (decodeElement : UInt32 → ByteArray → Except String α) (bytes : ByteArray) :
    Nat → Nat → PgArray α → Bool → Except String (ArrayBinaryResult α)
  | offset, 0, values, sawNull => .ok { values, offset, sawNull }
  | offset, remaining + 1, values, sawNull => do
      let length ← readInt32 "array element length" bytes offset
      if length == -1 then
        decodeArrayBinaryElements expectedElementOid decodeElement bytes
          (offset + 4) remaining (values.push none) true
      else if length < 0 then
        throw s!"array: invalid element length {length}"
      else
        let size := length.toNat
        unless offset + 4 + size ≤ bytes.size do
          throw s!"array: truncated element payload at byte {offset + 4}"
        let payload := bytes.extract (offset + 4) (offset + 4 + size)
        let value ← contextual s!"array element {values.size}"
          (decodeElement expectedElementOid payload)
        decodeArrayBinaryElements expectedElementOid decodeElement bytes
          (offset + 4 + size) remaining (values.push (some value)) sawNull

/-- Decode PostgreSQL's binary one-dimensional array representation.

The header's element OID must equal `expectedElementOid`.  Dimensions other
than zero or one, non-unit lower bounds, malformed null flags, impossible
lengths, truncation, and trailing bytes are rejected. -/
def decodeArrayBinary (expectedElementOid : UInt32)
    (decodeElement : UInt32 → ByteArray → Except String α) (bytes : ByteArray) :
    Except String (PgArray α) := do
  let dimensions ← readInt32 "array dimensions" bytes 0
  let nullFlag ← readInt32 "array null flag" bytes 4
  let elementOid ← readUInt32 "array element OID" bytes 8
  unless dimensions == 0 || dimensions == 1 do
    throw s!"array: only zero- or one-dimensional values are supported (got {dimensions})"
  unless nullFlag == 0 || nullFlag == 1 do
    throw s!"array: invalid null flag {nullFlag}"
  unless elementOid == expectedElementOid do
    throw s!"array: element OID mismatch: expected {expectedElementOid}, got {elementOid}"
  if dimensions == 0 then
    unless nullFlag == 0 do
      throw "array: empty array cannot carry the null flag"
    unless bytes.size == 12 do
      throw s!"array: trailing bytes after zero-dimensional value ({bytes.size - 12})"
    pure #[]
  else
    let count ← readInt32 "array dimension length" bytes 12
    let lowerBound ← readInt32 "array lower bound" bytes 16
    unless count ≥ 0 do
      throw s!"array: negative dimension length {count}"
    unless lowerBound == 1 do
      throw s!"array: lower bound {lowerBound} is not representable (expected 1)"
    let count := count.toNat
    unless count ≤ (bytes.size - 20) / 4 do
      throw s!"array: element count {count} exceeds the remaining payload"
    let result ← decodeArrayBinaryElements expectedElementOid decodeElement bytes
      20 count #[] false
    unless result.offset == bytes.size do
      throw s!"array: {bytes.size - result.offset} trailing bytes"
    unless (nullFlag == 1) == result.sawNull do
      throw "array: null flag does not match the element payload"
    pure result.values

private def decodeRangeBinaryBound (context : String) (subtypeOid : UInt32)
    (decodeElement : UInt32 → ByteArray → Except String α)
    (bytes : ByteArray) (offset : Nat) : Except String (α × Nat) := do
  let length ← readInt32 s!"{context} length" bytes offset
  unless length ≥ 0 do
    throw s!"range: invalid {context} length {length}"
  let size := length.toNat
  unless offset + 4 + size ≤ bytes.size do
    throw s!"range: truncated {context} payload at byte {offset + 4}"
  let payload := bytes.extract (offset + 4) (offset + 4 + size)
  let value ← contextual s!"range {context}" (decodeElement subtypeOid payload)
  pure (value, offset + 4 + size)

/-- Decode PostgreSQL's binary range representation.

Range payloads do not embed their subtype OID.  The caller therefore supplies
both the generated descriptor's `expectedSubtypeOid` and the catalog-resolved
`actualSubtypeOid`; decoding refuses to proceed unless they agree. -/
def decodeRangeBinary (expectedSubtypeOid actualSubtypeOid : UInt32)
    (decodeElement : UInt32 → ByteArray → Except String α) (bytes : ByteArray) :
    Except String (PgRange α) := do
  unless expectedSubtypeOid == actualSubtypeOid do
    throw s!"range: subtype OID mismatch: expected {expectedSubtypeOid}, got {actualSubtypeOid}"
  unless bytes.size ≥ 1 do
    throw "range: missing flags byte"
  let flags := bytes.get! 0
  let empty := (flags &&& (0x01 : UInt8)) != 0
  let lowerInclusive := (flags &&& (0x02 : UInt8)) != 0
  let upperInclusive := (flags &&& (0x04 : UInt8)) != 0
  let lowerInfinite := (flags &&& (0x08 : UInt8)) != 0
  let upperInfinite := (flags &&& (0x10 : UInt8)) != 0
  unless (flags &&& (0xe0 : UInt8)) == 0 do
    throw s!"range: unsupported or invalid flags {flags}"
  if empty then
    unless flags == 0x01 do
      throw s!"range: empty flag cannot be combined with flags {flags}"
    unless bytes.size == 1 do
      throw s!"range: {bytes.size - 1} trailing bytes after empty value"
    pure .empty
  else
    unless !(lowerInfinite && lowerInclusive) do
      throw "range: infinite lower bound cannot be inclusive"
    unless !(upperInfinite && upperInclusive) do
      throw "range: infinite upper bound cannot be inclusive"
    let (lower, offset) ←
      if lowerInfinite then pure (none, 1)
      else do
        let (value, offset) ← decodeRangeBinaryBound "lower bound" actualSubtypeOid
          decodeElement bytes 1
        pure (some { value, inclusive := lowerInclusive }, offset)
    let (upper, offset) ←
      if upperInfinite then pure (none, offset)
      else do
        let (value, offset) ← decodeRangeBinaryBound "upper bound" actualSubtypeOid
          decodeElement bytes offset
        pure (some { value, inclusive := upperInclusive }, offset)
    unless offset == bytes.size do
      throw s!"range: {bytes.size - offset} trailing bytes"
    pure (.span lower upper)

private def decodeMultirangeBinaryItems (expectedSubtypeOid actualSubtypeOid : UInt32)
    (decodeElement : UInt32 → ByteArray → Except String α) (bytes : ByteArray) :
    Nat → Nat → PgMultirange α → Except String (PgMultirange α × Nat)
  | offset, 0, values => .ok (values, offset)
  | offset, remaining + 1, values => do
      let length ← readInt32 "multirange item length" bytes offset
      unless length > 0 do
        throw s!"multirange: invalid item length {length}"
      let size := length.toNat
      unless offset + 4 + size ≤ bytes.size do
        throw s!"multirange: truncated item payload at byte {offset + 4}"
      let payload := bytes.extract (offset + 4) (offset + 4 + size)
      let value ← contextual s!"multirange item {values.size}"
        (decodeRangeBinary expectedSubtypeOid actualSubtypeOid decodeElement payload)
      decodeMultirangeBinaryItems expectedSubtypeOid actualSubtypeOid decodeElement bytes
        (offset + 4 + size) remaining (values.push value)

/-- Decode PostgreSQL's binary multirange representation, validating its
subtype identity, item count, every item length, each nested range, and final
payload consumption. -/
def decodeMultirangeBinary (expectedSubtypeOid actualSubtypeOid : UInt32)
    (decodeElement : UInt32 → ByteArray → Except String α) (bytes : ByteArray) :
    Except String (PgMultirange α) := do
  unless expectedSubtypeOid == actualSubtypeOid do
    throw s!"multirange: subtype OID mismatch: expected {expectedSubtypeOid}, got {actualSubtypeOid}"
  let count ← readInt32 "multirange count" bytes 0
  unless count ≥ 0 do
    throw s!"multirange: negative item count {count}"
  let count := count.toNat
  unless count ≤ (bytes.size - 4) / 5 do
    throw s!"multirange: item count {count} exceeds the remaining payload"
  let (values, offset) ← decodeMultirangeBinaryItems expectedSubtypeOid actualSubtypeOid
    decodeElement bytes 4 count #[]
  unless offset == bytes.size do
    throw s!"multirange: {bytes.size - offset} trailing bytes"
  pure values

end Pgx.Typed
