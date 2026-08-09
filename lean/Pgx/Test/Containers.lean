import Pgx.Typed.Containers

open Pgx.Typed

private def parseInt (text : String) : Except String Int :=
  match text.toInt? with
  | some value => .ok value
  | none => .error s!"not an integer: {text}"

private def renderInt (value : Int) : Except String String :=
  pure (toString value)

private def parseString (text : String) : Except String String := pure text
private def renderString (text : String) : Except String String := pure text

private def isError (result : Except String α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def okEq [BEq α] (result : Except String α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def i32 (value : Int) : ByteArray :=
  Pg.Protocol.putInt32 ByteArray.empty (Int32.ofInt value)

private def u32 (value : UInt32) : ByteArray :=
  Pg.Protocol.putUInt32 ByteArray.empty value

private def binaryElement : Option ByteArray → ByteArray
  | none => i32 (-1)
  | some payload => i32 payload.size ++ payload

private def arrayBinary (dimensions nullFlag : Int) (elementOid : UInt32)
    (dimensionData payload : ByteArray) : ByteArray :=
  i32 dimensions ++ i32 nullFlag ++ u32 elementOid ++ dimensionData ++ payload

private def rangeBinary (flags : UInt8) (payload : ByteArray := ByteArray.empty) : ByteArray :=
  ByteArray.empty.push flags ++ payload

private def multirangeBinary (ranges : Array ByteArray) : ByteArray :=
  ranges.foldl (fun out value => out ++ i32 value.size ++ value) (i32 ranges.size)

private def decodeBinaryInt (oid : UInt32) (bytes : ByteArray) : Except String Int := do
  unless oid == 23 do throw s!"unexpected int OID {oid}"
  let some text := String.fromUTF8? bytes | throw "integer payload is not UTF-8"
  parseInt text

private def span12 : PgRange Int :=
  .span (some { value := 1, inclusive := true })
    (some { value := 2, inclusive := false })

private def textContainerTests : IO Unit := do
  assert! okEq (decodeArrayText parseInt "{1,NULL, -3 }") #[some 1, none, some (-3)]
  assert! okEq (decodeArrayText parseString "{\"NULL\",NULL,\"a,b\",\"{x}\",\"q\\\"z\",\"c\\\\d\"}")
    #[some "NULL", none, some "a,b", some "{x}", some "q\"z", some "c\\d"]
  let arrayStrings : PgArray String :=
    #[some "", some "NULL", none, some "a,b", some "{nested}", some "q\"\\z"]
  let arrayText ← match encodeArrayText renderString arrayStrings with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  assert! okEq (decodeArrayText parseString arrayText) arrayStrings
  assert! isError (decodeArrayText parseInt "{{1},{2}}")
  assert! isError (decodeArrayText parseInt "{1,{2}}")
  assert! isError (decodeArrayText parseInt "{1,}")
  assert! isError (decodeArrayText parseInt "{,1}")
  assert! isError (decodeArrayText parseInt "{\"1\"x}")
  assert! isError (decodeArrayText parseInt "{\"1}")
  assert! isError (decodeArrayText parseInt "{1}junk")

  assert! okEq (decodeRangeText parseInt "[1,2)") span12
  assert! okEq (decodeRangeText parseInt "empty") (PgRange.empty : PgRange Int)
  assert! okEq (decodeRangeText parseInt "(,9]")
    (.span none (some { value := 9, inclusive := true }))
  let stringRange : PgRange String :=
    .span (some { value := "a,b", inclusive := false })
      (some { value := "q\"\\z", inclusive := true })
  let rangeText ← match encodeRangeText renderString stringRange with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  assert! okEq (decodeRangeText parseString rangeText) stringRange
  assert! isError (decodeRangeText parseInt "[1]")
  assert! isError (decodeRangeText parseInt "[1,2,3)")
  assert! isError (decodeRangeText parseInt "[,)" )
  assert! isError (decodeRangeText parseInt "(,]")
  assert! isError (decodeRangeText parseInt "[1,2)junk")
  assert! isError (decodeRangeText parseInt "[\"1,2)")

  let ranges : PgMultirange Int := #[span12, .empty, .span none none]
  let multirangeText ← match encodeMultirangeText renderInt ranges with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  assert! okEq (decodeMultirangeText parseInt multirangeText) ranges
  assert! okEq (decodeMultirangeText parseInt "{[1,2),(5,9]}")
    #[span12, .span (some { value := 5, inclusive := false })
      (some { value := 9, inclusive := true })]
  assert! okEq (decodeMultirangeText parseString "{[a\\]b,z)}")
    #[.span (some { value := "a]b", inclusive := true })
      (some { value := "z", inclusive := false })]
  assert! isError (decodeMultirangeText parseInt "{{[1,2)}}")
  assert! isError (decodeMultirangeText parseInt "{[1,2),}")
  assert! isError (decodeMultirangeText parseInt "{,[1,2)}")
  assert! isError (decodeMultirangeText parseInt "{[1,2}")
  assert! isError (decodeMultirangeText parseInt "{[1,2)}junk")

private def binaryArrayTests : IO Unit := do
  let payload := binaryElement (some "1".toUTF8) ++ binaryElement none ++
    binaryElement (some "-3".toUTF8)
  let valid := arrayBinary 1 1 23 (i32 3 ++ i32 1) payload
  assert! okEq (decodeArrayBinary 23 decodeBinaryInt valid) #[some 1, none, some (-3)]
  assert! okEq (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 0 0 23 ByteArray.empty ByteArray.empty)) #[]
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 2 0 23 (i32 1 ++ i32 1 ++ i32 1 ++ i32 1)
      (binaryElement (some "1".toUTF8))))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary (-1) 0 23 ByteArray.empty ByteArray.empty))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 1 0 25 (i32 0 ++ i32 1) ByteArray.empty))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 1 0 23 (i32 0 ++ i32 0) ByteArray.empty))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 1 2 23 (i32 0 ++ i32 1) ByteArray.empty))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 1 0 23 (i32 1 ++ i32 1) (i32 (-2))))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 1 0 23 (i32 1 ++ i32 1) (i32 4 ++ "1".toUTF8)))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 1 0 23 (i32 1 ++ i32 1) (binaryElement none)))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt (valid.push 0))
  assert! isError (decodeArrayBinary 23 decodeBinaryInt
    (arrayBinary 0 0 23 ByteArray.empty (ByteArray.empty.push 0)))

private def binaryRangeTests : IO Unit := do
  let valid := rangeBinary 0x02
    (binaryElement (some "1".toUTF8) ++ binaryElement (some "2".toUTF8))
  assert! okEq (decodeRangeBinary 23 23 decodeBinaryInt valid) span12
  assert! okEq (decodeRangeBinary 23 23 decodeBinaryInt (rangeBinary 0x01))
    (PgRange.empty : PgRange Int)
  let lowerOnly := rangeBinary 0x12 (binaryElement (some "1".toUTF8))
  assert! okEq (decodeRangeBinary 23 23 decodeBinaryInt lowerOnly)
    (.span (some { value := 1, inclusive := true }) none)
  assert! isError (decodeRangeBinary 23 25 decodeBinaryInt valid)
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt ByteArray.empty)
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt (rangeBinary 0x03))
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt (rangeBinary 0x22))
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt (rangeBinary 0x0a))
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt (rangeBinary 0x14))
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt (rangeBinary 0x00 (i32 (-1))))
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt
    (rangeBinary 0x00 (i32 3 ++ "1".toUTF8)))
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt (valid.push 0))
  assert! isError (decodeRangeBinary 23 23 decodeBinaryInt (rangeBinary 0x01 (ByteArray.empty.push 0)))

private def binaryMultirangeTests : IO Unit := do
  let first := rangeBinary 0x02
    (binaryElement (some "1".toUTF8) ++ binaryElement (some "2".toUTF8))
  let empty := rangeBinary 0x01
  let valid := multirangeBinary #[first, empty]
  assert! okEq (decodeMultirangeBinary 23 23 decodeBinaryInt valid)
    #[span12, .empty]
  assert! okEq (decodeMultirangeBinary 23 23 decodeBinaryInt (i32 0)) #[]
  assert! isError (decodeMultirangeBinary 23 25 decodeBinaryInt valid)
  assert! isError (decodeMultirangeBinary 23 23 decodeBinaryInt (i32 (-1)))
  assert! isError (decodeMultirangeBinary 23 23 decodeBinaryInt (i32 1 ++ i32 0))
  assert! isError (decodeMultirangeBinary 23 23 decodeBinaryInt
    (i32 1 ++ i32 5 ++ rangeBinary 0x01))
  assert! isError (decodeMultirangeBinary 23 23 decodeBinaryInt
    (multirangeBinary #[rangeBinary 0x03]))
  assert! isError (decodeMultirangeBinary 23 23 decodeBinaryInt (valid.push 0))

def main : IO UInt32 := do
  textContainerTests
  binaryArrayTests
  binaryRangeTests
  binaryMultirangeTests
  return 0
