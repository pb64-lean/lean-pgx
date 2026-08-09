import Pgx.Typed

/-! Reusable codecs for extension-owned PostgreSQL types used by the fixture. -/

namespace AppDb.ExtensionCodecs.Citext

def descriptor : Pgx.Typed.StaticTypeDesc := {
  key := { schema := "app", name := "citext", kind := .base }
}

def codec : Pgx.Typed.ResolvedCodec String where
  expected := descriptor
  encode _ _ value := pure { format := 0, value := some value.toUTF8 }
  decode _ _ format value := do
    unless format == 0 || format == 1 do
      throw (.decode "unsupported wire format for app.citext")
    let some bytes := value
      | throw (.decode "unexpected NULL for app.citext")
    let some text := String.fromUTF8? bytes
      | throw (.decode "app.citext value is not UTF-8")
    pure text

end AppDb.ExtensionCodecs.Citext
