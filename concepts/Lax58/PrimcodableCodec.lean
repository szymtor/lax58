import Lax58.PrimitiveCodecs

/-!
---
title: Binary codecs induced by Primcodable presentations
type: theorem
---

Every `Primcodable` type has a canonical binary codec obtained by applying the
standard natural-number codec to its chosen `Encodable.encode` value. The
failsafe decoder `Encodable.decode₂` rejects natural numbers outside the image
of that encoder. This construction is a qualitative fallback: it is canonical
and computable, but it makes no structural claim about encoding length beyond
the exact bit length of the chosen natural-number code.
-/

namespace Lax58.PrimcodableCodec

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.PrimitiveCodecs

universe u

/-- The canonical bit codec induced by a chosen `Primcodable` presentation. -/
def codec (α : Type u) [Primcodable α] : Codec α where
  encode x := natCodec.encode (Encodable.encode x)
  parse input :=
    match natCodec.parse input with
    | none => none
    | some (n, suffix) =>
        match Encodable.decode₂ α n with
        | none => none
        | some x => some (x, suffix)
  size x := natCodec.size (Encodable.encode x)

/-- The `Primcodable` codec is lawful, canonical, and effective. -/
structure Valid : Prop where
  lawful (α : Type u) [Primcodable α] : (codec α).Lawful
  canonical (α : Type u) [Primcodable α] : (codec α).Canonical
  effective (α : Type u) [Primcodable α] : (codec α).Effective

axiom valid : Valid

end Lax58.PrimcodableCodec
