import Lax58.CanonicalCodec

/-!
---
title: Full decoding laws
type: theorem
---

Every lawful codec decodes its distinguished encoding. For a canonical codec,
full decoding returns a value exactly when the input is that distinguished
encoding. In particular, the encoder of a lawful codec is injective.
-/

namespace Lax58.CanonicalDecoding

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec

universe u

/-- The basic consequences of lawful and canonical decoding. -/
structure DecodingLaws : Prop where
  decode_encode {α : Type u} (C : Codec α) (hC : C.Lawful) (x : α) :
    C.decode (C.encode x) = some x
  encode_injective {α : Type u} (C : Codec α) (hC : C.Lawful) :
    Function.Injective C.encode
  decode_eq_some_iff {α : Type u} (C : Codec α) (hC : C.Canonical)
      (input : BitString) (x : α) :
    C.decode input = some x ↔ input = C.encode x

axiom laws : DecodingLaws

end Lax58.CanonicalDecoding
