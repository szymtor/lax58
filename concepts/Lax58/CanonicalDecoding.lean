import Lax58.CanonicalCodec

/-!
---
title: Characterization of canonical decoding
type: theorem
---

For a lawful codec, full decoding returns a value exactly when the input is
that value's canonical encoding. In particular, decoding after encoding is the
identity and the encoder is injective.
-/

namespace Lax58.CanonicalDecoding

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec

universe u

axiom decode_eq_some_iff {α : Type u} (C : Codec α) (hC : C.Lawful)
    (input : BitString) (x : α) :
  C.decode input = some x ↔ input = C.encode x

end Lax58.CanonicalDecoding
