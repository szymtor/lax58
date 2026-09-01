import Lax58.CanonicalCodec

/-!
---
title: Computable maps through canonical encodings
type: theorem
---

An ordinary computable function between `Primcodable` types is realized by a
single computable operation on bit strings whenever the chosen input and
output codecs have computable encoders and parsers. On distinguished inputs
the operation produces the distinguished encoding of the function value;
behavior on alternative or malformed strings is immaterial.
-/

namespace Lax58.ComputableMaps

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec

universe u v

axiom computableMap_of_computable {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (C : Codec α) (D : Codec β)
    (hC : C.Lawful) (hCE : C.Effective) (hDE : D.Effective)
    {f : α → β} (hf : Computable f) :
  ComputableMap C D f

end Lax58.ComputableMaps
