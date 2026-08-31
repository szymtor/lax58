import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List

/-!
---
title: Canonical prefix codecs
type: definition
---

A codec represents values by finite bit strings. Its parser reads one value
from the beginning of a string and returns the unused suffix. A lawful codec
has three properties: parsing an encoding in front of an arbitrary suffix
recovers both the value and that suffix; every successful parse consumes
exactly the canonical encoding of its result; and the encoding length equals
the declared structural bit size.

Full decoding accepts precisely complete canonical encodings. Computability
of a map between presented types means that one computable operation on bit
strings transforms every canonical input encoding into the canonical encoding
of its image. Nothing is required on malformed input strings.
-/

namespace Lax58.CanonicalCodec

universe u v w

/-- A finite string over the fixed binary alphabet. -/
abbrev BitString := List Bool

/-- An encoder, prefix parser, and structural bit-size measure for a type. -/
structure Codec (α : Type u) where
  encode : α → BitString
  parse : BitString → Option (α × BitString)
  size : α → Nat

namespace Codec

/-- Decode a complete string, rejecting a valid prefix followed by garbage. -/
def decode {α : Type u} (C : Codec α) (input : BitString) : Option α :=
  match C.parse input with
  | some (x, []) => some x
  | _ => none

/-- Correctness, canonicality, and the exact size law for a codec. -/
structure Lawful {α : Type u} (C : Codec α) : Prop where
  parse_encode_append :
    ∀ (x : α) (suffix : BitString),
      C.parse (C.encode x ++ suffix) = some (x, suffix)
  parse_canonical :
    ∀ {input : BitString} {x : α} {suffix : BitString},
      C.parse input = some (x, suffix) → input = C.encode x ++ suffix
  encode_length : ∀ x : α, (C.encode x).length = C.size x

/-- Encoding followed by full decoding is the identity. -/
axiom decode_encode {α : Type u} (C : Codec α) (hC : C.Lawful) (x : α) :
  C.decode (C.encode x) = some x

/-- Full decoding succeeds exactly on canonical encodings. -/
axiom decode_eq_some_iff {α : Type u} (C : Codec α) (hC : C.Lawful)
    (input : BitString) (x : α) :
  C.decode input = some x ↔ input = C.encode x

/-- A lawful encoder is injective. -/
axiom encode_injective {α : Type u} (C : Codec α) (hC : C.Lawful) :
  Function.Injective C.encode

/-- The encoder, parser, and size function are computable with respect to a
chosen `Primcodable` presentation of the value type. -/
def Effective {α : Type u} [Primcodable α] (C : Codec α) : Prop :=
  Computable C.encode ∧ Computable C.parse ∧ Computable C.size

/-- Full decoding is computable whenever the prefix parser is computable. -/
axiom decode_computable {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) :
  Computable C.decode

/-- A string program computes `f` through codecs `C` and `D` when it maps
every canonical encoding of `x` to the canonical encoding of `f x`. -/
def ComputableMap {α : Type u} {β : Type v} (C : Codec α) (D : Codec β)
    (f : α → β) : Prop :=
  ∃ program : BitString → Option BitString,
    Computable program ∧
      ∀ x : α, program (C.encode x) = some (D.encode (f x))

/-- Identity maps are computable through every codec. -/
axiom computableMap_id {α : Type u} (C : Codec α) :
  ComputableMap C C id

/-- An ordinarily computable map is computable on strings through effective
input and output codecs. -/
axiom computableMap_of_computable {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (C : Codec α) (D : Codec β)
    (hC : C.Effective) (hD : D.Effective) {f : α → β} (hf : Computable f) :
  ComputableMap C D f

/-- Maps computable through canonical codecs are closed under composition. -/
axiom ComputableMap.comp {α : Type u} {β : Type v} {γ : Type w}
    {A : Codec α} {B : Codec β} {C : Codec γ} {f : α → β} {g : β → γ}
    (hg : ComputableMap B C g) (hf : ComputableMap A B f) :
  ComputableMap A C (g ∘ f)

end Codec

end Lax58.CanonicalCodec
