import Mathlib.Data.Finset.Sort
import Lax58.CodecCombinators

/-!
---
title: Codecs for finite multisets and sets
type: definition
---

A finite multiset or set over a linearly ordered type is encoded by sorting its
elements and applying the list codec. Decoding is deliberately permissive: it
accepts every list order, and finite-set decoding also ignores repetitions.
Thus these codecs round-trip and have a distinguished encoding, but are not
claimed to be canonical. Applications needing a unique accepted representation
should use an explicitly ordered list.
-/

namespace Lax58.FiniteCollections

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.CodecCombinators

universe u

/-- List codec for finite multisets, with a sorted distinguished encoding. -/
def multisetCodec {α : Type u} [LinearOrder α] (C : Codec α) : Codec (Multiset α) where
  encode s := (listCodec C).encode (s.sort (· ≤ ·))
  parse input := do
    let (xs, suffix) ← (listCodec C).parse input
    pure (xs, suffix)
  size s := (listCodec C).size (s.sort (· ≤ ·))

/-- List codec for finite sets, with a sorted distinguished encoding. The
decoder accepts arbitrary order and ignores repeated elements. -/
def finsetCodec {α : Type u} [LinearOrder α] (C : Codec α) : Codec (Finset α) where
  encode s := (listCodec C).encode (s.sort (· ≤ ·))
  parse input := do
    let (xs, suffix) ← (listCodec C).parse input
    pure (xs.toFinset, suffix)
  size s := (listCodec C).size (s.sort (· ≤ ·))

/-- Both unordered-collection codecs preserve round-trip correctness. -/
structure CollectionCodecsLawful : Prop where
  multiset {α : Type u} [LinearOrder α] (C : Codec α) (hC : C.Lawful) :
    (multisetCodec C).Lawful
  finset {α : Type u} [LinearOrder α] (C : Codec α) (hC : C.Lawful) :
    (finsetCodec C).Lawful

axiom collectionCodecs_lawful : CollectionCodecsLawful

end Lax58.FiniteCollections
