import Mathlib.Data.Finset.Sort
import Lax58.CodecCombinators

/-!
---
title: Canonical codecs for finite sets
type: definition
---

A finite set over a linearly ordered type is encoded as the canonical list of
its elements in increasing order. Decoding checks both sortedness and absence
of duplicates before constructing the set. Consequently the representation is
independent of the internal order used by `Finset`, is canonical, and has the
same exact structural size as the corresponding list encoding.
-/

namespace Lax58.FiniteCollections

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.CodecCombinators

universe u

/-- Increasing-list codec for finite sets. -/
def finsetCodec {α : Type u} [LinearOrder α] (C : Codec α) : Codec (Finset α) where
  encode s := (listCodec C).encode (s.sort (· ≤ ·))
  parse input := do
    let (xs, suffix) ← (listCodec C).parse input
    if xs.Pairwise (· ≤ ·) ∧ xs.Nodup then
      pure (xs.toFinset, suffix)
    else
      none
  size s := (listCodec C).size (s.sort (· ≤ ·))

axiom finsetCodec_lawful {α : Type u} [LinearOrder α]
    (C : Codec α) (hC : C.Lawful) :
  (finsetCodec C).Lawful

end Lax58.FiniteCollections
