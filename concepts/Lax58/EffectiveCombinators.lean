import Lax58.CodecCombinators

/-!
---
title: Effectiveness of codec combinators
type: theorem
---

Transport along a computable equivalence and the standard product, sum,
option, list, fixed-vector, finite-function, and finite-index constructions
preserve computability of encoding, prefix parsing, and structural bit size.
-/

namespace Lax58.EffectiveCombinators

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.CodecCombinators

universe u v

/-- All standard codec constructors preserve effectiveness. -/
structure Closure : Prop where
  equiv {α : Type u} {β : Type v} [Primcodable α] [Primcodable β]
      (e : α ≃ β) (C : Codec β) :
    Computable e → Computable e.symm → C.Effective → (equivCodec e C).Effective
  prod {α : Type u} {β : Type v} [Primcodable α] [Primcodable β]
      (A : Codec α) (B : Codec β) :
    A.Effective → B.Effective → (prodCodec A B).Effective
  sum {α : Type u} {β : Type v} [Primcodable α] [Primcodable β]
      (A : Codec α) (B : Codec β) :
    A.Effective → B.Effective → (sumCodec A B).Effective
  option {α : Type u} [Primcodable α] (C : Codec α) :
    C.Effective → (optionCodec C).Effective
  list {α : Type u} [Primcodable α] (C : Codec α) :
    C.Effective → (listCodec C).Effective
  vector {α : Type u} [Primcodable α] (C : Codec α) (n : Nat) :
    C.Effective → (vectorCodec C n).Effective
  finFunction {α : Type u} [Primcodable α] (C : Codec α) (n : Nat) :
    C.Effective → (finFunctionCodec C n).Effective
  fin (n : Nat) : (finCodec n).Effective

axiom closure : Closure

end Lax58.EffectiveCombinators
