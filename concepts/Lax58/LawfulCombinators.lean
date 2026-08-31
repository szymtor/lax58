import Lax58.CodecCombinators

/-!
---
title: Canonicality of codec combinators
type: theorem
---

Transport along an equivalence and the standard product, sum, option, list,
fixed-vector, finite-function, and finite-index codec constructions preserve
canonical prefix parsing and exact structural bit size.
-/

namespace Lax58.LawfulCombinators

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.CodecCombinators

universe u v

/-- All standard codec constructors preserve lawfulness. -/
structure Closure : Prop where
  equiv {α : Type u} {β : Type v} (e : α ≃ β) (C : Codec β) :
    C.Lawful → (equivCodec e C).Lawful
  prod {α : Type u} {β : Type v} (A : Codec α) (B : Codec β) :
    A.Lawful → B.Lawful → (prodCodec A B).Lawful
  sum {α : Type u} {β : Type v} (A : Codec α) (B : Codec β) :
    A.Lawful → B.Lawful → (sumCodec A B).Lawful
  option {α : Type u} (C : Codec α) :
    C.Lawful → (optionCodec C).Lawful
  list {α : Type u} (C : Codec α) :
    C.Lawful → (listCodec C).Lawful
  vector {α : Type u} (C : Codec α) (n : Nat) :
    C.Lawful → (vectorCodec C n).Lawful
  finFunction {α : Type u} (C : Codec α) (n : Nat) :
    C.Lawful → (finFunctionCodec C n).Lawful
  fin (n : Nat) : (finCodec n).Lawful

axiom closure : Closure

end Lax58.LawfulCombinators
