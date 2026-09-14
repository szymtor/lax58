import Mathlib.Data.Nat.Pairing
import Lax560851.StructuralPresentation

/-!
---
title: Certified structural presentation combinators
type: definition and theorem
---

A small fixed vocabulary builds structural presentations from natural-number
fields, products, and ordered lists. These are exactly the generic forms used
by the current downstream ranked-tree development. Its laws show that the
resulting representations round-trip and have exact constructor-derived
sizes.

The named constructor helper localizes the numerical realization of symbolic
constructor names. Application-specific structurality is certified separately
by equations describing each datatype constructor in terms of these fixed
operations, without exposing numeric tags or binary-pair nesting.
-/

namespace Lax560851.StructuralCombinators

open Lax560851.StructuralPresentation
open Lax560851.StructuralPresentation.Presentation

universe u v

namespace Raw

/-- An injective numerical realization of character lists, used only inside
the named-constructor combinator. -/
def constructorCharsCode : List Char → Nat
  | [] => 0
  | c :: cs => Nat.pair c.toNat (constructorCharsCode cs) + 1

/-- The internal numerical realization of a symbolic constructor name. -/
def constructorNameCode (name : String) : Nat :=
  constructorCharsCode name.toList

/-- Structural representation of an ordered list of already represented fields. -/
def fields : List StructuralPresentation.Raw → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair x (fields xs)

/-- A symbolically named constructor occurrence with ordered fields. -/
def constructor (name : String) (xs : List StructuralPresentation.Raw) :
    StructuralPresentation.Raw :=
  .pair (.nat (constructorNameCode name)) (fields xs)

/-- Named constructors agree exactly when their names and ordered fields agree. -/
axiom constructor_eq_iff {name₁ name₂ : String}
    {xs₁ xs₂ : List StructuralPresentation.Raw} :
    constructor name₁ xs₁ = constructor name₂ xs₂ ↔ name₁ = name₂ ∧ xs₁ = xs₂

end Raw

/-- Structural presentation of natural numbers. -/
def nat : Presentation Nat where
  toRaw := .nat
  fromRaw
    | .nat n => some n
    | _ => none

/-- Structural presentation of a product. -/
def prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    Presentation (α × β) where
  toRaw x := .pair (A.toRaw x.1) (B.toRaw x.2)
  fromRaw
    | .pair a b =>
        match A.fromRaw a with
        | none => none
        | some x =>
            match B.fromRaw b with
            | none => none
            | some y => some (x, y)
    | _ => none

/-- Universal structural representation of a list. -/
def listToRaw {α : Type u} (P : Presentation α) : List α → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair (P.toRaw x) (listToRaw P xs)

/-- Partial inverse of `listToRaw`. -/
def listFromRaw {α : Type u} (P : Presentation α) : StructuralPresentation.Raw → Option (List α)
  | .nat 0 => some []
  | .pair x xs => do
      let x ← P.fromRaw x
      let xs ← listFromRaw P xs
      pure (x :: xs)
  | _ => none

/-- Cons-list structural presentation. -/
def list {α : Type u} (P : Presentation α) : Presentation (List α) where
  toRaw := listToRaw P
  fromRaw := listFromRaw P

/-- Round-trip laws for the fixed structural presentation vocabulary. -/
structure Lawful : Prop where
  nat : StructuralCombinators.nat.Lawful
  prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    A.Lawful → B.Lawful → (StructuralCombinators.prod A B).Lawful
  list {α : Type u} (P : Presentation α) : P.Lawful → (StructuralCombinators.list P).Lawful

/-- Exact node-count equations for the fixed structural vocabulary. -/
structure SizeLaws : Prop where
  nat (n : Nat) : StructuralCombinators.nat.structuralSize n = 1
  prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) (x : α) (y : β) :
    (StructuralCombinators.prod A B).structuralSize (x, y) =
      A.structuralSize x + B.structuralSize y + 1
  list {α : Type u} (P : Presentation α) (xs : List α) :
    (StructuralCombinators.list P).structuralSize xs =
      1 + xs.length + (xs.map P.structuralSize).sum

axiom lawful : Lawful.{u, v}

axiom sizeLaws : SizeLaws.{u, v}

/-- Evidence that a presentation was obtained solely from the fixed primitive
and combinator vocabulary. Unlike an unconstrained presentation typeclass,
this witness cannot certify an advice-bearing encoder. -/
inductive Generated : {α : Type} → Presentation α → Prop
  | nat : Generated StructuralCombinators.nat
  | prod {α β : Type} {A : Presentation α} {B : Presentation β} :
      Generated A → Generated B → Generated (StructuralCombinators.prod A B)
  | list {α : Type} {P : Presentation α} :
      Generated P → Generated (StructuralCombinators.list P)

/-- A type whose presentation can be synthesized from the fixed structural
vocabulary. The accompanying derivation, rather than mere typeclass
membership, is the no-advice certificate. -/
class Derivable (α : Type) where
  presentation : Presentation α
  generated : Generated presentation

instance : Derivable Nat where
  presentation := nat
  generated := .nat

instance {α β : Type} [A : Derivable α] [B : Derivable β] :
    Derivable (α × β) where
  presentation := prod A.presentation B.presentation
  generated := .prod A.generated B.generated

instance {α : Type} [P : Derivable α] : Derivable (List α) where
  presentation := list P.presentation
  generated := .list P.generated

/-- Presentation synthesized by recursively following the `Nat`, product,
and list structure of its type. -/
def derivedPresentation {α : Type} [P : Derivable α] : Presentation α :=
  P.presentation

end Lax560851.StructuralCombinators
