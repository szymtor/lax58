import Mathlib.Data.Vector.Basic
import Lax58.StructuralPresentation

/-!
---
title: Certified structural presentation combinators
type: definition and theorem
---

A small fixed vocabulary builds structural presentations from primitive
fields, constructor choices, products, lists, finite indices, and finite
families. Its laws show that the resulting representations round-trip, are
faithful by round trip, and have exact constructor-derived sizes.

The raw constructor helper localizes the arbitrary numerical realization of
constructor names. Application-specific structurality is certified separately
by equations describing each datatype constructor in terms of these fixed
operations.
-/

namespace Lax58.StructuralCombinators

open Lax58.StructuralPresentation
open Lax58.StructuralPresentation.Presentation

universe u v

namespace Raw

/-- Structural representation of an ordered list of already represented fields. -/
def fields : List StructuralPresentation.Raw → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair x (fields xs)

/-- A constructor occurrence with a constructor number and ordered fields.
Datatype-specific concepts should wrap constructor numbers behind named
constructor equations. -/
def constructor (tag : Nat) (xs : List StructuralPresentation.Raw) :
    StructuralPresentation.Raw :=
  .pair (.nat tag) (fields xs)

end Raw

/-- Transport a presentation across an equivalence. Its structural use is
safe only when the equivalence itself is characterized constructor by
constructor. -/
def equiv {α : Type u} {β : Type v} (e : α ≃ β) (P : Presentation β) : Presentation α where
  toRaw x := P.toRaw (e x)
  fromRaw raw := (P.fromRaw raw).map e.symm

/-- Structural presentation of the unit type. -/
def unit : Presentation Unit where
  toRaw _ := .nat 0
  fromRaw
    | .nat 0 => some ()
    | _ => none

/-- Structural presentation of Boolean values. -/
def bool : Presentation Bool where
  toRaw
    | false => .nat 0
    | true => .nat 1
  fromRaw
    | .nat 0 => some false
    | .nat 1 => some true
    | _ => none

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

/-- Tagged structural presentation of a disjoint sum. -/
def sum {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    Presentation (α ⊕ β) where
  toRaw
    | .inl x => .pair (.nat 0) (A.toRaw x)
    | .inr y => .pair (.nat 1) (B.toRaw y)
  fromRaw
    | .pair (.nat 0) raw => (A.fromRaw raw).map Sum.inl
    | .pair (.nat 1) raw => (B.fromRaw raw).map Sum.inr
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

/-- Range-checked structural presentation of a finite index. -/
def fin (n : Nat) : Presentation (Fin n) where
  toRaw i := .nat i.val
  fromRaw
    | .nat i => if h : i < n then some ⟨i, h⟩ else none
    | _ => none

/-- Fixed-length vector presentation induced by the list presentation. -/
def vector {α : Type u} (P : Presentation α) (n : Nat) :
    Presentation (List.Vector α n) where
  toRaw xs := listToRaw P xs.1
  fromRaw raw := do
    let xs ← listFromRaw P raw
    if h : xs.length = n then pure ⟨xs, h⟩ else none

/-- Functions on `Fin n`, represented in increasing argument order. This
specifies representation content only; it does not assert that evaluating or
enumerating an arbitrary Lean function is cheap. -/
def finFunction {α : Type u} (P : Presentation α) (n : Nat) : Presentation (Fin n → α) :=
  equiv (Equiv.vectorEquivFin α n).symm (vector P n)

/-- Round-trip laws for the fixed structural presentation vocabulary. -/
structure Lawful : Prop where
  equiv {α : Type u} {β : Type v} (e : α ≃ β) (P : Presentation β) :
    P.Lawful → (StructuralCombinators.equiv e P).Lawful
  unit : StructuralCombinators.unit.Lawful
  bool : StructuralCombinators.bool.Lawful
  nat : StructuralCombinators.nat.Lawful
  prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    A.Lawful → B.Lawful → (StructuralCombinators.prod A B).Lawful
  sum {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    A.Lawful → B.Lawful → (StructuralCombinators.sum A B).Lawful
  list {α : Type u} (P : Presentation α) : P.Lawful → (StructuralCombinators.list P).Lawful
  fin (n : Nat) : (StructuralCombinators.fin n).Lawful
  vector {α : Type u} (P : Presentation α) (n : Nat) :
    P.Lawful → (StructuralCombinators.vector P n).Lawful
  finFunction {α : Type u} (P : Presentation α) (n : Nat) :
    P.Lawful → (StructuralCombinators.finFunction P n).Lawful

/-- Exact node-count equations for the fixed structural vocabulary. -/
structure SizeLaws : Prop where
  equiv {α : Type u} {β : Type v} (e : α ≃ β) (P : Presentation β) (x : α) :
    (StructuralCombinators.equiv e P).structuralSize x = P.structuralSize (e x)
  unit (x : Unit) : StructuralCombinators.unit.structuralSize x = 1
  bool (b : Bool) : StructuralCombinators.bool.structuralSize b = 1
  nat (n : Nat) : StructuralCombinators.nat.structuralSize n = 1
  prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) (x : α) (y : β) :
    (StructuralCombinators.prod A B).structuralSize (x, y) =
      A.structuralSize x + B.structuralSize y + 1
  sum_inl {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) (x : α) :
    (StructuralCombinators.sum A B).structuralSize (.inl x) = A.structuralSize x + 2
  sum_inr {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) (y : β) :
    (StructuralCombinators.sum A B).structuralSize (.inr y) = B.structuralSize y + 2
  list {α : Type u} (P : Presentation α) (xs : List α) :
    (StructuralCombinators.list P).structuralSize xs =
      1 + xs.length + (xs.map P.structuralSize).sum
  fin (n : Nat) (i : Fin n) : (StructuralCombinators.fin n).structuralSize i = 1
  vector {α : Type u} (P : Presentation α) (n : Nat) (xs : List.Vector α n) :
    (StructuralCombinators.vector P n).structuralSize xs =
      1 + n + (xs.toList.map P.structuralSize).sum
  finFunction {α : Type u} (P : Presentation α) (n : Nat) (f : Fin n → α) :
    (StructuralCombinators.finFunction P n).structuralSize f =
      1 + n + (List.ofFn fun i => P.structuralSize (f i)).sum

axiom lawful : Lawful.{u, v}

axiom sizeLaws : SizeLaws.{u, v}

end Lax58.StructuralCombinators
