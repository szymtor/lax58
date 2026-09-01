import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Vector.Basic
import Lax58.PrimitiveCodecs

/-!
---
title: Structural presentations of finite data
type: definition
---

Finite data may be presented through one universal shape: binary trees with
natural-number leaves. A presentation consists only of maps to and from this
shape. Its structural size is the number of shape nodes.

A structural encoding standard supplies a prefix codec for the universal
shape, turns presentations into binary codecs, and provides presentations for
the usual finitary type constructors. The interface deliberately leaves tag
choices, parser implementations, fuel management, sorting algorithms, and
other serialization details unspecified.
-/

namespace Lax58.StructuralEncoding

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.PrimitiveCodecs

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

/-- Number of nodes in a universal structural representation. -/
def nodes : Raw → Nat
  | .nat _ => 1
  | .pair a b => nodes a + nodes b + 1

/-- Intended bit length of a universal structural representation. -/
def bitSize : Raw → Nat
  | .nat n => natCodec.size n + 1
  | .pair a b => bitSize a + bitSize b + 1

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

namespace Presentation

/-- A presentation round-trips its distinguished representations. -/
def Lawful {α : Type u} (P : Presentation α) : Prop :=
  ∀ x : α, P.fromRaw (P.toRaw x) = some x

/-- A presentation is canonical if it accepts no alternative universal
representation of a value. -/
def Canonical {α : Type u} (P : Presentation α) : Prop :=
  P.Lawful ∧ ∀ {raw : Raw} {x : α}, P.fromRaw raw = some x → raw = P.toRaw x

/-- Structural size before natural leaves are serialized into bits. -/
def structuralSize {α : Type u} (P : Presentation α) (x : α) : Nat :=
  (P.toRaw x).nodes

/-- Exact intended bit size of a presented value. -/
def bitSize {α : Type u} (P : Presentation α) (x : α) : Nat :=
  (P.toRaw x).bitSize

end Presentation

/-- A complete family of structural codecs and presentation constructors.
Only the signatures are public; a valid standard is characterized separately
by declarative laws. -/
structure Standard where
  rawCodec : Codec Raw
  induced {α : Type u} : Presentation α → Codec α
  equiv {α β : Type u} : (α ≃ β) → Presentation β → Presentation α
  unit : Presentation Unit
  bool : Presentation Bool
  nat : Presentation Nat
  int : Presentation Int
  prod {α β : Type u} : Presentation α → Presentation β → Presentation (α × β)
  sum {α β : Type u} : Presentation α → Presentation β → Presentation (α ⊕ β)
  option {α : Type u} : Presentation α → Presentation (Option α)
  list {α : Type u} : Presentation α → Presentation (List α)
  array {α : Type u} : Presentation α → Presentation (Array α)
  fin : ∀ n : Nat, Presentation (Fin n)
  subtype {α : Type u} (P : Presentation α) (p : α → Prop)
      [DecidablePred p] : Presentation {x // p x}
  vector {α : Type u} : Presentation α → ∀ n : Nat, Presentation (List.Vector α n)
  finFunction {α : Type u} : Presentation α → ∀ n : Nat, Presentation (Fin n → α)
  multiset {α : Type u} [LinearOrder α] : Presentation α → Presentation (Multiset α)
  finset {α : Type u} [LinearOrder α] : Presentation α → Presentation (Finset α)

namespace Standard

/-- Declarative correctness and size specification for a structural encoding
standard. Multiset and finite-set presentations are only required to
round-trip: alternative orders, and repetitions for finite sets, may decode to
the same value. -/
structure Valid (S : Standard.{u}) : Prop where
  raw_lawful : S.rawCodec.Lawful
  raw_canonical : S.rawCodec.Canonical
  raw_size : ∀ raw : Raw, S.rawCodec.size raw = raw.bitSize
  induced_encode {α : Type u} (P : Presentation α) (x : α) :
    (S.induced P).encode x = S.rawCodec.encode (P.toRaw x)
  induced_size {α : Type u} (P : Presentation α) (x : α) :
    (S.induced P).size x = P.bitSize x
  induced_lawful {α : Type u} (P : Presentation α) :
    P.Lawful → (S.induced P).Lawful
  induced_canonical {α : Type u} (P : Presentation α) :
    P.Canonical → (S.induced P).Canonical
  equiv_size {α β : Type u} (e : α ≃ β) (P : Presentation β) (x : α) :
    (S.equiv e P).bitSize x = P.bitSize (e x)
  unit_size (x : Unit) : S.unit.bitSize x = 2
  bool_size (b : Bool) : S.bool.bitSize b = if b then 4 else 2
  nat_size (n : Nat) :
    S.nat.bitSize n = 2 * (binaryBits n).length + 2
  int_ofNat_size (n : Nat) :
    S.int.bitSize (.ofNat n) = 2 * (binaryBits n).length + 5
  int_negSucc_size (n : Nat) :
    S.int.bitSize (.negSucc n) = 2 * (binaryBits n).length + 7
  prod_size {α β : Type u} (A : Presentation α) (B : Presentation β)
      (x : α) (y : β) :
    (S.prod A B).bitSize (x, y) = A.bitSize x + B.bitSize y + 1
  sum_inl_size {α β : Type u} (A : Presentation α) (B : Presentation β)
      (x : α) :
    (S.sum A B).bitSize (Sum.inl x) = A.bitSize x + 3
  sum_inr_size {α β : Type u} (A : Presentation α) (B : Presentation β)
      (y : β) :
    (S.sum A B).bitSize (Sum.inr y) = B.bitSize y + 5
  option_none_size {α : Type u} (P : Presentation α) :
    (S.option P).bitSize none = 2
  option_some_size {α : Type u} (P : Presentation α) (x : α) :
    (S.option P).bitSize (some x) = P.bitSize x + 3
  list_size {α : Type u} (P : Presentation α) (xs : List α) :
    (S.list P).bitSize xs = 2 + xs.length + (xs.map P.bitSize).sum
  array_size {α : Type u} (P : Presentation α) (xs : Array α) :
    (S.array P).bitSize xs =
      2 + xs.size + (xs.toList.map P.bitSize).sum
  fin_size (n : Nat) (i : Fin n) :
    (S.fin n).bitSize i = 2 * (binaryBits i.val).length + 2
  subtype_size {α : Type u} (P : Presentation α) (p : α → Prop)
      [DecidablePred p] (x : {x // p x}) :
    (S.subtype P p).bitSize x = P.bitSize x.val
  vector_size {α : Type u} (P : Presentation α) (n : Nat)
      (xs : List.Vector α n) :
    (S.vector P n).bitSize xs =
      2 + n + (xs.toList.map P.bitSize).sum
  finFunction_size {α : Type u} (P : Presentation α) (n : Nat)
      (f : Fin n → α) :
    (S.finFunction P n).bitSize f =
      2 + n + (List.ofFn fun i => P.bitSize (f i)).sum
  multiset_size {α : Type u} [LinearOrder α] (P : Presentation α)
      (s : Multiset α) :
    (S.multiset P).bitSize s = 2 + s.card + (s.map P.bitSize).sum
  finset_size {α : Type u} [LinearOrder α] (P : Presentation α)
      (s : Finset α) :
    (S.finset P).bitSize s = 2 + s.card + s.sum P.bitSize
  equiv {α β : Type u} (e : α ≃ β) (P : Presentation β) :
    P.Lawful → (S.equiv e P).Lawful
  unit : S.unit.Lawful
  bool : S.bool.Lawful
  nat : S.nat.Lawful
  int : S.int.Lawful
  prod {α β : Type u} (A : Presentation α) (B : Presentation β) :
    A.Lawful → B.Lawful → (S.prod A B).Lawful
  sum {α β : Type u} (A : Presentation α) (B : Presentation β) :
    A.Lawful → B.Lawful → (S.sum A B).Lawful
  option {α : Type u} (P : Presentation α) :
    P.Lawful → (S.option P).Lawful
  list {α : Type u} (P : Presentation α) :
    P.Lawful → (S.list P).Lawful
  array {α : Type u} (P : Presentation α) :
    P.Lawful → (S.array P).Lawful
  fin (n : Nat) : (S.fin n).Lawful
  subtype {α : Type u} (P : Presentation α) (p : α → Prop)
      [DecidablePred p] :
    P.Lawful → (S.subtype P p).Lawful
  vector {α : Type u} (P : Presentation α) (n : Nat) :
    P.Lawful → (S.vector P n).Lawful
  finFunction {α : Type u} (P : Presentation α) (n : Nat) :
    P.Lawful → (S.finFunction P n).Lawful
  multiset {α : Type u} [LinearOrder α] (P : Presentation α) :
    P.Lawful → (S.multiset P).Lawful
  finset {α : Type u} [LinearOrder α] (P : Presentation α) :
    P.Lawful → (S.finset P).Lawful
  canonical_unit : S.unit.Canonical
  canonical_bool : S.bool.Canonical
  canonical_nat : S.nat.Canonical
  canonical_int : S.int.Canonical
  canonical_prod {α β : Type u} (A : Presentation α) (B : Presentation β) :
    A.Canonical → B.Canonical → (S.prod A B).Canonical
  canonical_sum {α β : Type u} (A : Presentation α) (B : Presentation β) :
    A.Canonical → B.Canonical → (S.sum A B).Canonical
  canonical_option {α : Type u} (P : Presentation α) :
    P.Canonical → (S.option P).Canonical
  canonical_list {α : Type u} (P : Presentation α) :
    P.Canonical → (S.list P).Canonical

end Standard

end Lax58.StructuralEncoding
