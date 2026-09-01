import Lax58.StructuralEncoding

/-!
---
title: Correctness of structural presentations
type: theorem
---

The universal structural codec is canonical. The standard structural
presentations round-trip, and the ordered constructors preserve canonicality.
Multiset and finite-set presentations are only asserted to round-trip because
their decoders deliberately accept alternative orders.
-/

namespace Lax58.StructuralEncodingLaws

open Lax58.CanonicalCodec.Codec
open Lax58.StructuralEncoding
open Lax58.StructuralEncoding.Presentation

universe u v

/-- Correctness laws for the universal codec and standard presentations. -/
structure Laws : Prop where
  raw_lawful : Raw.codec.Lawful
  raw_canonical : Raw.codec.Canonical
  induced_lawful {α : Type u} (P : Presentation α) :
    P.Lawful → P.codec.Lawful
  induced_canonical {α : Type u} (P : Presentation α) :
    P.Canonical → P.codec.Canonical
  equiv {α : Type u} {β : Type v} (e : α ≃ β) (P : Presentation β) :
    P.Lawful → (Presentation.equiv e P).Lawful
  unit : Presentation.unit.Lawful
  bool : Presentation.bool.Lawful
  nat : Presentation.nat.Lawful
  int : Presentation.int.Lawful
  prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    A.Lawful → B.Lawful → (Presentation.prod A B).Lawful
  sum {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    A.Lawful → B.Lawful → (Presentation.sum A B).Lawful
  option {α : Type u} (P : Presentation α) :
    P.Lawful → (Presentation.option P).Lawful
  list {α : Type u} (P : Presentation α) :
    P.Lawful → (Presentation.list P).Lawful
  array {α : Type u} (P : Presentation α) :
    P.Lawful → (Presentation.array P).Lawful
  fin (n : Nat) : (Presentation.fin n).Lawful
  subtype {α : Type u} (P : Presentation α) (p : α → Prop)
      [DecidablePred p] :
    P.Lawful → (Presentation.subtype P p).Lawful
  vector {α : Type u} (P : Presentation α) (n : Nat) :
    P.Lawful → (Presentation.vector P n).Lawful
  finFunction {α : Type u} (P : Presentation α) (n : Nat) :
    P.Lawful → (Presentation.finFunction P n).Lawful
  multiset {α : Type u} [LinearOrder α] (P : Presentation α) :
    P.Lawful → (Presentation.multiset P).Lawful
  finset {α : Type u} [LinearOrder α] (P : Presentation α) :
    P.Lawful → (Presentation.finset P).Lawful
  canonical_unit : Presentation.unit.Canonical
  canonical_bool : Presentation.bool.Canonical
  canonical_nat : Presentation.nat.Canonical
  canonical_int : Presentation.int.Canonical
  canonical_prod {α : Type u} {β : Type v} (A : Presentation α)
      (B : Presentation β) :
    A.Canonical → B.Canonical → (Presentation.prod A B).Canonical
  canonical_sum {α : Type u} {β : Type v} (A : Presentation α)
      (B : Presentation β) :
    A.Canonical → B.Canonical → (Presentation.sum A B).Canonical
  canonical_option {α : Type u} (P : Presentation α) :
    P.Canonical → (Presentation.option P).Canonical
  canonical_list {α : Type u} (P : Presentation α) :
    P.Canonical → (Presentation.list P).Canonical

axiom laws : Laws

end Lax58.StructuralEncodingLaws
