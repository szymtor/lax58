import Lax560851.StructuralCombinators

/-!
---
title: Field-encoding agreement (infrastructure)
type: infrastructure
---

An agreement witness fixes an encoder and a proposition, supplies an
implementation equal to that encoder, and carries a proof of the proposition.
The operations below retain natural values, erase subtype proofs, and
enumerate finite families in intrinsic order.

This record is bookkeeping for generated certificates, not a standalone
definition of advice-freedom: an arbitrary encoder and an arbitrary true
proposition can have an agreement witness. The constructor equations generated
for a particular datatype supply the semantic specification.

Use `Lax560851.CertifiedDerivationElab` for the closed derivation command. Its
field resolver accepts only approved primitives and previously generated
datatype witnesses, never arbitrary values of this record. Constructor
privacy alone is not a proof boundary; the indexed specification and equality
obligation prevent replacing a specified encoder with a different function.
-/

namespace Lax560851.CertifiedDerivation

open Lax560851.StructuralPresentation Lax560851.StructuralCombinators

universe u

/-- A checked implementation of a specified canonical encoder and law.
Both specifications are type indices, so even tactics accessing the private
constructor cannot replace them. Provenance of the specifications comes from
the closed derivation command, which never accepts arbitrary witness values. -/
structure CertifiedFieldEncoding (α : Type u) (canonical : α → Raw) (laws : Prop) where
  private mk ::
  toRaw : α → Raw
  agrees : toRaw = canonical
  checked : laws

namespace CertifiedFieldEncoding

/-- Package a specified encoder with a proof of its law. This constructs only
an agreement value: it does not register a datatype or certify the provenance
of the supplied specification. The derivation command alone manages that
registry, after inspecting the source constructors. -/
def ofLaws {α : Type u} (canonical : α → Raw) {laws : Prop} (checked : laws) :
    CertifiedFieldEncoding α canonical laws :=
  ⟨canonical, rfl, checked⟩

/-- The law fixed by a certificate's type, not chosen by its implementation. -/
def Laws {α : Type u} {canonical : α → Raw} {laws : Prop}
    (_P : CertifiedFieldEncoding α canonical laws) : Prop := laws

/-- The natural-number primitive. -/
def nat : CertifiedFieldEncoding Nat Raw.nat (∀ n : Nat, Raw.nat n = Raw.nat n) :=
  ⟨Raw.nat, rfl, fun _ => rfl⟩

/-- Finite indices retain their natural value. -/
def fin (n : Nat) : CertifiedFieldEncoding (Fin n) (fun i => Raw.nat i.val)
    (∀ i : Fin n, Raw.nat i.val = Raw.nat i.val) :=
  ⟨fun i => Raw.nat i.val, rfl, fun _ => rfl⟩

/-- Erase only a subtype's proof, retaining its certified computational field. -/
def subtype {α : Type u} {canonical : α → Raw} {laws : Prop}
    (P : CertifiedFieldEncoding α canonical laws) (p : α → Prop) :
    CertifiedFieldEncoding (Subtype p) (fun x => canonical x.val) laws :=
  ⟨fun x => canonical x.val, rfl, P.checked⟩

/-- Enumerate a possibly dependent finite family in intrinsic index order. -/
def family {n : Nat} {α : Fin n → Type u}
    {canonical : (i : Fin n) → α i → Raw} {laws : Fin n → Prop}
    (P : (i : Fin n) → CertifiedFieldEncoding (α i) (canonical i) (laws i)) :
    CertifiedFieldEncoding ((i : Fin n) → α i)
      (fun f => Raw.fields (List.ofFn fun i => canonical i (f i))) (∀ i, laws i) :=
  ⟨fun f => Raw.fields (List.ofFn fun i => canonical i (f i)),
    rfl, fun i => (P i).checked⟩

end CertifiedFieldEncoding

end Lax560851.CertifiedDerivation
