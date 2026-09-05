import Lax58.CertifiedDerivation

/- The small agreement API is usable without importing the derivation tool.
Run from concepts/: lake env lean ../tests/EncodingAgreement.lean -/

open Lax58.StructuralPresentation Lax58.CertifiedDerivation

set_option autoImplicit false

example {α : Type} (canonical : α → Raw) (laws : Prop) (checked : laws) :
    (CertifiedFieldEncoding.ofLaws canonical checked).toRaw = canonical := rfl

example {α : Type} (canonical : α → Raw) (laws : Prop) (checked : laws) :
    (CertifiedFieldEncoding.ofLaws canonical checked).Laws :=
  (CertifiedFieldEncoding.ofLaws canonical checked).checked

-- Agreement alone deliberately makes no provenance claim.
example : CertifiedFieldEncoding Nat (fun _ => Raw.nat 99) True :=
  CertifiedFieldEncoding.ofLaws (fun _ => Raw.nat 99) True.intro

example (n : Nat) : CertifiedFieldEncoding.nat.toRaw n = Raw.nat n := rfl

example {n : Nat} (i : Fin n) :
    (CertifiedFieldEncoding.fin n).toRaw i = Raw.nat i.val := rfl
