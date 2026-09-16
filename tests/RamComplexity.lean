import Lax560851.RamComplexityExample
import Lax560851.FormulaExample
import Lax560851.StructuralDerivation

open Lax560851 Lax560851.StructuralPresentation Lax560851.StructuralCombinators
open Lax560851.RamComplexity Lax560851.CertifiedDerivation

set_option autoImplicit false

namespace RamComplexityTests

-- These are kernel-checked equalities of the complete expanded propositions.
example (f T W : Nat → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing StructuralCombinators.nat natOutput f T W := rfl

example (f : Nat → Bool) (T W : Nat → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing StructuralCombinators.nat
        (fun b => [if b then 1 else 0]) f T W := rfl

example (n : Nat) : inputMagnitude n = n + 2 := by
  change 1 + n + 1 = n + 2
  omega

example (f : List Nat → List Nat) (T W : List Nat → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing (StructuralCombinators.list StructuralCombinators.nat)
        (arenaOutput (listToRaw StructuralCombinators.nat)) f T W := rfl

example (x : List Nat × List Nat) :
    inputMagnitude x = inputMagnitudeUsing
      (StructuralCombinators.prod
        (StructuralCombinators.list StructuralCombinators.nat)
        (StructuralCombinators.list StructuralCombinators.nat)) x := rfl

-- Imported registry entries work for both input and structured output.
open Lax560851.FormulaExample in
example (f : Formula → Formula) (T W : Formula → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing (presentationOf formulaRaw)
        (arenaOutput formulaRaw) f T W := rfl

inductive Leaf where
  | value (n : Nat)

derive_certified_encoding leafRaw indexed : Leaf

inductive Indexed : Nat → Type where
  | value {n : Nat} (i : Fin n) : Indexed n

derive_certified_encoding indexedRaw indexed {n : Nat} : Indexed n

example (n : Nat) (f : Indexed n → Nat) (T W : Indexed n → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing (presentationOf (@indexedRaw n)) natOutput f T W := rfl

-- The presentation wrapper uses a choice-based decoder. Complexity statements
-- inspect only its fixed encoder; no executable decoder is being claimed.
noncomputable def leafMagnitude (x : Leaf) : Nat := inputMagnitude x

example (x : Leaf) : leafMagnitude x =
    (leafRaw x).nodes + (leafRaw x).maxNat + 1 := rfl

example (f : List Leaf → Fin 3) (T W : List Leaf → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing
        (StructuralCombinators.list (presentationOf leafRaw))
        (arenaOutput (fun i : Fin 3 => Raw.nat i.val)) f T W := rfl

-- Compositions recurse through proof-erased subtypes and dependent families.
example (x : {xs : List Nat // xs.length > 0}) :
    inputMagnitude x = inputMagnitude x.val := rfl

example (x : (i : Fin 2) → List (Fin (i.val + 1))) :
    inputMagnitude x = inputMagnitudeUsing
      (presentationOf (fun x : (i : Fin 2) → List (Fin (i.val + 1)) =>
        Raw.fields (List.ofFn fun i =>
          listToRaw (presentationOf (fun j : Fin (i.val + 1) => Raw.nat j.val)) (x i)))) x := rfl

-- Arbitrary low-level instances and agreement records must have no effect.
instance : Lax560851.StructuralDerivation.FieldEncoding Nat where
  toRaw _ := Raw.nat 999

instance : Lax560851.StructuralDerivation.FieldEncoding Leaf where
  toRaw _ := Raw.nat 999

instance : Lax560851.StructuralDerivation.FieldEncoding Bool where
  toRaw _ := Raw.nat 999

example (f : Nat → Bool) (T W : Nat → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing StructuralCombinators.nat boolOutput f T W := rfl

example (n : Nat) : inputMagnitude n = inputMagnitudeUsing StructuralCombinators.nat n := rfl

example (f : Leaf → Nat) (T W : Leaf → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing (presentationOf leafRaw) natOutput f T W := rfl

-- Even a local presentation instance for an unregistered type is ignored.
inductive Unregistered where
  | value (n : Nat)

class HasPresentation (α : Type) where
  presentation : Presentation α

noncomputable instance : HasPresentation Unregistered where
  presentation := presentationOf (fun _ => Raw.nat 999)

instance : Lax560851.StructuralDerivation.FieldEncoding Unregistered where
  toRaw _ := Raw.nat 999

def forgedAgreement :
    CertifiedFieldEncoding Unregistered (fun _ => Raw.nat 999) True :=
  CertifiedFieldEncoding.ofLaws (fun _ => Raw.nat 999) True.intro

example : True := by
  fail_if_success
    have bad : Prop := RamComputableWithin
      (fun _ : Unregistered => 0) (fun _ => 1) (fun _ => 1)
  fail_if_success
    have bad : Prop := RamComputableWithin
      (fun _ : Nat => Unregistered.value 0) (fun _ => 1) (fun _ => 1)
  fail_if_success
    have bad : Nat := inputMagnitude (Unregistered.value 0)
  fail_if_success
    have bad : Prop := RamComputableWithin
      (fun _ : Nat → Nat => 0) (fun _ => 1) (fun _ => 1)
  fail_if_success
    have bad : Prop := RamComputableWithin
      (fun n : Nat => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)))
      (fun _ => 1) (fun _ => 1)
  fail_if_success
    have bad : Prop := RamComputableWithin 0 (fun _ => 1) (fun _ => 1)
  fail_if_success
    have bad : Prop := RamComputableWithin
      (fun n : Nat => n) (fun _ => true) (fun _ => 1)
  trivial

-- Failed resolution neither registers anything nor poisons later uses.
example (f T W : Nat → Nat) :
    (RamComputableWithin f T W) =
      RamComputableWithinUsing StructuralCombinators.nat natOutput f T W := rfl

-- The explicit core has exactly the promised quantifier order and premises.
example (f T W : Nat → Nat) :
    (RamComputableWithin f T W) ↔
      ∃ p : Lax808846.Ram.Program, ∀ n w : Nat,
        n < 2 ^ w → 3 ≤ 2 ^ w → W n ≤ 2 ^ w →
        Lax808846.RamComputes.ComputesInTime w p
          {(Lax560851.WordArena.encodeRaw (.nat n)).toInput}
          (fun _ => [f n]) (fun _ => T n) := Iff.rfl

-- Polynomial examples retain the same word convention and keep every
-- coefficient, degree, and program independent of the runtime input.
open Lax560851.RamComplexityExample in
example (f : List Nat → Nat) (d : Nat) :
    PolynomialTimeOfDegree f d ↔
      ∃ timeCoefficient wordCoefficient : Nat,
        RamComputableWithin f
          (fun xs => timeCoefficient * (xs.length + 1) ^ d)
          (fun xs => wordCoefficient * inputMagnitude xs) := Iff.rfl

open Lax560851.RamComplexityExample in
example (f : List Nat → Nat) :
    PolynomialTime f ↔ ∃ d : Nat, PolynomialTimeOfDegree f d := Iff.rfl

open Lax560851.RamComplexityExample in
example (f : List Nat → Nat) :
    PolynomialTimeOfDegree f 0 ↔
      ∃ timeCoefficient : Nat, TimeBounded f (fun _ => timeCoefficient) := by
  simp only [PolynomialTimeOfDegree, Nat.pow_zero, Nat.mul_one]

/-- info: 'Lax560851.RamComplexityExample.PolynomialTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lax560851.RamComplexityExample.PolynomialTime

/-- info: 'Lax560851.RamComplexityExample.LinearInFirstInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lax560851.RamComplexityExample.LinearInFirstInput

end RamComplexityTests
