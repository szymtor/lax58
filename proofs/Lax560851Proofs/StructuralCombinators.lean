import Lax560851.StructuralCombinators

namespace Lax560851Proofs.StructuralCombinators

open Lax560851.StructuralPresentation
open Lax560851.StructuralPresentation.Presentation
open Lax560851.StructuralCombinators

universe u v

private theorem constructorCharsCode_injective :
    Function.Injective Raw.constructorCharsCode := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys => simp [Raw.constructorCharsCode] at h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp [Raw.constructorCharsCode] at h
      | cons y ys =>
          simp only [Raw.constructorCharsCode] at h
          have hPair : Nat.pair x.toNat (Raw.constructorCharsCode xs) =
              Nat.pair y.toNat (Raw.constructorCharsCode ys) := Nat.add_right_cancel h
          have pairEq : (x.toNat, Raw.constructorCharsCode xs) =
              (y.toNat, Raw.constructorCharsCode ys) := Nat.pairEquiv.injective hPair
          have components := Prod.mk.inj pairEq
          have charEq : x = y := Char.toNat_inj.mp components.1
          have tailEq : xs = ys := ih components.2
          simp [charEq, tailEq]

private theorem constructorNameCode_injective :
    Function.Injective Raw.constructorNameCode := by
  intro a b h
  apply String.toList_injective
  exact constructorCharsCode_injective h

private theorem fields_injective : Function.Injective Raw.fields := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys => simp [Raw.fields] at h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp [Raw.fields] at h
      | cons y ys =>
          simp only [Raw.fields, Raw.pair.injEq] at h
          exact congrArg₂ List.cons h.1 (ih h.2)

private theorem constructorEq {name₁ name₂ : String} {xs₁ xs₂ : List Raw} :
    Raw.constructor name₁ xs₁ = Raw.constructor name₂ xs₂ ↔
      name₁ = name₂ ∧ xs₁ = xs₂ := by
  constructor
  · intro h
    simp only [Raw.constructor, Raw.pair.injEq, Raw.nat.injEq] at h
    exact ⟨constructorNameCode_injective h.1, fields_injective h.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem lawful_prod {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Lawful) (hB : B.Lawful) : (prod A B).Lawful := by
  intro x
  simp only [prod]
  rw [hA x.1, hB x.2]

private theorem list_roundtrip {α : Type u} (P : Presentation α) (hP : P.Lawful)
    (xs : List α) : listFromRaw P (listToRaw P xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listToRaw, listFromRaw, hP x, ih]

private theorem list_nodes {α : Type u} (P : Presentation α) (xs : List α) :
    (listToRaw P xs).nodes = 1 + xs.length + (xs.map P.structuralSize).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [listToRaw, Raw.nodes, List.length_cons, List.map_cons,
        List.sum_cons, Presentation.structuralSize]
      omega

private theorem lawfulWitness : Lax560851.StructuralCombinators.Lawful.{u, v} where
  nat := by intro n; rfl
  prod := lawful_prod
  list := by intro α P hP; exact list_roundtrip P hP

private theorem sizeWitness : Lax560851.StructuralCombinators.SizeLaws.{u, v} where
  nat := by intro n; rfl
  prod := by intro α β A B x y; rfl
  list := by intro α P xs; exact list_nodes P xs

/-- Any derivation from the fixed combinator vocabulary is lawful. -/
theorem Generated.lawful {α : Type} {P : Presentation α}
    (h : Generated P) : P.Lawful := by
  let laws : Lax560851.StructuralCombinators.Lawful.{0, 0} :=
    Lax560851.StructuralCombinators.lawful
  induction h with
  | nat => exact laws.nat
  | prod hA hB ihA ihB => exact laws.prod _ _ ihA ihB
  | list hP ih => exact laws.list _ ih

/-- Every automatically derived presentation round-trips. -/
theorem derivedPresentation_lawful {α : Type} [P : Derivable α] :
    (derivedPresentation (α := α)).Lawful :=
  Generated.lawful P.generated

/--
---
conclusion: Lax560851.StructuralCombinators.Raw.constructor_eq_iff
---
-/
theorem constructor_eq_iff_proof {name₁ name₂ : String} {xs₁ xs₂ : List Raw} :
    Raw.constructor name₁ xs₁ = Raw.constructor name₂ xs₂ ↔
      name₁ = name₂ ∧ xs₁ = xs₂ :=
  constructorEq

/--
---
conclusion: Lax560851.StructuralCombinators.lawful
---
-/
theorem structural_combinators_lawful : Lax560851.StructuralCombinators.Lawful.{u, v} :=
  lawfulWitness

/--
---
conclusion: Lax560851.StructuralCombinators.sizeLaws
---
-/
theorem structural_combinator_size_laws : Lax560851.StructuralCombinators.SizeLaws.{u, v} :=
  sizeWitness

end Lax560851Proofs.StructuralCombinators
