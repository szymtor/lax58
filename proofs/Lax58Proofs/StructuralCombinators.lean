import Lax58.StructuralCombinators

namespace Lax58Proofs.StructuralCombinators

open Lax58.StructuralPresentation
open Lax58.StructuralPresentation.Presentation
open Lax58.StructuralCombinators

universe u v

private theorem lawful_equiv {α : Type u} {β : Type v} (e : α ≃ β)
    (P : Presentation β) (hP : P.Lawful) : (equiv e P).Lawful := by
  intro x
  simp only [equiv]
  rw [hP (e x)]
  simp

private theorem lawful_prod {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Lawful) (hB : B.Lawful) : (prod A B).Lawful := by
  intro x
  simp only [prod]
  rw [hA x.1, hB x.2]

private theorem lawful_sum {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Lawful) (hB : B.Lawful) : (sum A B).Lawful := by
  intro x
  cases x with
  | inl x => simp [sum, hA x]
  | inr y => simp [sum, hB y]

private theorem list_roundtrip {α : Type u} (P : Presentation α) (hP : P.Lawful)
    (xs : List α) : listFromRaw P (listToRaw P xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listToRaw, listFromRaw, hP x, ih]

private theorem lawful_vector {α : Type u} (P : Presentation α) (n : Nat)
    (hP : P.Lawful) : (vector P n).Lawful := by
  intro xs
  simp [vector, list_roundtrip P hP, xs.2]

private theorem list_nodes {α : Type u} (P : Presentation α) (xs : List α) :
    (listToRaw P xs).nodes = 1 + xs.length + (xs.map P.structuralSize).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [listToRaw, Raw.nodes, List.length_cons, List.map_cons,
        List.sum_cons, Presentation.structuralSize]
      omega

private theorem lawfulWitness : Lax58.StructuralCombinators.Lawful.{u, v} where
  equiv := lawful_equiv
  unit := by intro x; cases x; rfl
  bool := by intro b; cases b <;> rfl
  nat := by intro n; rfl
  prod := lawful_prod
  sum := lawful_sum
  list := by intro α P hP; exact list_roundtrip P hP
  fin := by intro n i; simp [fin, i.isLt]
  vector := lawful_vector
  finFunction := by
    intro α P n hP
    exact lawful_equiv _ _ (lawful_vector P n hP)

private theorem sizeWitness : Lax58.StructuralCombinators.SizeLaws.{u, v} where
  equiv := by intro α β e P x; rfl
  unit := by intro x; cases x; rfl
  bool := by intro b; cases b <;> rfl
  nat := by intro n; rfl
  prod := by intro α β A B x y; rfl
  sum_inl := by
    intro α β A B x
    simp [sum, Presentation.structuralSize, Raw.nodes]
    omega
  sum_inr := by
    intro α β A B y
    simp [sum, Presentation.structuralSize, Raw.nodes]
    omega
  list := by intro α P xs; exact list_nodes P xs
  fin := by intro n i; rfl
  vector := by
    intro α P n xs
    simpa [vector, Presentation.structuralSize, xs.2] using list_nodes P xs.toList
  finFunction := by
    intro α P n f
    change (listToRaw P (List.Vector.ofFn f).toList).nodes =
      1 + n + (List.ofFn fun i => P.structuralSize (f i)).sum
    rw [List.Vector.toList_ofFn]
    simpa [List.map_ofFn, Function.comp_def] using list_nodes P (List.ofFn f)

/--
---
conclusion: Lax58.StructuralCombinators.lawful
---
-/
theorem structural_combinators_lawful : Lax58.StructuralCombinators.Lawful.{u, v} :=
  lawfulWitness

/--
---
conclusion: Lax58.StructuralCombinators.sizeLaws
---
-/
theorem structural_combinator_size_laws : Lax58.StructuralCombinators.SizeLaws.{u, v} :=
  sizeWitness

end Lax58Proofs.StructuralCombinators
