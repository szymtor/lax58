import Lax58.StructuralPresentation

namespace Lax58Proofs.StructuralPresentation

open Lax58.StructuralPresentation
open Lax58.StructuralPresentation.Presentation

universe u

/-- A round-tripping presentation is faithful. -/
theorem faithful_of_lawful {α : Type u} {P : Presentation α}
    (hP : P.Lawful) : P.Faithful := by
  intro x y hxy
  have hx := hP x
  have hy := hP y
  rw [hxy, hy] at hx
  exact (Option.some.inj hx).symm

/-- An injective map packaged by `presentationOf` round-trips. This is only a
faithfulness fact; downstream constructor equations are still required before
the presentation may serve as a neutral complexity input. -/
theorem presentationOf_lawful {α : Type u} {f : α → Raw}
    (hf : Function.Injective f) : (presentationOf f).Lawful := by
  intro x
  classical
  simp only [presentationOf]
  split
  next h =>
    apply congrArg some
    apply hf
    exact Classical.choose_spec h
  next h => exact False.elim (h ⟨x, rfl⟩)

end Lax58Proofs.StructuralPresentation
