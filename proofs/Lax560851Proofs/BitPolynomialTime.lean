import Lax560851.BitPolynomialTime

namespace Lax560851Proofs.BitPolynomialTime

open Lax865980.Ram Lax865980.RamComputes
open Lax560851.StructuralPresentation Lax560851.WordArena Lax560851.RamComplexity
open Lax560851.BitPolynomialTime

universe u v

/-- Unfold the capacity-form interface into the sufficient-bit-width form
used in the comparison with Lax759944. The program still precedes every input
and every runtime width in the quantifier order. -/
theorem using_iff {α : Type u} {β : Type v}
    (input : Presentation α) (output : β → List Nat)
    (inputSize : α → Nat) (f : α → β) :
    BitPolynomialTimeUsing input output inputSize f ↔
      ∃ (wordBits time : Polynomial Nat) (program : Program),
        (∀ x, (input.toRaw x).PayloadsFitInWord (wordBits.eval (inputSize x)) ∧
          3 * (input.toRaw x).nodes ≤ 2 ^ wordBits.eval (inputSize x)) ∧
        ∀ x w, wordBits.eval (inputSize x) ≤ w →
          ∃ t ≤ time.eval (inputSize x),
            RunsTo w program (encode input x).toInput (output (f x)) t := by
  constructor
  · rintro ⟨wordBits, time, hfit, program, hprogram⟩
    refine ⟨wordBits, time, program, hfit, ?_⟩
    intro x w hw
    have hcapacity := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw
    have hp : (input.toRaw x).PayloadsFitInWord w :=
      (hfit x).1.trans_le hcapacity
    exact hprogram x w hp ((hfit x).2.trans hcapacity) hcapacity _ (by rfl)
  · rintro ⟨wordBits, time, program, hfit, hprogram⟩
    refine ⟨wordBits, time, hfit, program, ?_⟩
    intro x w _ _ hcapacity tape htape
    have hw : wordBits.eval (inputSize x) ≤ w :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcapacity
    have htape : tape = (encode input x).toInput := htape
    subst tape
    exact hprogram x w hw

end Lax560851Proofs.BitPolynomialTime
