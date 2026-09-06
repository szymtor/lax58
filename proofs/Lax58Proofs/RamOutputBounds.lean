import Lax58.RamComplexity

namespace Lax58Proofs.RamOutputBounds

open Lax13.Ram Lax13.RamComputes
open Lax58.StructuralPresentation Lax58.WordArena Lax58.RamComplexity

/-- Every word written by a RAM fits, regardless of the input, memory,
program, or running time. -/
theorem effect_output_fits (w : Nat) (i : Instr) (s s' : State)
    (hs : ∀ a ∈ s.out, a < 2 ^ w) (h : i.effect w s = some s') :
    ∀ a ∈ s'.out, a < 2 ^ w := by
  cases i <;> simp only [Instr.effect] at h
  all_goals try { cases h; exact hs }
  case halt => cases h
  case read a =>
    cases hi : s.inp.head? with
    | none => rw [hi] at h; cases h
    | some v => rw [hi] at h; cases h; exact hs
  case write address =>
    cases h
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hs a ha
    · have : a = s.mem (address % 2 ^ w) % 2 ^ w := by simpa using ha
      subst a
      exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem step_output_fits (w : Nat) (p : Program) (s s' : State)
    (hs : ∀ a ∈ s.out, a < 2 ^ w) (h : step w p s = some s') :
    ∀ a ∈ s'.out, a < 2 ^ w := by
  simp only [step] at h
  cases hi : p[s.pc]? with
  | none => simp [hi] at h
  | some i => exact effect_output_fits w i s s' hs (by simpa [hi] using h)

theorem run_output_fits (w : Nat) (p : Program) (t : Nat) (s s' : State)
    (hs : ∀ a ∈ s.out, a < 2 ^ w) (h : run w p t s = some s') :
    ∀ a ∈ s'.out, a < 2 ^ w := by
  induction t generalizing s with
  | zero => cases h; exact hs
  | succ t ih =>
    simp only [run] at h
    cases he : step w p s with
    | none => simp [he] at h
    | some next =>
      exact ih next (step_output_fits w p s next hs he) (by simpa [he] using h)

theorem runsTo_output_fits {w : Nat} {p : Program} {x y : List Nat} {t : Nat}
    (h : RunsTo w p x y t) : ∀ a ∈ y, a < 2 ^ w := by
  obtain ⟨s, hrun, _, rfl⟩ := h
  exact run_output_fits w p t (initState x) s (by simp [initState]) hrun

/-- A capacity lower bound on exact natural outputs. This applies even
without any restriction on the allowed running time. -/
theorem within_nat_output_lt {α : Type} {input : Presentation α}
    {f : α → Nat} {timeBound wordBound : α → Nat}
    (h : RamComputableWithinUsing input natOutput f timeBound wordBound)
    (x : α) (w : Nat) (hp : (input.toRaw x).PayloadsFitInWord w)
    (ha : 3 * (input.toRaw x).nodes ≤ 2 ^ w) (hw : wordBound x ≤ 2 ^ w) :
    f x < 2 ^ w := by
  obtain ⟨p, h⟩ := h
  obtain ⟨t, _, ht⟩ := h x w hp ha hw (encode input x).toInput (by rfl)
  exact runsTo_output_fits ht (f x) (by simp [natOutput])

end Lax58Proofs.RamOutputBounds
