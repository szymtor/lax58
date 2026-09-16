import Lax560851Proofs.Legacy.RamPolynomialComparison
import Lax560851Proofs.BitPolynomialTime
import Lax759944Proofs.LegacyRamClasses

/-!
Transfer of the arena/native polynomial-class comparison to the current RAM.
The legacy compiler comparison is an internal checked lemma. This module
isolates the exact finite-run contract required of the input-buffer compiler,
then accounts for its linear scan and fixed extra word-width margin.
-/

namespace Lax560851Proofs.TapeRamPolynomialComparison

open Lax560851.StructuralPresentation Lax560851.StructuralCombinators
open Lax560851.WordArena Lax560851.RamComplexity
open Lax759944.BinaryWordEncoding

/-- The same-input buffering contract. `extra=1` covers native framing and
`extra=4` covers natural-list arena framing. Every current instruction is in
scope; the hypothesis is not a restriction on source programs. -/
def CorrectLowering
    (lower : Nat → Lax808846.Ram.Program → Lax759944Proofs.Legacy.Ram.Program) : Prop :=
  ∀ (extra header : Nat) (tail : List Nat) (program : Lax808846.Ram.Program)
      (v : Nat) (output : List Nat) (t : Nat),
    (header :: tail).length = header + extra →
    (∀ a ∈ header :: tail, a < 2 ^ v) →
    (header :: tail).length + 32 < 2 ^ v →
    Lax808846.Ram.RunsTo v program (header :: tail) output t →
    ∃ u ≤ 18 * t + 6 * (header :: tail).length + 26,
      Lax759944Proofs.Legacy.Ram.RunsTo (v + 1)
        (lower extra program) (header :: tail) output u

/-- A legacy arena computation embeds in the current model; terminal
instruction accounting increases its time bound by at most one. -/
theorem arena_forward {f : List Nat → Nat} (hf : Legacy.BitPolynomialTime f) :
    Lax560851.RamPolynomialComparison.BitPolynomialTime f := by
  obtain ⟨wordBits, time, program, hfit, hprogram⟩ := hf
  apply (Lax560851Proofs.BitPolynomialTime.using_iff
    (list nat) natOutput bitSize f).mpr
  refine ⟨wordBits, time + 1, Lax759944Proofs.LegacyRamBridge.embedProgram program,
    hfit, ?_⟩
  intro xs w hw
  obtain ⟨t, ht, hr⟩ := hprogram xs w hw
  obtain ⟨u, _, hu, hr'⟩ := Lax759944Proofs.LegacyRamBridge.runsTo hr
  exact ⟨u, by simpa using hu.trans (Nat.add_le_add_right ht 1), hr'⟩

private theorem arena_length (xs : List Nat) :
    (encode (list nat) xs).toInput.length = 6 * xs.length + 4 := by
  change (encodeRaw (listToRaw nat xs)).toInput.length = _
  rw [Lax560851Proofs.WordArena.encodeRaw_toInput_length_proof,
    Lax560851Proofs.RamPolynomialSeparation.natList_nodes]
  omega

/-- Buffer the complete arena, then simulate the current program using the
legacy instruction set. The scan contributes a linear bit-size term. -/
theorem arena_backward_of_lowering
    (lower : Nat → Lax808846.Ram.Program → Lax759944Proofs.Legacy.Ram.Program)
    (hlower : CorrectLowering lower)
    {f : List Nat → Nat} (hf : Lax560851.RamPolynomialComparison.BitPolynomialTime f) :
    Legacy.BitPolynomialTime f := by
  obtain ⟨wordBits, time, program, hfit, hprogram⟩ :=
    (Lax560851Proofs.BitPolynomialTime.using_iff
      (list nat) natOutput bitSize f).mp hf
  let newWord := wordBits + Polynomial.C 7
  let newTime := Polynomial.C 18 * time + Polynomial.C 36 * Polynomial.X + Polynomial.C 50
  refine ⟨newWord, newTime, lower 4 program, ?_, ?_⟩
  · intro xs
    have hpow : 2 ^ wordBits.eval (bitSize xs) ≤ 2 ^ newWord.eval (bitSize xs) := by
      apply Nat.pow_le_pow_right (by decide)
      simp [newWord]
    exact ⟨(hfit xs).1.trans_le hpow, (hfit xs).2.trans hpow⟩
  · intro xs w hw
    let v := w - 1
    have hweval : newWord.eval (bitSize xs) = wordBits.eval (bitSize xs) + 7 := by
      simp [newWord]
    have hv : v + 1 = w := by dsimp [v]; rw [hweval] at hw; omega
    have hqv : wordBits.eval (bitSize xs) + 6 ≤ v := by
      dsimp [v]; rw [hweval] at hw; omega
    have hq : wordBits.eval (bitSize xs) ≤ v := by omega
    have hpow : 2 ^ wordBits.eval (bitSize xs) * 64 ≤ 2 ^ v := by
      simpa [Nat.pow_add] using
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hqv)
    have hfitTape : ∀ a ∈ (encode (list nat) xs).toInput, a < 2 ^ v := by
      apply Lax560851Proofs.WordArena.encodeRaw_toInput_lt
      · exact (hfit xs).1.trans_le (Nat.pow_le_pow_right (by decide) hq)
      · exact (hfit xs).2.trans (Nat.pow_le_pow_right (by decide) hq)
    have hspace : (encode (list nat) xs).toInput.length + 32 < 2 ^ v := by
      have hn := (hfit xs).2
      change 3 * (listToRaw nat xs).nodes ≤ _ at hn
      rw [Lax560851Proofs.RamPolynomialSeparation.natList_nodes] at hn
      rw [arena_length]
      omega
    have hlength : (encode (list nat) xs).toInput.length =
        (encode (list nat) xs).root + 4 := by
      rw [arena_length, Lax560851Proofs.RamExponentialExample.natList_root]
    obtain ⟨t, ht, hr⟩ := hprogram xs v hq
    obtain ⟨u, hu, hr'⟩ := hlower 4 (encode (list nat) xs).root
      (encode (list nat) xs).memory.toList program v (natOutput (f xs)) t
      hlength hfitTape hspace hr
    refine ⟨u, ?_, ?_⟩
    · change u ≤ newTime.eval (bitSize xs)
      have hnbit := Lax560851Proofs.RamExponentialExample.length_le_bitSize xs
      change u ≤ 18 * t + 6 * (encode (list nat) xs).toInput.length + 26 at hu
      rw [arena_length] at hu
      simp only [newTime, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega
    · simpa [hv, WordImage.toInput] using hr'

/-- Assemble both current-model classes from the old arena/native compiler
comparison and the checked same-input buffering contract. -/
theorem comparison_of_lowering
    (lower : Nat → Lax808846.Ram.Program → Lax759944Proofs.Legacy.Ram.Program)
    (hlower : CorrectLowering lower) (f : List Nat → Nat) :
    Lax560851.RamPolynomialComparison.BitPolynomialTime f ↔
      Lax759944.RamPolytime.RamPolytime (fun xs => [f xs]) := by
  constructor
  · intro hf
    apply Lax759944Proofs.LegacyRamClasses.polytime_forward
    apply (Legacy.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime f).mp
    exact arena_backward_of_lowering lower hlower hf
  · intro hf
    apply arena_forward
    apply (Legacy.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime f).mpr
    apply Lax759944Proofs.LegacyRamClasses.polytime_backward_of_lowering
      (lower 1) ?_ hf Lax560851Proofs.RamExponentialExample.length_le_bitSize
    intro p v xs output t hfit hcapacity hrun
    exact hlower 1 xs.length xs p v output t (by simp)
      hfit (by simpa [List.length_cons, Nat.add_assoc] using hcapacity) hrun

end Lax560851Proofs.TapeRamPolynomialComparison
