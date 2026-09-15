import Lax560851.RamPolynomialComparison
import Lax560851Proofs.BitPolynomialTime
import Lax560851Proofs.RamOutputBounds
import Lax560851Proofs.RamExponentialExample
import Lax560851Proofs.RamArenaToNativeSimulation
import Lax560851Proofs.RamNativeToArenaSimulation

namespace Lax560851Proofs.RamPolynomialComparison

open Lax865980.Ram
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators
open Lax560851.RamComplexity Lax560851.RamPolynomialComparison
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

theorem list_payloads_fit_iff (xs : List Nat) (w : Nat) :
    (listToRaw nat xs).PayloadsFitInWord w ↔ ∀ value ∈ xs, value < 2 ^ w := by
  induction xs with
  | nil => simp [listToRaw, Raw.PayloadsFitInWord, Raw.maxNat]
  | cons value rest ih =>
      change max value (listToRaw nat rest).maxNat < 2 ^ w ↔ _
      change (listToRaw nat rest).maxNat < 2 ^ w ↔ _ at ih
      rw [max_lt_iff, ih]
      simp

private theorem capacity64 {w : Nat} (hw : 7 ≤ w) : 64 ≤ 2 ^ w := by
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw
  norm_num at hpow ⊢
  omega

/--
---
conclusion: Lax560851.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime
---
The two tape presentations are compiled into one another. If `T` and `Q` are
the source time and sufficient-width polynomials, the arena-to-native
translation uses time `66*T + 6*X + 81` and width `Q + 7`; the
native-to-arena translation uses time `18*T + 26` and width `Q + 7`.

Thus a nonconstant time degree is preserved, while arena-to-native conversion
can raise degree zero to degree one because the current adapter buffers the
input in linear startup time. Width degree is unchanged for nonconstant `Q`.
Each implication chooses its own witnesses: this theorem neither states nor
uses equality of polynomial degrees across the two directions.
-/
theorem bitPolynomialTime_iff_ramPolytime (f : List Nat → Nat) :
    BitPolynomialTime f ↔ Lax759944.RamPolytime.RamPolytime (fun xs => [f xs]) := by
  constructor
  · intro hbit
    rcases (Lax560851Proofs.BitPolynomialTime.using_iff
      (list nat) natOutput bitSize f).mp hbit with
      ⟨wordBits, time, program, hfit, hprogram⟩
    let nativeWordBits := wordBits + Polynomial.C 7
    let nativeTime := Polynomial.C 66 * time + Polynomial.C 6 * Polynomial.X +
      Polynomial.C 81
    refine ⟨RamNativeToArenaCompiler.compile program, nativeWordBits,
      nativeTime, ?_⟩
    intro xs
    let inputBits := bitSize xs
    have hwidthEval : nativeWordBits.eval inputBits =
        wordBits.eval inputBits + 7 := by
      simp [nativeWordBits]
    have hcapacityIncrease : 2 ^ wordBits.eval inputBits ≤
        2 ^ nativeWordBits.eval inputBits := by
      apply Nat.pow_le_pow_right (by decide)
      rw [hwidthEval]
      omega
    have hnodes := (hfit xs).2
    have hlength : xs.length < 2 ^ wordBits.eval inputBits := by
      dsimp [inputBits]
      change 3 * (listToRaw nat xs).nodes ≤ _ at hnodes
      rw [Lax560851Proofs.RamPolynomialSeparation.natList_nodes] at hnodes
      omega
    have hpayloads : ∀ value ∈ xs,
        value < 2 ^ wordBits.eval inputBits :=
      (list_payloads_fit_iff xs _).mp (hfit xs).1
    obtain ⟨sourceTime, hsourceTime, hsourceRun⟩ :=
      hprogram xs (wordBits.eval inputBits) (by rfl)
    have houtput : f xs < 2 ^ wordBits.eval inputBits :=
      Lax560851Proofs.RamOutputBounds.runsTo_output_fits hsourceRun (f xs)
        (by simp [natOutput])
    constructor
    · intro value hmember
      rcases List.mem_append.mp hmember with hmember | hmember
      · rcases List.mem_cons.mp hmember with hmember | hmember
        · subst value
          exact hlength.trans_le hcapacityIncrease
        · exact (hpayloads value hmember).trans_le hcapacityIncrease
      · have : value = f xs := by simpa using hmember
        subst value
        exact houtput.trans_le hcapacityIncrease
    · intro w hw
      have hnativeWidth : nativeWordBits.eval inputBits ≤ w := hw
      have hwSeven : 7 ≤ w := by rw [hwidthEval] at hnativeWidth; omega
      let sourceWidth := w - 1
      have hsourceWidth : sourceWidth + 1 = w := by
        dsimp [sourceWidth]
        omega
      have hwordBitsSource : wordBits.eval inputBits ≤ sourceWidth := by
        dsimp [sourceWidth]
        rw [hwidthEval] at hnativeWidth
        omega
      obtain ⟨logicalTime, hlogicalTime, hlogicalRun⟩ :=
        hprogram xs sourceWidth hwordBitsSource
      have hroot : 6 * xs.length < 2 ^ sourceWidth := by
        have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hwordBitsSource
        exact (by
          dsimp [inputBits]
          change 3 * (listToRaw nat xs).nodes ≤ _ at hnodes
          rw [Lax560851Proofs.RamPolynomialSeparation.natList_nodes] at hnodes
          omega : 6 * xs.length < 2 ^ wordBits.eval inputBits).trans_le hpow
      have hpayloadsSource : ∀ value ∈ xs, value < 2 ^ sourceWidth := by
        intro value hmember
        exact (hpayloads value hmember).trans_le
          (Nat.pow_le_pow_right (by decide) hwordBitsSource)
      rcases RamNativeToArenaSimulation.runsTo_compile
          (v := sourceWidth) (program := program) (values := xs)
          (capacity64 (by omega)) hroot hpayloadsSource hlogicalRun with
        ⟨physicalTime, hphysicalTime, hphysicalRun⟩
      refine ⟨physicalTime, ?_, ?_⟩
      · simp [nativeTime]
        have hbits := Lax560851Proofs.RamExponentialExample.length_le_bitSize xs
        omega
      · simpa [hsourceWidth] using! hphysicalRun
  · intro hnative
    rcases hnative with ⟨program, wordBits, time, hprogram⟩
    let arenaWordBits := wordBits + Polynomial.C 7
    let arenaTime := Polynomial.C 18 * time + Polynomial.C 26
    apply (Lax560851Proofs.BitPolynomialTime.using_iff
      (list nat) natOutput bitSize f).mpr
    refine ⟨arenaWordBits, arenaTime,
      RamArenaToNativeCompiler.compile program, ?_, ?_⟩
    · intro xs
      let inputBits := bitSize xs
      have hwidthEval : arenaWordBits.eval inputBits =
          wordBits.eval inputBits + 7 := by simp [arenaWordBits]
      have hfitNative := (hprogram xs).1
      have hlength : xs.length < 2 ^ wordBits.eval inputBits :=
        hfitNative xs.length (by simp)
      have hpayloads : ∀ value ∈ xs,
          value < 2 ^ wordBits.eval inputBits := by
        intro value hmember
        exact hfitNative value (by simp [hmember])
      constructor
      · apply (list_payloads_fit_iff xs _).mpr
        intro value hmember
        exact (hpayloads value hmember).trans_le
          (Nat.pow_le_pow_right (by decide) (by rw [hwidthEval]; omega))
      · change 3 * (listToRaw nat xs).nodes ≤ _
        rw [Lax560851Proofs.RamPolynomialSeparation.natList_nodes, hwidthEval,
          pow_add]
        norm_num
        have hpow := Nat.two_pow_pos (wordBits.eval inputBits)
        nlinarith
    · intro xs w hw
      let inputBits := bitSize xs
      have hwidthEval : arenaWordBits.eval inputBits =
          wordBits.eval inputBits + 7 := by simp [arenaWordBits]
      have hwSeven : 7 ≤ w := by rw [hwidthEval] at hw; omega
      let sourceWidth := w - 1
      have hsourceWidth : sourceWidth + 1 = w := by
        dsimp [sourceWidth]
        omega
      have hwordBitsSource : wordBits.eval inputBits ≤ sourceWidth := by
        dsimp [sourceWidth]
        rw [hwidthEval] at hw
        omega
      obtain ⟨logicalTime, hlogicalTime, hlogicalRun⟩ :=
        (hprogram xs).2 sourceWidth hwordBitsSource
      have hfitNative := (hprogram xs).1
      have hlength : xs.length < 2 ^ sourceWidth :=
        (hfitNative xs.length (by simp)).trans_le
          (Nat.pow_le_pow_right (by decide) hwordBitsSource)
      have hroot : 6 * xs.length < 2 ^ (sourceWidth + 1) := by
        have hsmall : 6 * xs.length < 2 ^ (wordBits.eval inputBits + 3) := by
          rw [pow_add]
          norm_num
          have hpositive := Nat.two_pow_pos (wordBits.eval inputBits)
          have hnativeLength := hfitNative xs.length (by simp)
          nlinarith
        exact hsmall.trans_le (Nat.pow_le_pow_right (by decide) (by
          dsimp [sourceWidth]
          rw [hwidthEval] at hw
          omega))
      rcases RamArenaToNativeSimulation.runsTo_compile
          (v := sourceWidth) (program := program) (values := xs)
          (by
            have h64 := capacity64 (w := sourceWidth + 1) (by omega)
            omega) hlength hroot hlogicalRun with
        ⟨physicalTime, hphysicalTime, hphysicalRun⟩
      refine ⟨physicalTime, ?_, ?_⟩
      · simp [arenaTime]
        omega
      · simpa [hsourceWidth, natOutput] using hphysicalRun

end Lax560851Proofs.RamPolynomialComparison
