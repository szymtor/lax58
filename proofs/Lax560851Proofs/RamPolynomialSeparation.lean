import Lax560851.RamPolynomialComparison
import Lax560851Proofs.RamOutputBounds
import Mathlib.Tactic.Linarith

namespace Lax560851Proofs.RamPolynomialSeparation

open Lax560851.StructuralPresentation Lax560851.StructuralCombinators
open Lax560851.RamComplexity Lax560851.RamComplexityExample Lax560851.RamPolynomialComparison

theorem natList_nodes (xs : List Nat) :
    (listToRaw nat xs).nodes = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 1 + (listToRaw nat xs).nodes + 1 = 2 * (xs.length + 1) + 1
    omega

theorem zeroList_maxNat (n : Nat) :
    (listToRaw nat (List.replicate n 0)).maxNat = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change max 0 (listToRaw nat (List.replicate n 0)).maxNat = 0
    simp [ih]

/-- No time allowance can compensate for the small admissible word width
on zero lists. The contradiction uses a concrete width, not an asymptotic
assertion about logarithms. -/
theorem exponentialLength_not_timeBounded (timeByLength : Nat → Nat) :
    ¬ TimeBounded exponentialLength timeByLength := by
  rintro ⟨wordCoefficient, h⟩
  let k := 4 * wordCoefficient + 8
  let n := 2 * k
  let xs := List.replicate n 0
  have hn : xs.length = n := List.length_replicate
  have hnodes : ((list nat).toRaw xs).nodes = 2 * n + 1 := by
    simpa [list, hn] using natList_nodes xs
  have hmax : ((list nat).toRaw xs).maxNat = 0 := zeroList_maxNat n
  have hpow := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
  have hsize : 3 * ((list nat).toRaw xs).nodes ≤ 2 ^ n := by
    rw [hnodes]
    dsimp [n]
    have hk : 8 ≤ k := by dsimp [k]; omega
    nlinarith
  have hcapacity : wordCoefficient * inputMagnitudeUsing (list nat) xs ≤ 2 ^ n := by
    simp only [inputMagnitudeUsing, hnodes, hmax, Nat.add_zero]
    dsimp [n]
    have hk : 4 * wordCoefficient + 8 = k := rfl
    nlinarith
  have hout := RamOutputBounds.within_nat_output_lt h xs n
    (by simp [Raw.PayloadsFitInWord, hmax]) hsize hcapacity
  simp only [exponentialLength, hn] at hout
  exact (Nat.lt_irrefl _ hout)

/--
---
conclusion: Lax560851.RamPolynomialComparison.exponentialLength_not_polynomialTime
---
The all-zero input of a sufficiently large even length admits that same
length as a word width, yet its exact exponential output does not fit.
This defeats every constant capacity coefficient, regardless of time.
-/
theorem exponentialLength_not_polynomialTime :
    ¬ PolynomialTime exponentialLength := by
  rintro ⟨degree, timeCoefficient, h⟩
  exact exponentialLength_not_timeBounded _ h

end Lax560851Proofs.RamPolynomialSeparation
