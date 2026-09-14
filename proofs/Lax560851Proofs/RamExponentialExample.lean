import Lax560851.RamPolynomialComparison
import Lax560851Proofs.RamPolynomialSeparation
import Lax560851Proofs.WordArena
import Mathlib.Data.Nat.Size

namespace Lax560851Proofs.RamExponentialExample

open Lax865980.Ram Lax865980.RamComputes
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators Lax560851.WordArena
open Lax560851.RamComplexity Lax560851.RamPolynomialComparison
open Lax759944.BinaryWordEncoding

-- These elementary size facts use the same binary encoding as Lax759944.
theorem bitSize_cons (a : Nat) (xs : List Nat) :
    bitSize (a :: xs) = a.bits.length + 1 + bitSize xs := by
  simp [bitSize, Lax759944.BinaryWordEncoding.encode, encodeNat,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem length_le_bitSize (xs : List Nat) : xs.length ≤ bitSize xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem natList_maxNat_lt (xs : List Nat) :
    (listToRaw nat xs).maxNat < 2 ^ bitSize xs := by
  induction xs with
  | nil => decide
  | cons a xs ih =>
    simp only [listToRaw, Raw.maxNat, nat, max_lt_iff, bitSize_cons]
    constructor
    · have ha : a < 2 ^ a.bits.length := by
        rw [Nat.size_eq_bits_len]
        exact Nat.lt_size_self a
      exact ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    · exact ih.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

theorem natList_root (xs : List Nat) :
    (encode (list nat) xs).root = 6 * xs.length := by
  have hroot := Lax560851Proofs.WordArena.encodeRaw_root_last ((list nat).toRaw xs)
  have hsize := Lax560851Proofs.WordArena.encodeRaw_memoryWords_proof ((list nat).toRaw xs)
  rw [hsize] at hroot
  change (encode (list nat) xs).root + 3 = 3 * (listToRaw nat xs).nodes at hroot
  rw [RamPolynomialSeparation.natList_nodes] at hroot
  omega

/-- Read the root (= six times the length), divide by six, and shift one.
The remaining arena tape need not be read because the answer ignores payloads. -/
def exponentialProgram : Program :=
  [.read 0, .set 1 6, .div 0 0 1, .set 1 1, .shiftl 0 1 0, .write 0, .halt]

theorem exponentialProgram_runs (n w : Nat) (rest : List Nat)
    (hroot : 6 * n < 2 ^ w) (hsix : 6 < 2 ^ w) (houtput : 2 ^ n < 2 ^ w) :
    RunsTo w exponentialProgram (6 * n :: rest) [2 ^ n] 6 := by
  have hzero : 0 % 2 ^ w = 0 := Nat.zero_mod _
  have hone : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by omega)
  have hn : n < 2 ^ w := by omega
  simp only [RunsTo, exponentialProgram, run, step, initState, Instr.effect,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.head?_cons, List.tail_cons,
    Option.bind_some, Option.map_some, setCell, hzero, hone, Nat.mod_eq_of_lt hroot,
    Nat.mod_eq_of_lt hsix]
  norm_num [Nat.mul_div_right, Nat.mul_div_left, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt houtput]

/--
---
conclusion: Lax560851.RamPolynomialComparison.exponentialLength_bitPolynomialTime
---
Six executed RAM instructions suffice. A sufficient word length is binary
input size plus four, which fits the arena, the literal six, and the output.
-/
theorem exponentialLength_bitPolynomialTime : BitPolynomialTime exponentialLength := by
  refine ⟨Polynomial.X + Polynomial.C 4, Polynomial.C 6, ?_, ?_⟩
  · intro xs
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have hlen := length_le_bitSize xs
    have hpow := Nat.lt_two_pow_self (n := bitSize xs)
    constructor
    · exact (natList_maxNat_lt xs).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    · change 3 * (listToRaw nat xs).nodes ≤ _
      rw [RamPolynomialSeparation.natList_nodes, pow_add]
      norm_num
      nlinarith
  · refine ⟨exponentialProgram, ?_⟩
    intro xs w _ hspace hwidth input hinput
    have hw : bitSize xs + 4 ≤ w := by
      simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        Nat.pow_le_pow_iff_right (by decide : 1 < 2)] using hwidth
    have hsix : 6 < 2 ^ w := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 4 ≤ w by omega)
      norm_num at this
      omega
    have hroot : 6 * xs.length < 2 ^ w := by
      change 3 * (listToRaw nat xs).nodes ≤ _ at hspace
      rw [RamPolynomialSeparation.natList_nodes] at hspace
      omega
    have houtput : 2 ^ xs.length < 2 ^ w :=
      Nat.pow_lt_pow_right (by decide) (by have := length_le_bitSize xs; omega)
    have heq : input = (encode (list nat) xs).toInput := by simpa using hinput
    subst input
    refine ⟨6, by simp, ?_⟩
    change RunsTo w exponentialProgram
      ((encode (list nat) xs).root :: (encode (list nat) xs).memory.toList)
      [2 ^ xs.length] 6
    rw [natList_root]
    exact exponentialProgram_runs _ _ _ hroot hsix houtput

end Lax560851Proofs.RamExponentialExample
