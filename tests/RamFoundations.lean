import Lax560851Proofs.RamExponentialExample
import Lax560851Proofs.BitPolynomialTime

open Lax808846.Ram
open Lax560851.RamPolynomialComparison
open Lax560851Proofs.RamExponentialExample

-- The program obtains the length from the arena root, not from payloads.
example : (run 16 exponentialProgram 6 (initState [60, 123, 456])).map State.out =
    some [1024] := by decide

-- RunsTo charges the explicit terminal halt after six successful transitions.
example : RunsTo 16 exponentialProgram [60, 123, 456] [1024] 7 := by
  exact exponentialProgram_runs 10 16 [123, 456] (by decide) (by decide) (by decide)

-- Empty input still has an arena root and returns one.
example : (run 4 exponentialProgram 6 (initState [0, 0, 0, 0])).map State.out =
    some [1] := by decide

example : RunsTo 4 exponentialProgram [0, 0, 0, 0] [1] 7 := by
  exact exponentialProgram_runs 0 4 [0, 0, 0] (by decide) (by decide) (by decide)

example : BitPolynomialTime exponentialLength :=
  Lax560851Proofs.RamExponentialExample.exponentialLength_bitPolynomialTime

example : ¬ Lax560851.RamComplexityExample.PolynomialTime exponentialLength :=
  Lax560851Proofs.RamPolynomialSeparation.exponentialLength_not_polynomialTime

-- The negative result rules out arbitrary time allowances, not merely polynomials.
example (timeByLength : Nat → Nat) :
    ¬ Lax560851.RamComplexityExample.TimeBounded exponentialLength timeByLength :=
  Lax560851Proofs.RamPolynomialSeparation.exponentialLength_not_timeBounded timeByLength

/-- info: 'Lax560851Proofs.RamOutputBounds.runsTo_output_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lax560851Proofs.RamOutputBounds.runsTo_output_fits

/--
info: 'Lax560851Proofs.RamExponentialExample.exponentialLength_bitPolynomialTime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lax560851Proofs.RamExponentialExample.exponentialLength_bitPolynomialTime

/--
info: 'Lax560851Proofs.RamPolynomialSeparation.exponentialLength_not_polynomialTime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lax560851Proofs.RamPolynomialSeparation.exponentialLength_not_polynomialTime

/-- info: 'Lax560851Proofs.BitPolynomialTime.using_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax560851Proofs.BitPolynomialTime.using_iff

