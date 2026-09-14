import Lax560851Proofs.RamExponentialExample
import Lax560851Proofs.BitPolynomialTime
import Lax560851Proofs.RamPolynomialComparison

open Lax865980.Ram
open Lax560851.RamPolynomialComparison
open Lax560851Proofs.RamExponentialExample

-- The program obtains the length from the arena root, not from payloads.
example : (run 16 exponentialProgram 6 (initState [60, 123, 456])).map State.out =
    some [1024] := by decide

-- Empty input still has an arena root and returns one.
example : (run 4 exponentialProgram 6 (initState [0, 0, 0, 0])).map State.out =
    some [1] := by decide

example : BitPolynomialTime exponentialLength :=
  Lax560851Proofs.RamExponentialExample.exponentialLength_bitPolynomialTime

-- The arena and length-prefixed notions define the same polynomial-time
-- class. The two implications may choose unrelated polynomial degrees.
example (f : List Nat → Nat) :
    BitPolynomialTime f ↔
      Lax759944.RamPolytime.RamPolytime (fun xs => [f xs]) :=
  Lax560851Proofs.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime f

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

/--
info: 'Lax560851Proofs.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lax560851Proofs.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime
