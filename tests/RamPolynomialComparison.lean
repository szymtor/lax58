import Lax560851Proofs.RamPolynomialComparison

open Lax560851.RamPolynomialComparison

-- The arena and length-prefixed notions define the same polynomial-time
-- class. The two implications may choose unrelated polynomial degrees.
example (f : List Nat → Nat) :
    BitPolynomialTime f ↔
      Lax759944.RamPolytime.RamPolytime (fun xs => [f xs]) :=
  Lax560851Proofs.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime f

/--
info: 'Lax560851Proofs.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lax560851Proofs.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime
