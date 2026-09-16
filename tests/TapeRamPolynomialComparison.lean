import Lax560851Proofs.RamPolynomialComparison

example (f : List Nat → Nat) :
    Lax560851Proofs.Legacy.BitPolynomialTime f ↔
      Lax759944Proofs.Legacy.RamPolytime.RamPolytime (fun xs => [f xs]) :=
  Lax560851Proofs.Legacy.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime f

example (lower : Nat → Lax808846.Ram.Program → Lax759944Proofs.Legacy.Ram.Program)
    (hlower : Lax560851Proofs.TapeRamPolynomialComparison.CorrectLowering lower)
    (f : List Nat → Nat) :
    Lax560851.RamPolynomialComparison.BitPolynomialTime f ↔
      Lax759944.RamPolytime.RamPolytime (fun xs => [f xs]) :=
  Lax560851Proofs.TapeRamPolynomialComparison.comparison_of_lowering lower hlower f

/--
info: 'Lax560851Proofs.Legacy.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lax560851Proofs.Legacy.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime
/--
info: 'Lax560851Proofs.TapeRamPolynomialComparison.arena_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lax560851Proofs.TapeRamPolynomialComparison.arena_forward
/--
info: 'Lax560851Proofs.TapeRamPolynomialComparison.arena_backward_of_lowering' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lax560851Proofs.TapeRamPolynomialComparison.arena_backward_of_lowering
/--
info: 'Lax560851Proofs.TapeRamPolynomialComparison.comparison_of_lowering' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lax560851Proofs.TapeRamPolynomialComparison.comparison_of_lowering

-- The public equivalence uses the concrete verified compiler with no premise.
example : Lax560851Proofs.TapeRamPolynomialComparison.CorrectLowering
    Lax759944Proofs.TapeRamBufferedLegacy.lower :=
  Lax560851Proofs.RamPolynomialComparison.bufferedLowering_correct
