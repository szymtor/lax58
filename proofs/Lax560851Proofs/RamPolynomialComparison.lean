import Lax560851Proofs.TapeRamPolynomialComparison
import Lax759944Proofs.TapeRamBufferedSimulation
import Lax759944Proofs.TapeRamBufferedLegacy

namespace Lax560851Proofs.RamPolynomialComparison

open Lax560851.RamPolynomialComparison

/-- The existing presentation lemma is independent of the machine model. -/
theorem list_payloads_fit_iff (xs : List Nat) (w : Nat) :
    (Lax560851.StructuralCombinators.listToRaw
      Lax560851.StructuralCombinators.nat xs).PayloadsFitInWord w ↔
      ∀ value ∈ xs, value < 2 ^ w :=
  Legacy.RamPolynomialComparison.list_payloads_fit_iff xs w

/-- Buffer the dedicated input tape, simulate every current instruction, then
project the generated legacy instruction subset to its checked semantics. -/
theorem bufferedLowering_correct :
    TapeRamPolynomialComparison.CorrectLowering
      Lax759944Proofs.TapeRamBufferedLegacy.lower := by
  intro extra header tail program v output time hlength hfit hcapacity hrun
  obtain ⟨physicalTime, htime, hphysical⟩ :=
    Lax759944Proofs.TapeRamBufferedSimulation.runsTo_compile
      hlength hfit hcapacity hrun
  obtain ⟨legacyTime, hlegacyTime, hlegacy⟩ :=
    Lax759944Proofs.TapeRamBufferedLegacy.runsTo_lower hphysical
  exact ⟨legacyTime, hlegacyTime.trans htime, hlegacy⟩

/--
---
conclusion: Lax560851.RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime
---
The two input presentations define the same polynomial-time class for the
full Lax808846 instruction set, including indexed input and EOF tests.
The checked buffering compiler preserves the source input and output tapes;
the internal legacy compilers then convert between the two presentations.

If `T` and `Q` are the source time and sufficient-width polynomials, the
composed arena-to-native witnesses are `1188*T + 2382*X + 3382` and `Q + 14`.
The native-to-arena witnesses are `324*T + 108*X + 603` and `Q + 14`.
Both directions can introduce a linear startup term. Each implication chooses
its own witnesses; no equality of polynomial degrees is stated or used.
-/
theorem bitPolynomialTime_iff_ramPolytime (f : List Nat → Nat) :
    BitPolynomialTime f ↔ Lax759944.RamPolytime.RamPolytime (fun xs => [f xs]) :=
  TapeRamPolynomialComparison.comparison_of_lowering
    Lax759944Proofs.TapeRamBufferedLegacy.lower bufferedLowering_correct f

end Lax560851Proofs.RamPolynomialComparison
