import Lax560851.RamPolynomialComparison
import Lax759944Proofs.Legacy.RamPolytime

/-!
Proof-internal arena polynomial-time class for the historical sequential RAM.
The sufficient-width form is the proved unfolding of the former public
capacity predicate. Only the predicate is retained; no historical statement is
assumed. The public predicates use Lax808846 directly.
-/

namespace Lax560851Proofs.Legacy

open Lax560851.StructuralPresentation Lax560851.StructuralCombinators
open Lax560851.WordArena Lax560851.RamComplexity
open Lax759944.BinaryWordEncoding

/-- One legacy program, polynomial sufficient width and time, on the exact
natural-list arena. The arena fits already at the sufficient width. -/
def BitPolynomialTime (f : List Nat → Nat) : Prop :=
  ∃ (wordBits time : Polynomial Nat) (program : Lax759944Proofs.Legacy.Ram.Program),
    (∀ xs, (listToRaw nat xs).PayloadsFitInWord (wordBits.eval (bitSize xs)) ∧
      3 * (listToRaw nat xs).nodes ≤ 2 ^ wordBits.eval (bitSize xs)) ∧
    ∀ xs w, wordBits.eval (bitSize xs) ≤ w →
      ∃ t ≤ time.eval (bitSize xs),
        Lax759944Proofs.Legacy.Ram.RunsTo w program
          (encode (list nat) xs).toInput (natOutput (f xs)) t

end Lax560851Proofs.Legacy
