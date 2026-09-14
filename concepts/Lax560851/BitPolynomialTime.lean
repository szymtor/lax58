import Lax560851.RamComplexity
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
---
title: Polynomial time with polynomial word length
type: definition
---

This variant bounds both running time and sufficient word length by
polynomials in a specified input size, normally its binary size. Input still
uses the distinguished structural arena. A bound of `q` bits means capacity
`2 ^ q`, so this is an instance of the existing RAM resource predicate, not
a different machine model.

The arena must fit already at the stated sufficient width. This prevents
oversized payloads from making the guarantee vacuous. The one program works
at every larger width, and must produce the exact encoded output.

In contrast, `RamComplexityExample.PolynomialTime` measures time in sequence
length and permits only a constant-times-input-magnitude capacity threshold.
Polynomially many sufficient bits can accommodate exponentially large
natural-number outputs; that linear capacity convention cannot in general.
-/

namespace Lax560851.BitPolynomialTime

open Lax560851.StructuralPresentation Lax560851.WordArena Lax560851.RamComplexity

universe u v

/-- Polynomial instruction count and polynomial sufficient word length,
relative to a presentation, output encoding, and input-size measure.
Both polynomials are chosen once, independently of the input and runtime
word width. The input remains a root word followed by its structural arena. -/
def BitPolynomialTimeUsing {α : Type u} {β : Type v}
    (input : Presentation α) (output : β → List Nat)
    (inputSize : α → Nat) (f : α → β) : Prop :=
  ∃ wordBits time : Polynomial Nat,
    (∀ x, (input.toRaw x).PayloadsFitInWord (wordBits.eval (inputSize x)) ∧
      3 * (input.toRaw x).nodes ≤ 2 ^ wordBits.eval (inputSize x)) ∧
    RamComputableWithinUsing input output f
      (fun x => time.eval (inputSize x))
      (fun x => 2 ^ wordBits.eval (inputSize x))

end Lax560851.BitPolynomialTime
