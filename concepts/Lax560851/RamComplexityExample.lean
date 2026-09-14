import Mathlib.Computability.Partrec
import Lax560851.RamComplexityElab

/-!
---
title: Examples — separate resource bounds and polynomial time
type: definition
---

These properties describe functions on finite sequences, without asserting
that every function satisfies them. Encodings are selected automatically.
The two-input property has linear time dependence on the first sequence's
length and computable time and word-capacity coefficients depending only on
the second sequence's length. The ordinary one-input property instead uses
a constant word-capacity coefficient. Natural payload magnitudes are included
in `inputMagnitude`, not in the sequence-length time measure.

Polynomial time below means polynomial in sequence length, under that same
constant-times-input-magnitude word-capacity convention. It is a word-RAM
notion, not a claim about polynomial time in a binary serialization. The degree
is an upper bound on the time exponent, not a claim of optimality.
-/

namespace Lax560851.RamComplexityExample

abbrev Input := List Nat × List Nat

/-- One program, linear in the first input, with computable dependence on
the second input in both resource bounds.

`timeCoefficient k` bounds the instruction allowance per first-input element
(including the extra unit for empty input), when the second input has length
`k`. `wordCoefficient k` multiplies input magnitude to give a sufficient word
capacity. Both functions depend only on that length, not on either list's
contents; they are chosen once for the algorithm. -/
def LinearInFirstInput (f : Input → Nat) : Prop :=
  ∃ timeCoefficient wordCoefficient : Nat → Nat,
    Computable timeCoefficient ∧ Computable wordCoefficient ∧
    RamComputableWithin f
      (fun x => (x.1.length + 1) * timeCoefficient x.2.length)
      (fun x => wordCoefficient x.2.length * inputMagnitude x)

/-- An explicit time allowance and a constant word-capacity coefficient. -/
def TimeBounded (f : List Nat → Nat) (timeByLength : Nat → Nat) : Prop :=
  ∃ wordCoefficient : Nat,
    RamComputableWithin f
      (fun xs => timeByLength xs.length)
      (fun xs => wordCoefficient * inputMagnitude xs)

/-- Computable in at most `timeCoefficient * (n + 1)^d` instructions on
sequences of length `n`, for some constant `timeCoefficient`. The degree `d`
is fixed before the input is supplied; degree zero permits constant time.
The sufficient word-capacity bound is the one specified by `TimeBounded`. -/
def PolynomialTimeOfDegree (f : List Nat → Nat) (d : Nat) : Prop :=
  ∃ timeCoefficient : Nat,
    TimeBounded f (fun n => timeCoefficient * (n + 1) ^ d)

/-- Polynomial-time computability with some fixed natural-number degree.
The degree and coefficients may depend on `f`, but not on the runtime input.
This retains `TimeBounded`'s word-capacity convention. -/
def PolynomialTime (f : List Nat → Nat) : Prop :=
  ∃ d : Nat, PolynomialTimeOfDegree f d

end Lax560851.RamComplexityExample
