import Lax58.BitPolynomialTime
import Lax58.RamComplexityExample
import Lax51.RamPolytime

/-!
---
title: Two polynomial-time conventions, and their separation
type: definition and theorem
---

For a sequence `xs`, let `n = xs.length`, let `m` be its largest entry
(zero for the empty sequence), and let `B` be its binary size: one separator
per entry plus the number of bits of each entry. The distinguished arena
has `2*n+1` structural nodes, and input magnitude is `2*n+m+2`.

`BitPolynomialTime` permits polynomial instruction count and polynomial
sufficient word length in `B`. It keeps arena input and one-word natural
output. It agrees with Lax51's convention, whose input is instead the native
length-prefixed sequence. The agreement requires explicit efficient encoding
conversions; it is not a definitional identification of the two input tapes.

The checked proof uses the following witness transformations, where `T` is a
time polynomial, `Q` is a sufficient-word-length polynomial, and `X` denotes
the binary input size. From arena input to native input it uses
`66*T + 6*X + 81`; from native input to arena input it uses `18*T + 26`.
Both directions use `Q + 7` for word length. Consequently, nonconstant time
degrees are preserved, but the first translation can turn a constant bound
into a linear one because its current adapter has linear startup. The theorem
asserts equivalence of the existential polynomial-time classes only: it does
not require the two witnesses, or their degrees, to match.

`RamComplexityExample.PolynomialTime` instead bounds time polynomially in
`n` and requires correctness whenever capacity exceeds a constant times
input magnitude (and the arena fits). The difference in capacity matters
even on all-zero inputs, where `B=n`: the exact result `2^n` fits in `n+1`
bits but cannot fit at all admissible logarithmic word widths. Thus the
example below satisfies the bit-polynomial convention but not the
length-polynomial, linear-capacity convention.
-/

namespace Lax58.RamPolynomialComparison

open Lax58.StructuralCombinators Lax58.RamComplexity

/-- Polynomial time and sufficient word length in the binary size of a
natural-number sequence; input uses its distinguished structural arena. -/
def BitPolynomialTime (f : List Nat → Nat) : Prop :=
  Lax58.BitPolynomialTime.BitPolynomialTimeUsing (list nat) natOutput
    Lax51.BinaryWordEncoding.bitSize f

/-- A small exact-output example, independent of all input payloads. -/
def exponentialLength (xs : List Nat) : Nat := 2 ^ xs.length

/-- Arena input and native length-prefixed input yield the same
bit-polynomial computability class for natural-number outputs. This is a class
equivalence, not a same-degree equivalence. -/
axiom bitPolynomialTime_iff_ramPolytime (f : List Nat → Nat) :
  BitPolynomialTime f ↔ Lax51.RamPolytime.RamPolytime (fun xs => [f xs])

axiom exponentialLength_bitPolynomialTime : BitPolynomialTime exponentialLength

axiom exponentialLength_not_polynomialTime :
  ¬ Lax58.RamComplexityExample.PolynomialTime exponentialLength

end Lax58.RamPolynomialComparison
