import Lax560851.BitPolynomialTime
import Lax560851.RamComplexityExample
import Lax759944.RamPolytime

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
output. It agrees with Lax759944's convention, whose input is instead the native
length-prefixed sequence. The agreement requires explicit efficient encoding
conversions; it is not a definitional identification of the two input tapes.

The input conversions must preserve both indexed access to the original
input and sequential reads, including EOF. Buffering an input can contribute
linear startup time in either direction. The theorem asserts equivalence of
the existential polynomial-time classes only: it does not require the two
time witnesses, or their degrees, to match. Terminal instructions are charged
according to the Lax808846 machine semantics.

`RamComplexityExample.PolynomialTime` instead bounds time polynomially in
`n` and requires correctness whenever capacity exceeds a constant times
input magnitude (and the arena fits). The difference in capacity matters
even on all-zero inputs, where `B=n`: the exact result `2^n` fits in `n+1`
bits but cannot fit at all admissible logarithmic word widths. Thus the
example below satisfies the bit-polynomial convention but not the
length-polynomial, linear-capacity convention.
-/

namespace Lax560851.RamPolynomialComparison

open Lax560851.StructuralCombinators Lax560851.RamComplexity

/-- Polynomial time and sufficient word length in the binary size of a
natural-number sequence; input uses its distinguished structural arena. -/
def BitPolynomialTime (f : List Nat → Nat) : Prop :=
  Lax560851.BitPolynomialTime.BitPolynomialTimeUsing (list nat) natOutput
    Lax759944.BinaryWordEncoding.bitSize f

/-- A small exact-output example, independent of all input payloads. -/
def exponentialLength (xs : List Nat) : Nat := 2 ^ xs.length

/-- Arena input and native length-prefixed input yield the same
bit-polynomial computability class for natural-number outputs. This is a class
equivalence, not a same-degree equivalence. -/
axiom bitPolynomialTime_iff_ramPolytime (f : List Nat → Nat) :
  BitPolynomialTime f ↔ Lax759944.RamPolytime.RamPolytime (fun xs => [f xs])

axiom exponentialLength_bitPolynomialTime : BitPolynomialTime exponentialLength

axiom exponentialLength_not_polynomialTime :
  ¬ Lax560851.RamComplexityExample.PolynomialTime exponentialLength

end Lax560851.RamPolynomialComparison
