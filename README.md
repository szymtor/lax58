# Lax560851: certified structural encodings

## What it does

Lax560851 turns finite mathematical data into a predictable structural representation
and then into an exact sequence of machine words. Examples include:

- Logical formulas and terms, represented by their syntax and variable indices.
- Finite relational structures, such as graphs, represented by an explicitly
  numbered domain and finite relation tables.
- Other finite mathematical structures, such as trees and finite automata,
  represented by their constituent data.

These objects must first be expressed using supported finite datatypes and
fields. The representation records those constructors and fields, without
attaching precomputed answers or other derived advice through a custom encoder.

This is useful when stating algorithmic complexity: the input convention must
not secretly do part of the algorithm's work. Lax560851 supplies a common encoding
framework; the mathematics and algorithms using the data remain separate.

## How it works

The pipeline is:

`datatype value → constructor-derived Raw tree → immutable word arena`

- `Raw` has natural-number leaves and binary pairs. Fixed combinators represent
  constructor names and ordered fields.
- `derive_certified_encoding` inspects every constructor field. It accepts
  `Nat`, `Fin`, subtypes with erased proofs and certified underlying values,
  finite families, recursive children, and previously constructor-certified
  datatypes. Unsupported fields cause an elaboration error; there is no fallback
  to arbitrary `FieldEncoding` instances.
- The command generates the encoder, its complete constructor equations
  (`.Laws`), and a witness proving them (`.certified`) together. The expanded
  definitions and proofs remain inspectable and kernel-checkable.
- `WordArena.encodeRaw` stores children before parents, using three words per
  `Raw` node. Its input tape is the root address followed by the arena words:
  exactly `3 * raw.nodes + 1` words, with no extra prefix or suffix.

The closed derivation establishes where an encoding comes from; its generated
equations specify exactly what it contains. A standalone `CertifiedFieldEncoding`
record—or a private constructor—is **not** by itself an advice-freedom guarantee.
Low-level `Presentation` and `FieldEncoding` remain available for other uses.

## How to use it

For an example inside the submission, see
[FormulaExample](concepts/Lax560851/FormulaExample.lean): it derives an encoding for
propositional formulas and constructs the word input for $p_0 \land \neg p_1$.

In a Lean package depending on Lax560851:

```lean
import Lax560851.CertifiedDerivationElab
import Lax560851.WordArena

namespace Example

inductive Expr where
  | lit (n : Nat)
  | add (left right : Expr)

derive_certified_encoding exprRaw indexed : Expr

example : exprRaw.Laws := exprRaw.certified.checked

def input (e : Expr) : List Nat :=
  (Lax560851.WordArena.encodeRaw (exprRaw e)).toInput

#print exprRaw
#print exprRaw.Laws
#print exprRaw.certified

end Example
```

Derive encodings for nonrecursive field datatypes before their containers.
The `indexed` keyword is required even when the datatype has no indices;
parameterized/indexed examples are in Lax842588's `StructuralRepresentations.lean`.

Structural size counts nodes, not bits: a large natural payload still occupies
one leaf. Word-width hypotheses must cover both payloads and addresses.
Runtime costs, injectivity, and round-trip decoder proofs are separate
obligations; this command does not automatically prove them.

## Stating RAM complexity

Import `Lax560851.RamComplexityElab` and supply a mathematical function and two
explicit resource bounds:

```lean
import Mathlib.Computability.Partrec
import Lax560851.RamComplexityElab

def LinearInFirstInput (f : List Nat × List Nat → Nat) : Prop :=
  ∃ timeCoefficient wordCoefficient : Nat → Nat,
    Computable timeCoefficient ∧ Computable wordCoefficient ∧
    RamComputableWithin f
      (fun x => (x.1.length + 1) * timeCoefficient x.2.length)
      (fun x => wordCoefficient x.2.length * inputMagnitude x)
```

This specifies one program with the indicated instruction bound at every
sufficient word width. The third argument bounds required **word capacity**
(`wordBound x ≤ 2 ^ w`), not the number of bits. Payloads and input addresses
must also fit. `inputMagnitude x` is the selected representation's node count
plus its largest natural payload plus one. Neither computability nor a growth
restriction on the bounds is implicit; quantify coefficients as in this example.

`timeCoefficient k` supplies the time multiplier when the second sequence has
length `k`; `wordCoefficient k` supplies the sufficient-capacity multiplier.
They are computable functions of that length alone, chosen once for the
algorithm. The example concept also defines `PolynomialTimeOfDegree f d`
using time `timeCoefficient * (n + 1)^d`, and `PolynomialTime f` by existentially
quantifying `d`. Both retain `TimeBounded`'s constant-times-input-magnitude
word-capacity convention; sequence length is the time measure, not bit length.

The frontend selects approved encodings without consulting user instances.
Inputs use arenas. `Nat` outputs are `[n]`, `Bool` outputs are `[0]` or `[1]`,
and other supported outputs use arenas. Output production counts toward time.
Registered constructor encoders can be composed with the fixed Nat/list/product
vocabulary, proof-erased subtypes, and finite families. Unsupported types and
genuinely dependent result types are rejected; bundle dependent data into a
supported input datatype first.

The expanded proposition is `Lax560851.RamComplexity.RamComputableWithinUsing`,
with both encodings explicit and inspectable. It is a low-level relative
predicate, not itself an encoding certificate. See
[RamComplexityExample](concepts/Lax560851/RamComplexityExample.lean) for the
two-input and ordinary size-based examples. This layer uses the existing
[Lax808846 machine model](https://laxarchive.org/lax-808846/Lax808846.Ram.html),
with immutable indexed input, sequential input access, and append-only output.
Its instruction count includes a fetched final `halt` or exhausted `read`.

## Polynomial time measured in bits

`Lax560851.RamPolynomialComparison.BitPolynomialTime f` keeps arena input and
one-word natural output, but bounds time and sufficient **word length in bits**
by polynomials in `Lax759944.BinaryWordEncoding.bitSize xs`. This size counts a
separator per entry and the entry's binary digits. The underlying reusable
`BitPolynomialTimeUsing` accepts an explicit presentation, output encoding,
and size measure. It instantiates `RamComputableWithinUsing` with capacity
`2 ^ wordBits.eval (inputSize x)` and requires the input to fit at that width.

The concept includes `exponentialLength xs = 2 ^ xs.length`. Its positive
bit-polynomial proof uses seven RAM instructions, including its final `halt`,
and sufficient width `bitSize xs + 4`. Its negative proof rules out the existing
linear-capacity `TimeBounded` property for **every** time allowance, hence also rules out
`PolynomialTime`. Both proofs use only Lean's permitted background axioms.

The general equivalence with Lax759944's explicit, length-prefixed input
convention now covers every Lax808846 instruction. A verified compiler buffers
the immutable input tape and preserves indexed access, sequential reads, input
length, EOF branches, and exact output. The earlier sequential-input machine
and tape adapters remain internal checked proof helpers.

For source time polynomial `T` and sufficient-width polynomial `Q`, the
composed arena-to-native witnesses are `1188*T + 2382*X + 3382` and `Q + 14`.
The native-to-arena witnesses are `324*T + 108*X + 603` and `Q + 14`.
Both directions can add linear startup time; the class theorem does not
require equal polynomial degrees. See [CURRENT_STATE.md](CURRENT_STATE.md)
for the completed checks and remaining archive validation.

Run `bash scripts/check-certified.sh` for the positive and negative derivation
tests. See [CURRENT_STATE.md](CURRENT_STATE.md) for validation status and
[WORKFLOW.md](WORKFLOW.md) for development rules.
