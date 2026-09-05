# Lax58: certified structural encodings

## What it does

Lax58 turns finite mathematical data into a predictable structural representation
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
not secretly do part of the algorithm's work. Lax58 supplies a common encoding
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
[FormulaExample](concepts/Lax58/FormulaExample.lean): it derives an encoding for
propositional formulas and constructs the word input for $p_0 \land \neg p_1$.

In a Lean package depending on Lax58:

```lean
import Lax58.CertifiedDerivationElab
import Lax58.WordArena

namespace Example

inductive Expr where
  | lit (n : Nat)
  | add (left right : Expr)

derive_certified_encoding exprRaw indexed : Expr

example : exprRaw.Laws := exprRaw.certified.checked

def input (e : Expr) : List Nat :=
  (Lax58.WordArena.encodeRaw (exprRaw e)).toInput

#print exprRaw
#print exprRaw.Laws
#print exprRaw.certified

end Example
```

Derive encodings for nonrecursive field datatypes before their containers.
The `indexed` keyword is required even when the datatype has no indices;
parameterized/indexed examples are in Lax53's `StructuralRepresentations.lean`.

Structural size counts nodes, not bits: a large natural payload still occupies
one leaf. Word-width hypotheses must cover both payloads and addresses.
Runtime costs, injectivity, and round-trip decoder proofs are separate
obligations; this command does not automatically prove them.

Run `bash scripts/check-certified.sh` for the positive and negative derivation
tests. See [CURRENT_STATE.md](CURRENT_STATE.md) for validation status and
[WORKFLOW.md](WORKFLOW.md) for development rules.
