import Lax560851.CertifiedDerivationElab
import Lax560851.WordArena

/-!
---
title: Example — structural encoding of propositional formulas
type: definition
---

A propositional formula is finite mathematical data: an atom has a natural
number as its name, a negation has one subformula, and a conjunction has two.
The example below represents this syntax directly, without evaluating the
formula or attaching information about its truth or satisfiability.

The single `derive_certified_encoding` command generates `formulaRaw`, its
complete constructor equations `formulaRaw.Laws`, and their checked witness
`formulaRaw.certified`. Atoms retain their natural indices; negation and
conjunction retain their constructor names and recursively encoded children.

For the sample formula $p_0 \land \neg p_1$, the structural description is
`conj(atom(0), neg(atom(1)))`, expressed using the fixed `Raw.constructor`
vocabulary. `sampleInput` then gives its distinguished word-arena input:
the root address followed by the three-word blocks for the structural nodes.
The same two-stage construction applies to other supported finite datatypes.
-/

namespace Lax560851.FormulaExample

open Lax560851.StructuralPresentation Lax560851.WordArena

/-- Propositional syntax with natural-number atom names. -/
inductive Formula where
  | atom (index : Nat)
  | neg (body : Formula)
  | conj (left right : Formula)

/-- Derive the structural encoder and its complete certificate together. -/
derive_certified_encoding formulaRaw indexed : Formula

/-- The formula $p_0 \land \neg p_1$. -/
def sample : Formula := .conj (.atom 0) (.neg (.atom 1))

/-- Constructor structure, before choosing a word-memory layout. -/
def sampleStructure : Raw := formulaRaw sample

/-- Exact input words, including the root address and no additional data. -/
def sampleInput : List Nat := (encodeRaw sampleStructure).toInput

end Lax560851.FormulaExample
