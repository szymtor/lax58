# Current Proposal for Lax-58

## Purpose

Lax-58 should provide a neutral, human-reviewable input representation for
finite constructor data and a compact immutable realization of that
representation in word memory.

The intended chain is:

```text
Lean inductive value
    → certified constructor-structural representation
    → distinguished word arena
    → downstream computation
```

The central complexity-theoretic requirement is that the assumed input must
not contain hidden preprocessing or advice.

## 1. Universal structural data

Use a small universal structural datatype:

```lean
inductive Raw where
  | nat  : Nat → Raw
  | pair : Raw → Raw → Raw
```

Expose at least:

```lean
Raw.nodes  : Raw → Nat
Raw.maxNat : Raw → Nat
```

`Raw.nodes` measures combinatorial structure. `Raw.maxNat` measures the
magnitude of primitive payloads. These quantities must remain separate: a
large natural number is one structural node but may require a wider machine
word.

## 2. General presentations remain low-level infrastructure

Retain the general notion:

```lean
structure Presentation (α : Type) where
  toRaw   : α → Raw
  fromRaw : Raw → Option α
```

with separate properties such as:

```lean
Presentation.Lawful
Presentation.Faithful
Presentation.structuralSize
Presentation.PayloadsFitInWord
```

An arbitrary `Presentation α` is **not** automatically an admissible input
representation for a complexity theorem. Its `toRaw` function could compute
and attach satisfiability, treewidth, an index, or other expensive advice.

Lawfulness, injectivity, computability, and linear output size do not by
themselves exclude this possibility.

## 3. Structurality is certified by constructor equations

A representation qualifies as the neutral structural baseline only when
kernel-checked equations completely determine its output constructor by
constructor.

For example, a formula presentation must satisfy equations conceptually of
the following form:

```text
P.toRaw (atom n)   = AtomStruct(n)
P.toRaw (neg φ)    = NegStruct(P.toRaw φ)
P.toRaw (and φ ψ)  = AndStruct(P.toRaw φ, P.toRaw ψ)
```

The right-hand sides may contain only:

- the small fixed base primitives supplied by Lax-58, initially `Nat` and
  finite indices;
- fixed Lax-58 structural combinators;
- representations that themselves carry appropriate structurality
  certificates;
- recursive representations of recursive occurrences of the datatype being
  certified.

Because these equations determine the entire output, an additional advice bit
would make them false. This is a semantic, kernel-checkable guarantee rather
than a restriction on the source syntax of `toRaw`.

The guarantee is relative to the source datatype and its designated primitive
fields. If advice is already stored as a field of the source value, structural
representation cannot and should not erase it.

This condition is transitively closed: calling an arbitrary complicated type
"primitive" does not bypass structural certification.

## 4. Certificates are datatype-specific for now

Lax-58 cannot define one nontrivial universal certificate for arbitrary
`α`: it does not know the constructors of `α`. A generic structure containing
an arbitrary user-selected predicate would merely relocate the loophole.

For the present development, each downstream datatype should therefore have a
small law group whose fields are its complete constructor equations. For
example, Lax-53 may define:

```lean
structure TreePresentationLaws (P : Presentation (Tree A)) : Prop where
  node : ...
```

Lax-58 supplies the fixed vocabulary and generic theorems used on the
right-hand sides. Lax-53 supplies the equations specific to ranked trees and
its intrinsic Lax-52 formulas.

The current `structural%` and `structuralFun%` elaborators generate the
constructor fold, including dependent finite families. The owning submission
still states a first-class law group containing the equations a human would
write and proves it by reduction. The kernel checks those equations, so the
automation introduces no additional mathematical trust.

## 5. Keep the structural vocabulary small

Provide only the fixed combinators needed by current consumers. The initial
set should be determined against Lax-53 and will likely include:

- natural-number primitive fields;
- constructor choice and product-like field composition;
- ordered lists;
- finite indices and ordered finite families, because a ranked-tree node has
  children of type `Fin (rank a) → Tree A`.

Finite-family combinators certify provenance only. Since an arbitrary Lean
function may be expensive to evaluate, the cost of enumerating a finite
function remains a separate computation/refinement theorem.

Concrete `Raw.nat` tags and `Raw.pair` nesting are implemented inside these
combinators. `Raw.constructor` takes a symbolic string name and ordered fields;
its injectivity law lets downstream certificates describe constructor
structure without numerical tags or parser details. The string is only a
human-readable constructor identifier: Lax-58 realizes it injectively as one
internal natural payload, so it cannot carry value-dependent advice.

Combinators such as multisets, finite sets, integers, subtypes, and optional
values should be retained only when an immediate archive consumer needs them.

The exact certificate-facing vocabulary should be finalized by writing the
ranked-tree and raw-formula certificates first. This avoids designing an
unnecessarily broad generic datatype library.

## 6. Structural size and payload conditions

For a certified presentation `P`, define:

```text
|x|struct = (P.toRaw x).nodes
```

Constructor equations should yield corresponding size recurrences. A
downstream submission may then prove that this size equals or is linearly
related to its customary constructor count.

Keep payload fit explicit:

```lean
P.PayloadsFitInWord x w
```

meaning that every natural payload in `P.toRaw x` is less than `2^w`.
Structural size alone does not imply this condition.

## 7. Distinguished immutable word arena

Lax-58 should provide one explicit arena representation of `Raw`:

```lean
structure WordImage where
  memory : Array Nat
  root   : Nat

encodeRaw : Raw → WordImage
```

A simple postorder layout may use three words per raw node:

```text
natural leaf: [tag, payload, 0]
pair node:    [tag, leftAddress, rightAddress]
```

The numerical tags and allocation calculations are implementation details of
Lax-58. Downstream concepts should use the named arena construction and its
laws.

Expose a semantic relation:

```lean
WordImage.Represents address raw
```

and prove that the distinguished image represents its source. Also prove the
relevant address validity, block well-formedness, and density properties.
The explicit encoder determines every stored word and is the primary
no-annotation guarantee. Density separately proves that the distinguished
image contains no unreachable auxiliary blocks.

No canonical whole-memory decoder is required. Multiple physical memories may
represent the same raw value; complexity theorems use the distinguished dense
image unless they explicitly establish a stronger representation invariant.

## 8. Exact footprint and word-fit bridge

The distinguished arena should satisfy exact laws:

```text
memoryWords (encodeRaw raw) = 3 * raw.nodes
totalWords  (encodeRaw raw) = 3 * raw.nodes + 1
```

For a presented value `x`, this gives:

```text
memoryWords (encode P x) = 3 * P.structuralSize x
```

Keep the following conditions conceptually separate:

- primitive payloads fit in `w` bits;
- the memory address space fits in `w` bits;
- every stored word, including pointers and the root, fits in `w` bits.

The public bridge theorem should show that payload fit together with

```text
3 * P.structuralSize x ≤ 2^w
```

implies that the distinguished image fits in `w`-bit word memory.

## 9. Remove generic binary serialization

Lax-58 should not contain the generic binary-codec layer under this revised
scope. Remove the public dependency on:

- bit strings, prefix parsers, and bit-length functions;
- canonical binary codecs and primitive codecs;
- codec combinators;
- codec-based `ComputableMap`;
- structural-to-binary serialization modules.

Binary serialization solves persistence and interchange problems. It is not
needed for the neutral RAM input model and enlarges the human review surface.

The repository name may remain unchanged for continuity, but the mathematical
scope of Lax-58 becomes structural representation and word-memory realization.

## 10. Consequences for Lax-53

Lax-53 should remove its existential binary `Serialization` package while
keeping mathematical formula/automaton translations at the mathematical
level.

Conceptually:

```text
Formula → Automaton
language preservation
```

Separate downstream computation theorems may then show that these mathematical
functions are effectively realized on distinguished structural inputs. The
arena should support the mathematics rather than becoming part of every
mathematical definition.

The reusable predicate may be defined temporarily in Lax-53 or later moved to
a dedicated computation/refinement submission. It should not pull a general
execution model into Lax-58.

Lax-53 may retain specialized word layouts such as a transition table or a
one-word-per-tree-node postorder layout. These are RAM data structures, not
generic binary serialization. Their use must be connected to the structural
baseline:

- preprocessing depending only on a parameter fixed outside the measured
  execution needs effective constructibility;
- preprocessing depending on runtime input must be included in the time bound;
- a conversion charged to the main algorithm needs an explicit time bound;
- alternatively, the RAM program may consume the generic arena directly.

## 11. Provenance and construction time are distinct

Constructor equations guarantee what information occurs in the
representation. They do not guarantee how quickly a particular Lean
implementation computes that output: an extensionally correct implementation
could perform irrelevant work before returning it.

Lax-58 is responsible for:

- structural provenance;
- faithfulness;
- structural and payload measures;
- faithful linear-space arena realization.

A later computation/refinement framework is responsible for:

- construction time;
- conversion time to specialized representations;
- RAM instruction semantics;
- algorithmic asymptotic bounds.

## 12. Concept organization

Concepts should be grouped by one coherent human mathematical idea. Lax allows
multiple statements in one concept, so related laws should remain together.

A practical organization is:

```text
StructuralPresentation       definitions of Raw and Presentation
StructuralCombinators        fixed vocabulary and its related laws
WordArena                    memory definitions, encoder, and related laws

CertifiedDerivation          small field-agreement API (infrastructure)
CertifiedDerivationElab      closed command and registry (elaboration infrastructure)
StructuralDerivation         unrestricted folds (elaboration infrastructure)
```

The first three pages are mathematical concepts. The remaining three are
explicitly labeled infrastructure: agreement bookkeeping is not a standalone
definition of advice-freedom, and the generator is not a mathematical object.
Lax currently classifies every non-root concept-package module as a concept,
so the tooling remains visible and auditable under that packaging constraint.
No hidden helper directory or proof-package import is used to bypass it.

The closed command still creates the encoder, complete constructor laws, and
checked witness together. Its resolver never consumes arbitrary agreement
values or unrestricted field encoders. Generated downstream laws are the
human-reviewable semantic specification; the kernel checks their proofs.

## 13. Non-goals

Lax-58 should not introduce:

- a closed universe of all Lean datatype descriptions;
- treating automatic derivation or `FieldEncoding` membership by itself as a
  no-advice certificate;
- mutable heaps or allocation semantics;
- separation logic;
- RAM instruction semantics;
- general ADT cost models;
- runtime or Big-O proofs for downstream algorithms.

These would obscure the central claim and belong in later infrastructure.

## 14. Proposed implementation order

1. Generate complete constructor certificates for Lax-53 ranked trees and
   intrinsic formulas, recursively resolving only approved fields.
2. Reduce and adjust the Lax-58 combinator vocabulary to express those
   equations without low-level tags.
3. Remove binary serialization concepts and their proof obligations from
   Lax-58.
4. Complete the structural combinator and distinguished-arena proofs.
5. Keep Lax-53's mathematical translations at value level and add separate
   effective-realization claims where needed.
6. Connect Lax-53's specialized RAM layouts to the certified structural
   baseline with the appropriate computability or time-bound theorems.
7. Run full Lax validation and kernel replay for both submissions.

## Summary

The proposed Lax-58 guarantee is:

> A certified representation contains exactly the source datatype's
> constructor structure and certified primitive fields, introduces no derived
> advice, and has a faithful distinguished word-memory realization whose space
> is exactly linear in structural size.

This guarantee comes from complete kernel-checked constructor equations, not
from an unrestricted presentation function having a suggestive name or
typeclass instance.
