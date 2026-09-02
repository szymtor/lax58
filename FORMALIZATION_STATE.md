# Formalization state

Read this file first when resuming work. Update it at the end of every session.

## Submission

- Lax id: `lax-58`
- Lean namespace: `Lax58`
- Proof namespace: `Lax58Proofs`
- Title: `Certified structural representations of finite data`
- Authors: Szymon Toruńczyk and Codex 5.6
- Current phase: revised concepts and proofs complete locally; fresh full Lax
  build passes; awaiting user review

## Current architecture (2026-09-02)

Lax-58 now has exactly three concept modules:

- `StructuralPresentation`: the universal `Raw` type of natural leaves and
  binary pairs, structural node count, maximum payload, `Presentation`,
  round-trip lawfulness, faithfulness, structural size, and payload fit;
- `StructuralCombinators`: the small fixed structural vocabulary needed by
  Lax-53 (`Unit`, `Bool`, `Nat`, products, sums, lists, finite indices,
  vectors, and ordered finite families), with grouped round-trip and exact
  size laws;
- `WordArena`: one distinguished dense immutable postorder arena for `Raw`,
  with semantic representation, block validity, exact `3 * nodes` memory
  footprint, exact `3 * nodes + 1` total footprint, and a payload/address
  word-fit bridge.

The generic binary serialization layer and `Presentation.Canonical` have been
removed. The explicit arena encoder, rather than density alone, determines
every stored word and rules out hidden annotations. Density independently
rules out unreachable auxiliary blocks. Finite-function presentations certify
content provenance only; no cheap-enumeration claim is made.

Datatype-specific constructor certificates belong to downstream submissions.
Lax-53 now provides such certificates for automaton data, raw formulas, and
ranked trees. The tree certificate uses a fixed constructor tag, exposes the
symbol number as a `Nat` field, and recursively exposes the ordered children.

## Proof and validation status

- `proofs/Lax58Proofs/StructuralCombinators.lean` proves all structural
  combinator laws.
- `proofs/Lax58Proofs/WordArena.lean` proves representation, well-formedness,
  density, exact footprints, and word fit for the distinguished arena.
- A fresh `lax build . --no-color` passes layout, dependency resolution,
  concept compilation, proof compilation, and statement inspection
  (`3 concepts · 12 proofs`).
- The current organization deliberately uses multiple related statements in
  each coherent concept, as confirmed by the Lax authors.
- No `lax register` or publication action has been run.

## Preservation and dependency notes

- Preserve the untracked user artifacts `Archive.zip` and
  `lax58_inmemory_patch/`; neither is submission content.
- Lax-53 consumes this checkout through generated local Lake package
  overrides. The installed Lax CLI still insists on an Archive content record
  before honoring that local build setup, so a full Lax-53 `lax build` remains
  blocked until the CLI behavior catches up or Lax-58 is submitted. Direct
  `lake build` works locally and does not require publication.
- Registration remains strictly user-only.

## Exact next action

Review the combined Lax-58/Lax-53 revision. Do not add serialization back to
Lax-58 unless a distinct persistence/interchange use case is proposed.
