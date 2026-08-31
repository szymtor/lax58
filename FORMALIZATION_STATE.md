# Formalization state

Read this file first when resuming work. Update it at the end of every session.

## Submission

- Lax id: `lax-58`
- Lean namespace: `Lax58`
- Proof namespace: `Lax58Proofs`
- Title: `Canonical encodings of finite data`
- Current phase: public concepts pass Lax validation and await user review;
  proof work must not begin before approval

## Intended result

Provide a reusable, canonical and effective encoding standard for finitary
data built from natural numbers, finite sums and products, lists, finite sets,
and finite functions. Encoders produce strings over a fixed finite alphabet;
decoders accept exactly canonical encodings; prefix parsing composes; and
encoding length is controlled by a structural bit-size measure.

The standard should support concise `Primcodable` presentations of ranked
alphabets, finite relational signatures, automata, tree automata, and syntax
trees without exposing application-specific token grammars.

## Workflow

1. Complete and validate concept files only.
2. Present the concepts to the user for semantic review.
3. Begin proofs only after approval.

Registration remains user-only.

## 2026-08-31 checkpoint

- Reserved `lax-58` and initialized a standalone Git repository.
- Added eight focused concept modules: the core codec definition, canonical
  decoding, computable maps, primitive codecs, raw combinators, lawfulness and
  effectiveness closure, and canonical finite-set codecs.
- The standard bit encoding of a natural `n` has exact length
  `2 * n.bits.length + 1`.
- Both `lake build` and `lax build . --only concepts --no-color` pass without
  warnings. A full build reports `8 concepts · 0 proofs`.
- The live preview was verified at `http://localhost:8123/lax-58/index.html`.
- No proof work has begun; present the concepts to the user and wait for
  approval.
