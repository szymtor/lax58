# Formalization state

Read this file first when resuming work. Update it at the end of every session.

## Submission

- Lax id: `lax-58`
- Lean namespace: `Lax58`
- Proof namespace: `Lax58Proofs`
- Title: `Canonical encodings of finite data`
- Current phase: public concepts compile; Lax validation and user review remain

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
- Added four concept modules: canonical prefix codecs, primitive codecs,
  compositional codecs, and canonical finite-set codecs.
- The standard bit encoding of a natural `n` has exact length
  `2 * n.bits.length + 1`.
- `lake build` passes for all concept modules without warnings.
- No proof work has begun; after Lax concept validation, present the concepts
  to the user and wait for approval.
