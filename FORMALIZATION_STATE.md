# Formalization state

Read this file first when resuming work. Update it at the end of every session.

## Submission

- Lax id: `lax-58`
- Lean namespace: `Lax58`
- Proof namespace: `Lax58Proofs`
- Title: `Structural encodings of finite data`
- Authors: Szymon Toruńczyk and Codex 5.6
- Current phase: implementation, proofs, replay validation, and preview
  verification complete

## Implemented result

The submission provides a reusable encoding layer for finite data:

- prefix codecs over bit strings, with separate lawfulness, canonicality, and
  effectiveness properties;
- exact structural bit-size functions;
- canonical primitive codecs for `Unit`, `Bool`, `Nat`, and `Int`;
- codec constructors for equivalences, products, sums, options, lists,
  fixed-length vectors, functions on `Fin n`, and finite indices;
- sorted canonical encoders with permutation-insensitive decoders for
  multisets and repetition-insensitive decoders for finite sets;
- a universal recursive representation by binary trees with natural leaves,
  together with presentations for arrays, subtypes, collections, and the
  standard finitary constructors;
- a generic `Primcodable` codec as a qualitative fallback; and
- computable realization of ordinary computable maps on distinguished bit
  encodings.

The proof package establishes all eight public proof obligations. In
particular, effectiveness of the list parser is proved through a terminating
partial-recursive fixed point rather than assumed.

## Validation checkpoint (2026-09-01)

- `lake build` succeeds for the complete proof package.
- `lax build . --no-color` succeeds with `11 concepts · 8 proofs`.
- `lax build . --replay --no-color` succeeds, including kernel replay and
  axiom-hygiene inspection.
- Every public statement currently has a proof annotation in
  `Lax58Proofs`.
- The refreshed live preview at `http://localhost:8124/lax-58/index.html`
  displays all eight statements as proven and no longer reports a stale local
  archive database. Port 8123 was occupied when the final preview server was
  started, so Lax selected port 8124.

Registration remains a user-only action.
