# Session history

Historical checkpoints, preserved from the former `FORMALIZATION_STATE.md`.
Read `CURRENT_STATE.md` for authoritative current status; later audit entries
can supersede earlier claims in this history.

## Submission

- Lax id: `lax-58`
- Lean namespace: `Lax58`
- Proof namespace: `Lax58Proofs`
- Title: `Certified structural representations of finite data`
- Authors: Szymon Toruńczyk and Codex 5.6
- Current phase: closed certified derivation implemented locally;
  cross-repository integration validation in progress

## Current architecture (2026-09-04)

Lax-58 now has five concept modules:

- `StructuralPresentation`: the universal `Raw` type of natural leaves and
  binary pairs, structural node count, maximum payload, `Presentation`,
  round-trip lawfulness, faithfulness, structural size, and payload fit;
- `StructuralCombinators`: the minimal fixed structural vocabulary actually
  used by Lax-53 (symbolically named constructors, `Nat`, products, and
  ordered lists), with constructor injectivity, grouped round-trip laws, and
  exact size laws;
- `StructuralDerivation`: an elaborator that derives constructor folds for
  inductive and dependent inductive values while leaving non-recursive field
  encodings explicit; its `FieldEncoding` class is elaboration input and is
  deliberately not a no-advice certificate;
- `CertifiedDerivation`: a closed command generating an encoder, `.Laws`, and
  `.certified` together. Its field resolver admits only Nat, Fin, proof-erased
  subtypes, finite families, and earlier successful constructor derivations
  recorded in a private registry. `CertifiedFieldEncoding` is indexed by the
  canonical encoder and law and requires equality of its stored encoder to
  that canonical function. Arbitrary field instances are
  ignored, unsupported fields fail, and failed commands roll back their
  declarations. The temporary `structuralLaw%` shortcut was removed;
- `WordArena`: one distinguished dense immutable postorder arena for `Raw`,
  with semantic representation, block validity, exact `3 * nodes` memory
  footprint, exact `3 * nodes + 1` total and distinguished-input footprints,
  `WordImage.toInput = root :: memory.toList`, and a payload/address word-fit
  bridge.

The generic binary serialization layer and `Presentation.Canonical` have been
removed. The explicit arena encoder, rather than density alone, determines
every stored word and rules out hidden annotations. Density independently
rules out unreachable auxiliary blocks. Finite-function presentations certify
content provenance only; no cheap-enumeration claim is made.

Datatype-specific constructor certificates are generated in the downstream
namespace. Lax-53 uses four compact invocations for terms, relations, intrinsic
formulas, and ranked trees. Their fields bottom out transitively in Nat/Fin.
The elaborator establishes correspondence with the datatype declaration;
Lean checks the expanded constructor laws and their reduction witnesses.

## Proof and validation status

- The proof package has been adapted to the minimal combinator vocabulary and
  proves all fifteen public combinator and arena axioms.
- A direct `lake build` of the Lax-58 proof root passes after moving ordinary
  helper theorems out of concept files.
- `lax build . --replay --no-color` on 2026-09-04 passes layout checks,
  dependency resolution, concept and proof compilation, independent kernel
  replay, and statement inspection for all five concepts and fifteen proofs.
- `lake env lean ../tests/CertifiedDerivation.lean` passes from `concepts/`.
  The regression suite verifies primitives, transitive datatype fields,
  dependent finite families, immunity to actual low-level instance overrides,
  rejection of unsupported/hidden fields, atomic rollback, and rejection of
  both direct witness construction and record updates.
- Lax-53's companion regression suite passes concrete encoding equations and
  verifies that all four generated witnesses depend only on the permitted
  background axioms. Its structural representation proof module also builds.

### 2026-09-05 certificate audit correction

- Found that Lean's `constructor` tactic can access a private structure
  constructor. Thus the previous unindexed record could be fabricated with
  an arbitrary encoder and `True` as its law, without new axioms. The closed
  registry never consumed such a record, but claiming the record itself was
  sealed was too strong.
- Moved the canonical function and law into type indices and added an
  `agrees : toRaw = canonical` obligation. Tactics cannot change those indices
  while inhabiting a genuine generated certificate type. Provenance still
  comes from the closed generator/registry, not arbitrary record membership.
- Added a regression for the constructor-tactic attack and a general proof
  that any certificate for `Raw.nat` cannot output `Raw.nat 42` on input `7`.
  The complete generic suite passes after this strengthening.
- Interrupted the previous downstream rebuild at 3075/3109 jobs to avoid
  validating the superseded record. Restarted the final full proof build with
  `LEAN_NUM_THREADS=2`; final replay/integration results are recorded below.
- The current organization deliberately uses multiple related statements in
  each coherent concept, as confirmed by the Lax authors.
- No `lax register` or publication action has been run.

## Preservation and dependency notes

- Preserve the untracked user artifact `Archive.zip`; it is not submission
  content.
- Lax-53 consumes this checkout through generated local Lake package
  overrides. The installed Lax CLI still insists on an Archive content record
  before honoring that local build setup, so a full Lax-53 `lax build` remains
  blocked until the CLI behavior catches up or Lax-58 is submitted. Direct
  `lake build` works locally and does not require publication.
- Registration remains strictly user-only.

## 2026-09-05 workflow and current-state handoff

- Moved this historical log out of `FORMALIZATION_STATE.md`; that filename is
  now a compatibility pointer. `CURRENT_STATE.md` is the concise authoritative
  status and `WORKFLOW.md` defines the narrow package boundary and check tiers.
- Added local agent instructions and `scripts/check-certified.sh`. The script
  passes on the strengthened API (focused concept build and regression suite).
- Final Lax-58 replay of the strengthened API passed on 2026-09-05: five
  concepts and fifteen proofs, including independent kernel replay.
- Added downstream report tooling, compiler-operation completion criteria,
  and milestone tracking without changing compiler semantics or archive pins.

## Exact next action at the preceding encoding checkpoint

Finish the coordinated Lax-53 audit repairs and its full proof build. Commit
or publication requires a separate user request; never run `lax register`
autonomously.

## 2026-09-05 mathematical surface / elaboration tooling split

- Reduced `CertifiedDerivation.lean` from 255 to 82 lines: agreement data and
  primitive/subtype/family operations only, with no explicit Lean import or
  elaborator definitions. Its title/type explicitly identify infrastructure,
  not a mathematical definition of advice-freedom.
- Moved constructor inspection, the private registry, generated syntax, and
  rollback into `CertifiedDerivationElab.lean`, labeled elaboration
  infrastructure. Apart from namespace and proof packaging, its resolver and
  command body are byte-for-byte unchanged. Relabeled unrestricted
  `StructuralDerivation` as elaboration infrastructure too.
- Added the checked `ofLaws` packaging function so the tooling module need
  not access a private constructor across modules. It fixes the output to
  the specified encoder and requires the law proof; it never registers a
  datatype. A negative test checks that a packaged arbitrary agreement still
  cannot make an unregistered datatype an admissible field.
- Added an agreement-only import test. Generic derivation regressions and
  downstream focused proofs/equations/axiom audits pass. Lax-58 full build
  and independent replay pass six modules and fifteen proofs in 1m24s.
- Updated the abstract, proposal, workflow, and current-state documents.
  The running Lax-58 preview rebuilt with explicit infrastructure labels.
  No archive tooling category, dependency pin, or publication was changed.

## 2026-09-05 downstream headline completion check

- Reran `scripts/check-certified.sh` and the downstream Lax-53 certification
  suite together; session `7534` passed (437, 900, and 904 build jobs).
- Lax-53 now has both unchanged headline MSO runtime proofs, with a full local
  proof-root build, type-equality and background-only axiom guards, and
  independent replay of its twelve latest modules. Detailed evidence is in
  `../MSO-automata-trees/CURRENT_STATE.md`.
- No Lax-58 concept, implementation, or dependency pin changed. Updated only
  this history and the current-state validation note. Downstream Archive
  resolution remains a separate authorization gate.

## 2026-09-05 short guide and paused submission

- Updated the author list as requested to Jan Dreier, Szymon Toruńczyk,
  and ChatGPT (5.6 and 6). The user then paused submission to review locally;
  no commit or submission was made.
- The local preview rebuild completed full validation and kernel replay:
  session `86625`, 39s, six concepts and fifteen proofs.
- Added `README.md`, a short explanation of Lax58's purpose, closed derivation,
  generated laws/certificates, immutable arena, usage, and guarantee limits.
- Extracted the README's Lean block directly into `lake env lean --stdin`;
  session `63266` passed and printed the generated definitions. Whitespace
  validation also passed. Linked the guide from `CURRENT_STATE.md`.

## 2026-09-05 generalize the guide's examples

- Reframed the README around finite mathematical data: formulas and terms,
  relational structures such as graphs, trees, and finite automata.
- Removed the automata-specific motivation and clarified that examples need
  explicit representations using supported finite datatypes and fields.
- Prose-only change; the previously checked Lean example is unchanged.
  Submission remains paused.

## 2026-09-05 illustrative concept inside the submission

- Added `concepts/Lax58/FormulaExample.lean` and its concept-root import.
  The file defines propositional syntax, derives its structural encoding,
  and presents `p₀ ∧ ¬p₁`, its raw structure, and its exact word-arena input.
- No new concept axioms or manual proof-package declarations were needed.
  The existing command generates the complete laws and checked certificate.
- Added `tests/FormulaExample.lean` to the certification suite, checking the
  exact constructor expansion and generated certificate. The suite passes
  (session `90504`, 439 build jobs); the certificate has only background axioms.
- Full `lax build . --replay --no-color` passes (session `51014`, 30s):
  seven concepts, fifteen proofs. The existing local preview regenerated and
  lists `Lax58.FormulaExample`. Whitespace checks pass.
- Linked the example from the README and refreshed current state. Submission
  remains paused, with the new concept ready for user review.

## 2026-09-05 public Git preparation

- User authorized committing Lax58 and making the Git source public; Lax
  submission and registration remain paused.
- Verified GitHub authentication for `szymtor`. No Git remote is configured,
  so requested the public destination before creating a repository or pushing.
- Prepared the validated implementation, example, guide, author metadata,
  tests, and workflow notes for a scoped commit. Excluded the unrelated
  `Archive.zip` and generated build artifacts; source credential-pattern and
  whitespace checks found no issues.
