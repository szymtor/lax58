# Session history

Historical checkpoints, preserved from the former `FORMALIZATION_STATE.md`.
Read `CURRENT_STATE.md` for authoritative current status; later audit entries
can supersede earlier claims in this history.

## Submission

- Lax id: `lax-560851`
- Lean namespace: `Lax560851`
- Proof namespace: `Lax560851Proofs`
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
- Added `README.md`, a short explanation of Lax560851's purpose, closed derivation,
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

- Added `concepts/Lax560851/FormulaExample.lean` and its concept-root import.
  The file defines propositional syntax, derives its structural encoding,
  and presents `p₀ ∧ ¬p₁`, its raw structure, and its exact word-arena input.
- No new concept axioms or manual proof-package declarations were needed.
  The existing command generates the complete laws and checked certificate.
- Added `tests/FormulaExample.lean` to the certification suite, checking the
  exact constructor expansion and generated certificate. The suite passes
  (session `90504`, 439 build jobs); the certificate has only background axioms.
- Full `lax build . --replay --no-color` passes (session `51014`, 30s):
  seven concepts, fifteen proofs. The existing local preview regenerated and
  lists `Lax560851.FormulaExample`. Whitespace checks pass.
- Linked the example from the README and refreshed current state. Submission
  remains paused, with the new concept ready for user review.

## 2026-09-05 public Git preparation

- User authorized committing Lax560851 and making the Git source public; Lax
  submission and registration remain paused.
- Verified GitHub authentication for `szymtor`. No Git remote is configured,
  so requested the public destination before creating a repository or pushing.
- Prepared the validated implementation, example, guide, author metadata,
  tests, and workflow notes for a scoped commit. Excluded the unrelated
  `Archive.zip` and generated build artifacts; source credential-pattern and
  whitespace checks found no issues.

## 2026-09-05 public Git publication

- Committed the validated source as `9439690`.
- After explicit confirmation, created the public repository
  https://github.com/szymtor/lax58 and pushed `main`; `origin/main` tracking
  is configured. The create-and-push command completed successfully.
- `Archive.zip` remains local and untracked. Lax submission and registration
  remain paused; no Lax publication command was run.

## 2026-09-05 successful Lax draft submission

- User authorized submitting Lax560851. The first command added the required
  issue binding to `manifest.yaml`; committed and pushed it as `53278a4`.
- Retried `lax submit . --allow-dirty --no-color`, excluding only the local
  untracked `Archive.zip`. Session `89909` completed successfully: local build
  33s, Archive rebuild 2m05s, public-record publication 36s.
- Workflow `33964638553` published commit
  `53278a48b0605bde8cfc9510066ee797d085a6f1` as the Lax560851 draft at
  https://laxarchive.org/lax-560851/. Archive commit:
  `ebdab5038116a53393dc56dbfde44ba2f3c6e82c`.
- Drafted the requested message to Jan in the conversation; did not send it.
  No registration was performed. Lax842588 submission is now separately requested.

## 2026-09-06 explicit RAM resource bounds and closed encoding selection

- Implemented the user-approved `RamComputableWithin f timeBound wordBound`
  frontend and its encoding-explicit `RamComputableWithinUsing` definition.
  Word capacity remains explicit; the earlier hidden parameter/coefficient
  proposal was not implemented. The two example properties quantify their
  coefficients directly. Both bounds are functions of the whole typed input.
- Added `RamComplexity`, `RamComplexityElab`, and `RamComplexityExample` to
  the concept root. The elaborator is a read-only client of the original
  closed field resolver/registry. Fixed list/product composition uses the
  exact existing presentations; subtype and finite-family composition keeps
  proofs erased and intrinsic order. No arbitrary presentation instances or
  hand-built agreement records are consumed. Nat/Bool outputs use one word;
  other supported outputs use arenas.
- Added `inputMagnitude` through the same input resolver and updated README,
  abstract, and workflow to describe the new layer over Lax865980. Added the
  Lax865980 pin already used by Lax842588, without changing other dependency pins.
- Regression-driven fixes preserve exact list/product encoding expansions
  and postpone selection until binder-local type constraints are resolved.
  Indexed-encoder tests use the existing command's supported implicit-index
  syntax. The choice-based decoder wrapper is not claimed executable.
- `bash scripts/check-certified.sh` passes in session `67976` (814 build
  jobs): previous certification suites plus expanded proposition/quantifier
  checks, primitive/structured outputs, imported and indexed registrations,
  dependent families, subtypes, ignored malicious field instances, rejected
  unregistered input/output types, dependent result rejection, malformed
  bounds, and background-axiom audit.
- Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passes in
  session `63434` (1m19s): 10 concepts, 15 proofs, independent kernel replay.
  The only warning is Lax865980's supersession by Lax67. Earlier validation runs
  exposed missing network access for dependency provisioning; the approved
  retry fetched the pinned dependency. Final whitespace checks pass.
- Discussed why input length alone is not a universal word-capacity bound:
  input payload fit is separate, and intermediate values/addresses may exceed
  input length. No semantic change was inferred from that question.
- Changes remain local and uncommitted. No Lax842588 files, existing structural
  encoders, publication state, registration, or unrelated `Archive.zip` were
  changed. The generated local preview data now includes the new concepts.

## 2026-09-06 descriptive coefficients, polynomial examples, and Lax759944 comparison

- Renamed `g`/`h` to `timeCoefficient`/`wordCoefficient`, documenting how both
  depend only on the second input's length. Also named `timeByLength` and the
  constant `wordCoefficient` in the one-input example; synchronized README.
- Added `PolynomialTimeOfDegree f d`, with time at most a constant times
  `(n + 1)^d`, and `PolynomialTime f := ∃ d, PolynomialTimeOfDegree f d`.
  Both reuse the existing `TimeBounded` word-capacity convention. Degree zero
  is allowed and the degree is an upper bound, not an optimality claim.
- Full build and independent replay passed in session `46904` (1m41s,
  10 concepts, 15 proofs). Updated regression file passed in session `98595`;
  the earlier suite `76784` found only an overestimated expected axiom set in
  the new audit, corrected from `[propext, Quot.sound]` to `[propext]`.
  Added exact-expansion, existential-degree, and zero-degree checks.
- User asked whether this coincides with `Lax759944.RamPolytime`, and requested a
  proof if so. Read that definition and `BinaryWordEncoding`/`TuringPolytime`.
  It does not coincide: Lax759944 measures time and polynomial sufficient word
  bit width in binary input size. The local example measures time in list
  length and bounds sufficient capacity linearly in input magnitude. Its
  input arena also differs from Lax759944's length-prefixed native list.
- Explained the separating output `2 ^ xs.length` (wrapped as a singleton
  for Lax759944): on zero lists its bit length is linear, but its numerical value
  cannot fit at every linear-capacity width required by the local example.
  No equivalence proof was asserted, no additional dependency was introduced,
  and neither definition was changed in response to the comparison question.
- User requested preview refresh; the successful full build regenerated local
  preview data with the new names and polynomial definitions. All changes
  remain local and uncommitted; no publication or registration was performed.

## 2026-09-06 explanatory comparison PDF

- At the user's request, rewrote the Lax759944/Lax560851 comparison as a two-page PDF
  and editable LaTeX in `docs/ram-polynomial-time-comparison.{pdf,tex}`.
- The comparison table defines input magnitude as structural node count plus
  maximum payload plus one, and specializes it to `2n + m + 2` for lists.
  Included the reason for using `m` rather than `log m`, quantifier/width
  distinctions, and the `2 ^ length` separating example with numeric values.
- Compiled with pdflatex, corrected a reserved macro-name conflict and a line
  overflow, and visually inspected both rendered pages. Final compilation has
  no overfull/underfull boxes or warnings. Build intermediates remain in the
  task-specific temporary directory, outside the source tree.
- No Lean definitions, proofs, package pins, manifest, or publication state
  changed. The note explicitly distinguishes its mathematical explanation from
  a kernel-checked separation theorem.

## 2026-09-06 PDF notation layout

- Replaced the second paragraph's inline notation definitions with four aligned
  display lines for `n`, `m`, `B`, and `M = inputMagnitude(x)` as requested.
- Regenerated the same PDF; it remains two pages. Inspected the updated first
  page and checked the final LaTeX log: no warnings or overfull/underfull boxes.
- No mathematical definitions or Lean files changed.

## 2026-09-06 requested arena bit-polynomial equivalence: model conflict

- User requested an additional notion aligned with Lax759944, an equivalence
  theorem, explanatory comments, and formal positive/negative results for the
  separating example. User explicitly chose to keep certified arena input.
- Inspected Lax759944's clean local source and archive record (both at
  `4f6c21aae81fbe8d1233d3ae8358b82b110549b9`), both lakefiles, RAM definitions,
  existing TM/RAM input adapters, and proof code. Lax759944 pins the older
  accumulator RAM at `d35ba57ad420ce6a6d3c763aa7f6a4a8be1d406d`, whereas
  Lax560851 uses the cell-to-cell RAM at `92ae2d6275d09b856c02d6f851755590fdcb30ed`.
  A source diff confirms different instruction types, state, and semantics
  under the same `Lax865980.Ram` module name; old proofs explicitly require `Op`
  and `State.acc`. This is additional to arena/native conversion obligations.
- No existing ready compatibility theorem was found in active Lax759944/Lax842588/
  Lax560851 sources. Did not silently repin either package, reinterpret Lax759944,
  add an unproved equivalence axiom, or claim the requested proofs complete.
- Paused for authority to resolve the older Lax759944 dependency/model before
  implementing the cross-package equivalence. Existing validated files and
  the explanatory PDF remain intact; Lax759944 worktree is unchanged.

## 2026-09-06 bit-polynomial definition and formal separation

- Reattached to Lax759944's already-authorized submission. The archive confirmed
  successful publication of `6fe5a3d94f6c2da46cc2c5ab98cd36997b130737`;
  synced and pinned its concept package in Lax560851. The old model conflict is
  resolved, without local source overrides or changed Lax759944 statements.
- Added the arena-based bit-polynomial definition and comparison concept.
  The general equivalence is explicitly open; both exponential-example
  statements have independent proofs that do not assume it.
- Proved a generic RAM output-fit invariant, the negative result for every
  time allowance under linear capacity, and a six-instruction positive
  arena algorithm at sufficient width `bitSize xs + 4`.
- Proved the generic capacity/bit-width reformulation. Full Lake proof root
  and first regression/axiom audit passed; independent replay and guarded
  regression rerun are the next validation steps.
- Equivalence still needs actual tape adapters and composition safe against
  arbitrary programs using scratch memory. No Lax560851 commit or publication yet.
- Guarded full regression suite passed (`63986`). Independent kernel replay
  and statement inspection passed (`21080`, then `8159` after adding checked
  even/odd virtual-memory lemmas): 12 concepts, 17 proofs. The open equivalence
  remains deliberately unproved and is not used by either example proof.
- Updated README and regenerated the two-page explanatory PDF with current
  proof status; final LaTeX log is clean. Recorded the remaining streaming
  adapter/compiler design in `RAM_EQUIVALENCE_PLAN.md`.

## 2026-09-06 completed RAM equivalence and publication

- Implemented both safe tape compilers over interleaved virtual/scratch RAM
  memory and proved arbitrary-run, halt, exact-output, and resource transfer.
  The native-to-arena bound is `18*t+26`; arena-to-native is
  `66*t+6*n+81`, with constant word-width slack.
- Proved `bitPolynomialTime_iff_ramPolytime`. The class-level witnesses use
  `18*T+26` and `66*T+6*X+81`; degrees are not required to match, and the
  second translation can raise a constant time bound to linear.
- Aggregate Lean build, guarded regression suite, independent kernel replay,
  and statement inspection passed. The preview contains 12 concepts and 18
  proofs and reports no outstanding assumptions for the equivalence.
- Published commit `86319376d4ce21dfdfa796713e06f18c575de972` to
  `szymtor/lax58` and submitted it as the current Lax-58 draft through archive
  workflow `34054472817`. The public page was checked against that commit.

## Lean 4.33 migration, 2026-09-15

Prepared independent lax-560851 from original lax-58 published sources.
Full build, certification regression suite, and independent replay passed.
12 concepts, 18 annotated proofs, no extra assumptions. Four proof-line
compatibility edits; concepts unchanged apart from namespaces. Publication next.

Publication confirmed at https://laxarchive.org/lax-560851/, issue 114,
commit 091d4fe67804863dac4001f7bc1ac72d8597a7e4.

## 2026-09-15 dedicated-input/output RAM rebase

- Rebased the public resource predicate and comparison endpoints onto the
  complete Lax808846 model at exact archive commit
  `9394e531cc51cb67a0214bca3f9264dfe97ba5c7`. Dedicated immutable input supports
  indexed access, sequential reads, length, and EOF; fetched terminal
  instructions are charged. The arena layout and explicit native length prefix
  are unchanged encodings.
- Migrated output-fit and separation directly. The positive exponential example
  now counts its halt, giving seven executed instructions.
- Retained the former sequential arena/native compiler comparison under
  `Lax560851Proofs.Legacy` as a checked internal lemma. Its predicates contain
  definitions only, and it imports RAM/TM's vendored legacy machine rather than
  the deleted archive dependency.
- Proved class transfer through the full-instruction buffered compiler,
  projected its generated instruction subset into the old semantics, and
  restored the original annotated public equivalence without a compiler
  assumption. The public theorem uses Lax808846 in both endpoints.
- Composed bounds are `1188*T + 2382*X + 3382`, `Q + 14` from arena to native,
  and `324*T + 108*X + 603`, `Q + 14` in the other direction. Both may add a
  linear startup term; polynomial degrees need not match.
- Preserved the existing presentation helper API. The proof root now imports
  all 20 modules exactly once and retains 18 annotated conclusions. Updated
  the regression script to build the public comparison and run concrete
  lowering/class transfer audits; optional `LAKE_PACKAGES` makes development
  dependency overrides explicit.
- The concrete annotated frontend and its background-axiom guard pass Lean
  4.33 with `autoImplicit=false`. The only axiom dependencies are `propext`,
  `Classical.choice`, and `Quot.sound`. A transfer audit's expected message
  wrapping was corrected; its mathematical axiom list was unchanged.
- Updated WORKFLOW, README, current status, and the explanatory note. The
  coordinating agent regenerated the PDF and visually inspected both pages.
  The normal full proof-root build passed (1316 jobs), and the full certification
  script passed all eight regression files using explicit local overrides.
  Logs are `../migration-tools/canonical-808846-proof-build.log` and
  `../migration-tools/canonical-808846-certified.log`. Archive replay and
  publication await the rebased dependency pins.
  No commit, publication, or registration was performed by this frontend task.

## 2026-09-16 rebased RAM/TM release pins

- Pinned canonical concepts' `Lax759944` and proofs' `Lax759944Proofs` to
  `7010243df12cdda03abc5f63ec8de2c0963d4052`, the rebased RAM/TM release commit.
  The direct Lax808846 pin remains
  `9394e531cc51cb67a0214bca3f9264dfe97ba5c7`.
- The coordinating agent confirmed RAM/TM's full independent Lax replay passed:
  seven concepts, four annotated proofs, and empty assumption lists. Its
  archive record update is still awaiting confirmation.
- Canonical validation has deliberately not been started against the new pins.
  Exact next action is to run canonical Lax validation with independent replay
  after the coordinating agent confirms the RAM/TM archive record contains the
  new commit. Previous local canonical build/regression evidence is unchanged.
- No commit, push, publication, registration, or PDF edit was performed in this
  release-pin preparation task.

## 2026-09-16 final canonical validation against the published RAM

- RAM/TM archive workflow
  [35061865356](https://github.com/lax-archive/lax/actions/runs/35061865356)
  completed successfully. Refreshed the local archive with `lax sync` (the
  installed CLI does not recognize the older `pull-db` spelling), then verified
  `lax-759944` records exactly commit
  `7010243df12cdda03abc5f63ec8de2c0963d4052` from `szymtor/RAM-TM`.
- Ran `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` on the canonical
  package. The initial sandboxed dependency clone hit a DNS restriction; the
  approved unrestricted retry completed successfully. No proof change was
  needed during validation.
- Final result: 12 concepts, 18 annotated proofs, and empty assumption lists
  for every proof, including the full-model arena/native equivalence.
  Total time was 7m08s: concepts 2m16s, proofs 2m36s, independent kernel replay
  2m08s, and inspection 7s. Evidence:
  `../migration-tools/canonical-808846-validation.log`.
- Both generated manifests were checked for the exact current RAM/TM and
  Lax808846 revisions. Neither generated package-overrides file contains any
  local archive-package override; the deleted RAM dependency is absent.
  All 39 recorded source/configuration hashes were unchanged, including the
  coordinating agent's final WordArena description corrections.
- The 45 warnings comprise 42 intentionally retained helper lemmas, one
  proof-package dependency, and two draft-package dependencies. There are no
  extra assumptions or mathematical errors.
- Updated current status to hand off the validated working tree for coordinated
  commit/publication and downstream repinning. No commit, push, publication,
  registration, or PDF edit was performed in this final-validation task.
# 2026-09-16 publication policy and final local scope

- Committed and pushed the validated implementation as
  `8ec635640f3fd05271fa5cb7b1d3ae9e59400d7b`.
- Archive workflow `35064198245` rejected its RAM/TM draft dependencies at
  the static gate. The current archive policy requires registered dependencies
  for publication, while local builds may warn about them.
- The user explicitly chose to keep the dependencies as drafts and finish
  local validation. No registration or further archive publication is
  authorized. The corrected sources and all local validation evidence are
  retained; the existing archive record remains unchanged.
- This status update changes no Lean source, dependency pin, or PDF. Tree
  development continues to pin the validated implementation commit above.
