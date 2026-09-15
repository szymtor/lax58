# Lean 4.33 draft migration

Original draft: lax-58. New draft: lax-560851; branch lean-4.33.
Independent draft linked to the original, without supersedes.

Full proof build passed (1278 jobs). bash scripts/check-certified.sh passed,
including positive and negative encoding/elaborator tests, polynomial comparison,
virtual compiler checks, and background-only axiom audits.
Full Lax validation/replay passed in 3m06s (2m24s replay): 12 concepts and
18 annotated proofs; all assumption lists empty. Concept Lean sources remain
unchanged after namespace renaming. Four proof-line compatibility changes
make list-length simplification explicit and restore simpa matching transparency.
The 42 inherited unused helpers are intentionally retained for downstream use,
including the tree-automata draft. RAM/TM dependency is pinned to published
Lean 4.33 commit 13530db8ae9e82025c8874656ae54ccfcecba566.

Evidence: ../migration-tools/canonical-proof-build.log,
canonical-regression.log, canonical-validation.log.
Next: push and submit this validated independent draft, then update the
new tree-automata draft to the published commit. No registration performed.

## Historical record from the original (not validation of this port)

# Lax-58 current state

Updated: 2026-09-06. The completed RAM-complexity extension is public at
`8631937` on https://github.com/szymtor/lax58 (`main`) and in the Lax-58 draft
at https://laxarchive.org/lax-560851/. Registration has not been requested.

## Local RAM-complexity extension

- Added the mathematical concept `RamComplexity`: `RamComputableWithinUsing`
  states one program, all inputs, all sufficient widths, with explicit time
  and word-capacity bounds. There is no hidden parameter or coefficient.
- Added `RamComplexityElab`: `RamComputableWithin f timeBound wordBound`
  automatically selects approved encodings; `inputMagnitude x` uses the same
  input resolver. It reuses a new read-only `resolveCertifiedField` wrapper
  around the existing private resolver. No registry writes or arbitrary
  witness/instance fallback were added.
- Selection uses exact existing Nat/list/product presentations, proof-erased
  subtypes, finite families, and registered constructor encoders. Nat/Bool
  outputs are one word; other supported outputs use arenas. The choice-based
  presentation wrapper for registered encoders does not claim an executable
  decoder. Existing structural encoders and Lax842588 statements are unchanged.
- Added `RamComplexityExample` with `LinearInFirstInput`, `TimeBounded`,
  `PolynomialTimeOfDegree`, and `PolynomialTime`, and documented usage in
  README. These are properties, not algorithm claims. Coefficient names are
  now `timeCoefficient` and `wordCoefficient`, with their roles documented.
  Polynomial time is measured in list length and retains the constant-times-
  input-magnitude capacity convention; it is not Lax759944's bit-size notion.
- Added the Lax865980 concept dependency at
  `92ae2d6275d09b856c02d6f851755590fdcb30ed`, matching Lax842588's pin. This adds a
  resource-predicate layer over the existing model, not a new machine model.
- `bash scripts/check-certified.sh` passes (session `67976`, 814 build jobs),
  including existing suites and new exact-expansion, imported/indexed encoder,
  finite-family, subtype, malicious-override, unsupported-input/output, and
  background-axiom checks. Full `lax build . --replay --no-color` passes
  (session `63434`, 1m19s): 10 concepts, 15 proofs, independent kernel replay.
  The only warning is that Lax865980 is superseded by Lax67. The build refreshed
  `build-output.json`; no new axioms or proof obligations were introduced.
- The updated polynomial examples passed full build and independent replay
  in session `46904` (1m41s, 10 concepts, 15 proofs). The extended RAM test file
  passes in session `98595`, including the exact polynomial expansion, degree
  zero, existential degree, and background-axiom checks. The full suite run
  `76784` passed the old checks but initially rejected the new audit's expected
  axiom list; corrected it to the actual smaller set (`propext` only).
- Compared `RAM-TM-equivalence/concepts/Lax759944/RamPolytime.lean` read-only:
  Lax759944 uses binary input size and polynomial sufficient bit width, with
  length-prefixed native input. The example here uses list length and an
  arena, with a linear-in-magnitude capacity threshold. For the singleton
  output adapter, `f xs = 2 ^ xs.length` separates the conventions on zero
  lists: polynomial output bit length is allowed by Lax759944 but exceeds the
  logarithmic-in-length sufficient widths required here. This is a mathematical
  comparison initially had no formal separation proof. The extension below
  now proves separation independently and adds the migrated Lax759944 dependency;
  the original convention has not been silently changed.
- The user's input-length question does not change the implementation:
  payload fit is a separate premise, while the explicit word bound can account
  for intermediate values and addresses exceeding the input length.

## Arena-based bit-polynomial extension (completed locally)

The Lax759944 model conflict is resolved: its migration to the current Lax865980 was
kernel-replayed, committed, pushed, and successfully submitted. `lax submit
--resume` confirmed publication at `6fe5a3d94f6c2da46cc2c5ab98cd36997b130737`.
Lax560851 now pins that Lax759944 concept package; `lax sync` and dependency resolution
accepted it. No local replacement of an archive dependency is being used.

Implemented:

- `BitPolynomialTime.BitPolynomialTimeUsing`: explicit presentation/output/size,
  polynomial time and sufficient bit width, instantiated through the existing
  capacity predicate. It requires the arena to fit at the sufficient width.
- `RamPolynomialComparison.BitPolynomialTime`: natural-list input with the
  same binary size as Lax759944, arena input, and one-word natural output.
- The comparison concept states the general equivalence and both halves of
  the `exponentialLength xs = 2 ^ xs.length` separation. Comments explain
  the different size and width conventions.
- `RamOutputBounds`: all exact output words fit, for every program/run.
- `RamPolynomialSeparation`: the exponential example fails `TimeBounded`
  for every time allowance, and therefore fails `PolynomialTime`.
- `RamExponentialExample`: the example satisfies the new bit-polynomial
  definition, using six executed RAM instructions and width `bitSize xs + 4`.
- `BitPolynomialTime.using_iff`: proved conversion between the capacity-form
  API and the usual quantification over every sufficiently large bit width.
- New regression tests check actual runs (including empty input), both
  theorem endpoints, and exact background-axiom sets.
- `RamVirtualMemory`, `RamVirtualCompiler`, and `RamVirtualSimulation`:
  interleaved virtual/scratch memory and a verified constant-overhead
  simulation of arbitrary programs.
- `RamArenaToNativeCompiler` and its simulation convert native
  length-prefixed input into the structural arena seen by a virtual program.
  `RamNativeToArenaCompiler` and its simulation perform the reverse
  conversion, buffering the native payloads in protected scratch cells.
- `RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime` now proves the
  general class equivalence. Each implication selects a new word polynomial
  and a new time polynomial independently. No degree equality, degree
  preservation, or common-degree witness is stated or used.

Final local validation passes. The aggregate proof build completed all 1,258
jobs; `bash scripts/check-certified.sh` passed its 814-job closed-derivation
suite and 1,247-job RAM prerequisite build. Independent Lax replay then
kernel-checked and inspected 12 concepts and 18 proofs in 3m21s. The final
equivalence proof's guarded audit reports only `propext`, `Classical.choice`,
and `Quot.sound`; it does not assume its own concept statement. The two
machine translations establish exact output preservation and the bounds
`18*t+26` (native to arena) and `66*t+6*B+81` (arena to native), where `B` is
binary input size. Thus every nonconstant time degree is preserved, while a
constant arena-time witness may become linear. Both width witnesses are
translated as `Q+7`; no same-degree claim is part of the equivalence. The
constant seven-bit reserve supplies all fixed address and arena-root margins.

The explanatory PDF has been regenerated and both pages visually inspected.
The refreshed local preview lists 12 concepts and 18 proofs, marks
`RamPolynomialComparison` proved, and links the equivalence proof with no
outstanding assumptions. The implementation is published in the current
public draft revision. Lax842588 and `Archive.zip` remain untouched.
`RAM_EQUIVALENCE_PLAN.md` is retained as the implementation record rather than
as an open-work checklist.

The explanatory comparison is also available as
[`docs/ram-polynomial-time-comparison.pdf`](docs/ram-polynomial-time-comparison.pdf)
with editable LaTeX alongside it. It includes input magnitude in the comparison
table, explains capacity versus bit width, and gives the separating example.
The opening definitions of `n`, `m`, `B`, and `inputMagnitude` are displayed
on four aligned lines. The two-page PDF compiled successfully; both original
pages and the revised first-page layout were visually inspected.
It is supporting documentation, not a submitted paper or a Lean proof.

## Implemented

For a short explanation and usage example, see [README.md](README.md).
The guide presents formulas, finite relational structures, trees, and automata
as examples of the general framework, rather than centering one application.

The original mathematical surface is `StructuralPresentation`, `StructuralCombinators`,
and `WordArena`, with `FormulaExample` as a separate illustrative concept.
It encodes the propositional formula `p₀ ∧ ¬p₁` and constructs its exact word input.
Three additional modules are explicitly labeled infrastructure:
`CertifiedDerivation` is the small field-agreement API (no elaborator code),
`CertifiedDerivationElab` implements the closed command, and
`StructuralDerivation` provides unrestricted low-level folds. Lax currently
counts those seven as concept modules; the local extension adds three more.
No unsupported hidden-helper category is
assumed. `FieldEncoding` is not a no-advice certificate; `structuralLaw%` is removed.

`CertifiedDerivationElab` supplies `derive_certified_encoding`, generating the encoder,
complete constructor-law proposition (`.Laws`), and witness (`.certified`)
together. Its closed field resolver permits Nat, Fin, proof-erased subtypes,
finite families, direct recursive children, and previously registered
constructor derivations. Unsupported fields fail; errors roll back the
command. There is no arbitrary `toRaw` or typeclass fallback.

`CertifiedFieldEncoding` is indexed by the canonical function and law, with
`agrees : toRaw = canonical`. Privacy alone is **not** a kernel seal: Lean's
`constructor` tactic can access private structure constructors. The closed
generator/registry establishes provenance; the kernel checks the generated
equations and witnesses. A standalone certificate for an arbitrary different
specification is not a registered certified datatype. The public `ofLaws`
helper packages an exact specified encoder and a supplied proof only; it does
not register anything. A regression checks that such a value cannot admit an
unregistered datatype into closed field resolution.

Lax-53 now uses four compact commands for terms, relations, intrinsic formulas,
and trees. Their represented fields transitively bottom out in Nat/Fin.
This is a content-provenance guarantee, not a cost bound for enumerating a
finite family. Compiler/runtime refinements belong to Lax-53, not Lax-58.

## Validation

- Adding `FormulaExample` passed full local validation and independent kernel
  replay (session `51014`, 30s, seven concepts and fifteen proofs). The local
  Lax-58 preview now lists the example as a separate concept.
- The extended certification suite passes (session `90504`, 439 build jobs),
  including the example's exact constructor expansion and certificate audit.
- The README's complete Lean example was extracted and checked with
  `lake env lean --stdin` (session `63266`); it compiles and prints the
  encoder, full laws, and certificate.
- The local preview rebuild after the author update passed full validation
  and kernel replay (session `86625`, 39s, six concepts and fifteen proofs).
- After the module split, `env LEAN_NUM_THREADS=2 lax build . --replay --no-color`
  passed on 2026-09-05: six modules and fifteen proofs, including independent
  kernel replay (1m24s). The generated preview now labels infrastructure explicitly.
- `bash scripts/check-certified.sh` passes the split module build and both
  agreement/derivation suites:
  primitive/transitive fields, dependent families, malicious low-level
  instances, hidden/unsupported fields, rollback, record-update and
  constructor-tactic attacks. `tests/EncodingAgreement.lean` also passed with
  only the small agreement module imported.
- Downstream focused concepts/proofs, concrete equations, axiom audits, and
  both certificate report modes passed. Full downstream status
  is maintained in [Lax-53 current state](../MSO-automata-trees/CURRENT_STATE.md).
- The closed certification suites in both repositories passed again after
  completion of Lax-53's two unchanged headline proofs (session `7534`).
  No Lax-58 implementation or concept changes were needed for this milestone.

## Constraints and next action

Public Git publication is complete at https://github.com/szymtor/lax58.
`origin` is configured and `main` tracks `origin/main`.
Lax draft submission succeeded for commit
`86319376d4ce21dfdfa796713e06f18c575de972`:
https://laxarchive.org/lax-560851/. Archive workflow `34054472817` rebuilt and
published the draft successfully. Registration has not been requested.
The manifest lists Jan Dreier,
Szymon Toruńczyk, and ChatGPT (5.6 and 6).

Keep this boundary narrow; extend the approved grammar only for a concrete
client need with positive and negative tests. Follow [WORKFLOW.md](WORKFLOW.md).
Lax-53 archive validation is blocked by archive source resolution, not by a
failed Lax-58 replay. Do not publish to bypass it. Preserve `Archive.zip` and
all unrelated dirty changes. `Archive.zip` and generated build artifacts are
excluded from the publication commit. The local extension adds the Lax865980 pin
noted above; existing dependency pins were not changed.

History: [SESSION_HISTORY.md](SESSION_HISTORY.md).
