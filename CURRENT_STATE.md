# Lax-58 current state

Updated: 2026-09-05. Validated implementation prepared for Git publication.

## Implemented

For a short explanation and usage example, see [README.md](README.md).
The guide presents formulas, finite relational structures, trees, and automata
as examples of the general framework, rather than centering one application.

The mathematical surface is `StructuralPresentation`, `StructuralCombinators`,
and `WordArena`, with `FormulaExample` as a separate illustrative concept.
It encodes the propositional formula `p₀ ∧ ¬p₁` and constructs its exact word input.
Three additional modules are explicitly labeled infrastructure:
`CertifiedDerivation` is the small field-agreement API (no elaborator code),
`CertifiedDerivationElab` implements the closed command, and
`StructuralDerivation` provides unrestricted low-level folds. Lax currently
counts all seven as concept modules; no unsupported hidden-helper category is
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

The user has authorized a Git commit and public Git publication. The destination
is awaiting confirmation because this repository has no configured remote.
Lax submission and registration remain paused. The manifest lists Jan Dreier,
Szymon Toruńczyk, and ChatGPT (5.6 and 6).

Keep this boundary narrow; extend the approved grammar only for a concrete
client need with positive and negative tests. Follow [WORKFLOW.md](WORKFLOW.md).
Lax-53 archive validation is blocked by archive source resolution, not by a
failed Lax-58 replay. Do not publish to bypass it. Preserve `Archive.zip` and
all unrelated dirty changes. `Archive.zip` and generated build artifacts are
excluded from the publication commit. No dependency pins were changed.

History: [SESSION_HISTORY.md](SESSION_HISTORY.md).
