# Lax-58 development workflow

Read [CURRENT_STATE.md](CURRENT_STATE.md) first. This package owns structural
content provenance, the distinguished immutable arena, and an encoding-aware
resource predicate over the existing Lax865980 RAM model. It does not own automata,
mutable compiler storage, or a new machine cost model.

Keep agreement definitions in `CertifiedDerivation` free of elaborator code;
constructor inspection and the private registry belong to
`CertifiedDerivationElab`. Both are infrastructure, not new mathematical
definitions of advice-freedom. Lax currently requires their concept annotations;
do not hide the tooling in an undeclared directory or import it from proofs.

## Changing certified derivation

1. State the needed field form and its canonical Nat/Fin-based interpretation.
2. Extend only the closed resolver; do not add a typeclass search, user witness
   registration, or arbitrary encoder escape hatch.
3. Generate the encoder, complete laws, and witness in one atomic command.
   Embed expressions directly; pretty-printing is only for inspection.
4. Add acceptance, malicious-override, and unsupported-field tests. Check
   failed commands leave neither definitions nor registry entries behind.
5. Review the downstream expanded certificate diff. A new axiom dependency,
   missing constructor case, hidden payload, or changed raw layout requires
   an explicit explanation. Privacy is not a kernel trust boundary.

## Validation tiers

`RamComplexityElab` is a read-only client of the closed derivation registry.
Keep its Nat/list/product, subtype, and finite-family rules explicit. Never
replace them with an unrestricted presentation instance search. The same
resolver must select input encodings for the predicate and `inputMagnitude`.
Test exact expanded propositions, fixed output conventions, imported registry
entries, and rejection of unregistered inputs and outputs after each change.

From this repository root:

```sh
bash scripts/check-certified.sh
```

This builds the changed concept and runs the negative/positive regression
suite with two Lean threads by default. For a release-sized milestone:

```sh
env LEAN_NUM_THREADS=2 lax build . --replay --no-color
```

Then run Lax-53's focused suite and certificate report with its local Lax-58
override. Run its full proof root after shared API/layout changes. A successful
local Lake build is not archive validation. Do not change archive pins or
publish merely to make a local check pass.

Update `CURRENT_STATE.md` with the exact completed checks and blockers; put
chronological detail in `SESSION_HISTORY.md`. Preserve user changes and
`Archive.zip`. No registration or publication without the user's action.
