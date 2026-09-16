#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
# Explicit development overrides are optional; releases use archive pins.
run_lake() {
  if [[ -n "${LAKE_PACKAGES:-}" ]]; then
    lake --packages="$LAKE_PACKAGES" "$@"
  else
    lake "$@"
  fi
}
cd -- "$script_dir/../concepts"
run_lake build Lax560851.CertifiedDerivationElab Lax560851.StructuralDerivation Lax560851.FormulaExample Lax560851.RamComplexityExample
run_lake env lean ../tests/EncodingAgreement.lean
run_lake env lean ../tests/CertifiedDerivation.lean
run_lake env lean ../tests/FormulaExample.lean
run_lake env lean ../tests/RamComplexity.lean
cd ../proofs
run_lake build Lax560851Proofs.RamExponentialExample Lax560851Proofs.BitPolynomialTime Lax560851Proofs.RamVirtualMacros Lax560851Proofs.RamPolynomialComparison
run_lake env lean ../tests/RamFoundations.lean
run_lake env lean ../tests/RamPolynomialComparison.lean
run_lake env lean ../tests/TapeRamPolynomialComparison.lean
run_lake env lean ../tests/RamVirtualCompiler.lean
