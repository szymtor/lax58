#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
cd -- "$script_dir/../concepts"
lake build Lax58.CertifiedDerivationElab Lax58.StructuralDerivation Lax58.FormulaExample Lax58.RamComplexityExample
lake env lean ../tests/EncodingAgreement.lean
lake env lean ../tests/CertifiedDerivation.lean
lake env lean ../tests/FormulaExample.lean
lake env lean ../tests/RamComplexity.lean
cd ../proofs
lake build Lax58Proofs.RamExponentialExample Lax58Proofs.BitPolynomialTime Lax58Proofs.RamVirtualMacros
lake env lean ../tests/RamPolynomialComparison.lean
lake env lean ../tests/RamVirtualCompiler.lean
