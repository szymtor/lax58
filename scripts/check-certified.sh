#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
cd -- "$script_dir/../concepts"
lake build Lax58.CertifiedDerivationElab Lax58.StructuralDerivation Lax58.FormulaExample
lake env lean ../tests/EncodingAgreement.lean
lake env lean ../tests/CertifiedDerivation.lean
lake env lean ../tests/FormulaExample.lean
