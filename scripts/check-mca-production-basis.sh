#!/usr/bin/env bash
# Compile the production-basis proof and its certificate, basis, and residual-row dependencies.
# Run from a Lake project with the matching pinned Mathlib imports cached.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output_dir="${1:?usage: check-mca-production-basis.sh OUTPUT_DIRECTORY}"
mkdir -p "$output_dir"
mca_build_root="$(cd "$output_dir" && pwd)"

prime_module="ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30"
basis_module="scripts/probes/astra_mca_polynomial_basis"
rows_module="scripts/probes/astra_mca_residual_rows"
production_module="scripts/probes/astra_mca_production_basis"

for module in "$prime_module" "$basis_module" "$rows_module" "$production_module"; do
  python3 "$repo_root/scripts/forbidden_tokens.py" "$repo_root/$module.lean"
done

mkdir -p "$mca_build_root/$(dirname "$prime_module")" "$mca_build_root/$(dirname "$basis_module")"
lake env lean --root="$repo_root" -o "$mca_build_root/$prime_module.olean" "$repo_root/$prime_module.lean"
lake env lean --root="$repo_root" -o "$mca_build_root/$basis_module.olean" "$repo_root/$basis_module.lean"

lake env python3 - "$mca_build_root" "$repo_root" "$rows_module" "$production_module" <<'PY'
import os
import subprocess
import sys

build_root, repo_root, *modules = sys.argv[1:]
child_env = os.environ.copy()
child_env["LEAN_PATH"] = build_root + os.pathsep + child_env.get("LEAN_PATH", "")
for module in modules:
    result = subprocess.run(
        ["lean", "--root=" + repo_root, "-o", build_root + "/" + module + ".olean",
         repo_root + "/" + module + ".lean"],
        env=child_env,
    )
    if result.returncode:
        raise SystemExit(result.returncode)
PY
