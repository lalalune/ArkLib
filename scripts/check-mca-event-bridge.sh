#!/usr/bin/env bash
# Check actual events, probability, and threshold after compiling their ArkLib dependencies.
# Run from the matching Lake project. The second path defaults to ArkLib's normal build directory.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
auxiliary_lib="${1:?usage: check-mca-event-bridge.sh AUXILIARY_LIB [ARKLIB_LIB]}"
arklib_lib="${2:-$repo_root/.lake/build/lib/lean}"
modules=(astra_mca_event_bridge astra_mca_production_events astra_mca_production_upper
  astra_mca_single_hole astra_mca_kkh26_upper astra_mca_root_relocation
  astra_mca_four_cubic_seed astra_mca_power_fibers astra_mca_received_assembly
  astra_mca_scaled_polynomials)

for module in "${modules[@]}"; do
  python3 "$repo_root/scripts/forbidden_tokens.py" "$repo_root/scripts/probes/$module.lean"
done
lake env python3 - "$repo_root" "$auxiliary_lib" "$arklib_lib" "${modules[@]}" <<'PY'
import os
from pathlib import Path
import subprocess
import sys

repo_root, auxiliary_lib, arklib_lib, *modules = sys.argv[1:]
child_env = os.environ.copy()
# Prefer the complete ArkLib namespace over the auxiliary prime-certificate subtree.
child_env["LEAN_PATH"] = os.pathsep.join([
    str(Path(arklib_lib).resolve()),
    str(Path(auxiliary_lib).resolve()),
    child_env.get("LEAN_PATH", ""),
])
output_dir = Path(auxiliary_lib).resolve() / "scripts" / "probes"
output_dir.mkdir(parents=True, exist_ok=True)
failed_modules = []
for module in modules:
    proof = str(Path(repo_root) / "scripts" / "probes" / (module + ".lean"))
    result = subprocess.run(
        ["lean", "--root=" + repo_root, "-o", str(output_dir / (module + ".olean")), proof],
        env=child_env,
    )
    if result.returncode:
        failed_modules.append(module)
if failed_modules:
    raise SystemExit("Lean checks failed: " + ", ".join(failed_modules))
PY
