#!/usr/bin/env bash
# Check the actual-event bridge after compiling Errors and the auxiliary evaluation modules.
# Run from the matching Lake project. The second path defaults to ArkLib's normal build directory.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
auxiliary_lib="${1:?usage: check-mca-event-bridge.sh AUXILIARY_LIB [ARKLIB_LIB]}"
arklib_lib="${2:-$repo_root/.lake/build/lib/lean}"
proof="$repo_root/scripts/probes/astra_mca_event_bridge.lean"

python3 "$repo_root/scripts/forbidden_tokens.py" "$proof"
lake env python3 - "$repo_root" "$proof" "$auxiliary_lib" "$arklib_lib" <<'PY'
import os
from pathlib import Path
import subprocess
import sys

repo_root, proof, auxiliary_lib, arklib_lib = sys.argv[1:]
child_env = os.environ.copy()
# Prefer the complete ArkLib namespace over the auxiliary prime-certificate subtree.
child_env["LEAN_PATH"] = os.pathsep.join([
    str(Path(arklib_lib).resolve()),
    str(Path(auxiliary_lib).resolve()),
    child_env.get("LEAN_PATH", ""),
])
result = subprocess.run(["lean", "--root=" + repo_root, proof], env=child_env)
raise SystemExit(result.returncode)
PY
