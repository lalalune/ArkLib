#!/usr/bin/env bash
# Post-login one-shot: auto-discover image+subnet, then launch the delta* GPU box.
# PREREQ: you have logged in (`nebius profile create` done; `nebius iam whoami` works).
# Usage:   ./run-nebius-deltastar.sh            # dry-run: shows plan + discovered ids
#          CONFIRM=1 ./run-nebius-deltastar.sh  # actually create the (paid) instance
set -euo pipefail
export PATH="$HOME/.nebius/bin:$PATH"
cd "$(dirname "$0")"

PLATFORM="${PLATFORM:-gpu-h200-sxm}"           # single H200: recommended for n=32..40
PRESET="${PRESET:-1gpu-16vcpu-200gb}"
SSH_PUB="${SSH_PUB:-$HOME/.ssh/id_ecdsa.pub}"   # user has ecdsa/rsa, not ed25519

echo "== auth check =="; nebius iam whoami >/dev/null && echo "OK: $(nebius iam whoami --format json 2>/dev/null | python3 -c 'import sys,json;print(json.load(sys.stdin).get("subject_id","?"))' 2>/dev/null || echo authed)"

echo "== discovering GPU-ready Ubuntu image =="
IMAGE="${IMAGE:-$(nebius compute image list --format json 2>/dev/null \
  | python3 -c 'import sys,json;ims=json.load(sys.stdin).get("items",[]);
c=[i for i in ims if "ubuntu" in (i.get("metadata",{}).get("name","")+i.get("spec",{}).get("name","")).lower()];
print((c or ims)[0]["metadata"]["id"] if (c or ims) else "")' 2>/dev/null)}"
echo "  IMAGE=$IMAGE"

echo "== discovering subnet =="
SUBNET="${SUBNET:-$(nebius vpc subnet list --format json 2>/dev/null \
  | python3 -c 'import sys,json;s=json.load(sys.stdin).get("items",[]);print(s[0]["metadata"]["id"] if s else "")' 2>/dev/null)}"
echo "  SUBNET=$SUBNET"

[ -n "$IMAGE" ] && [ -n "$SUBNET" ] || { echo "!! could not auto-discover IMAGE/SUBNET — run: nebius compute image list / nebius vpc subnet list, then pass IMAGE=.. SUBNET=.."; exit 1; }
[ -f "$SSH_PUB" ] || { echo "!! no ssh pubkey at $SSH_PUB (set SSH_PUB=)"; exit 1; }

echo
echo "PLAN: launch $PLATFORM / $PRESET (single H200), boot from $IMAGE, subnet $SUBNET, key $SSH_PUB"
echo "      cloud-init auto: build rust-pg + cuda-pg, validate vs reference, run n=32/36/40/44 (rho=1/4) + 3-prime p-dependence scan."
echo "      Results -> /root/pg-results on the box. DESTROY after to stop billing."
if [ "${CONFIRM:-0}" != "1" ]; then
  echo; echo ">> DRY RUN. Re-run with CONFIRM=1 to actually create the (paid) instance."
  exit 0
fi
echo ">> CONFIRM=1 set — launching..."
PLATFORM="$PLATFORM" PRESET="$PRESET" IMAGE="$IMAGE" SUBNET="$SUBNET" SSH_PUB="$SSH_PUB" ./nebius-launch.sh
