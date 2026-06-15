#!/usr/bin/env bash
# Launch a Nebius GPU instance that auto-builds + validates + runs the delta* search
# (via nebius-bootstrap.sh as cloud-init).  Prereqs:
#   1. nebius CLI authenticated:  nebius iam whoami   (federation = browser login)
#   2. an SSH public key in $SSH_PUB (default ~/.ssh/id_ed25519.pub)
#   3. a GPU-ready boot image id in $IMAGE  (Ubuntu 22.04 + NVIDIA driver; see
#      `nebius compute image list`); the bootstrap installs the CUDA toolkit itself.
#
# Usage:  PLATFORM=gpu-h200-sxm PRESET=1gpu-16vcpu-200gb IMAGE=<image-id> ./nebius-launch.sh
#
# GPU choices (all crush the CPU baseline for this 32-bit-integer kernel):
#   gpu-l40s-a   1gpu-16vcpu-64gb     L40S (Ada)   — cheapest; great for validate + n<=36
#   gpu-h200-sxm 1gpu-16vcpu-200gb    H200 (Hopper)— recommended single-GPU for n=32..40
#   gpu-h200-sxm 8gpu-128vcpu-1600gb  8x H200      — max reach (n=40..44, multi-prime scan)
set -euo pipefail
cd "$(dirname "$0")"

PLATFORM="${PLATFORM:-gpu-h200-sxm}"
PRESET="${PRESET:-1gpu-16vcpu-200gb}"
IMAGE="${IMAGE:?set IMAGE to a GPU-ready boot image id (nebius compute image list)}"
SSH_PUB="${SSH_PUB:-$HOME/.ssh/id_ed25519.pub}"
NAME="${NAME:-pg-deltastar-$(date +%s 2>/dev/null || echo run)}"
DISK_GB="${DISK_GB:-100}"

[ -f "$SSH_PUB" ] || { echo "no ssh pubkey at $SSH_PUB (set SSH_PUB)"; exit 1; }

# cloud-init: inject the ssh key + run the bootstrap on first boot
USERDATA=$(mktemp)
{
  echo "#cloud-config"
  echo "ssh_authorized_keys:"
  echo "  - $(cat "$SSH_PUB")"
  echo "runcmd:"
  echo "  - [ bash, -c, \"$(sed 's/\"/\\\"/g' nebius-bootstrap.sh | tr '\n' '\001' | sed 's/\\x01/\\n/g')\" ]"
} > "$USERDATA"
# (simpler/robust alternative if the above quoting is fiddly: pass the raw script)
cp nebius-bootstrap.sh "$USERDATA"   # Nebius accepts a bare #! script as user-data

# NOTE: Nebius `instance create` takes a nested boot-disk spec + a --network-interfaces
# JSON; exact flags are project/version-specific. Verify against
#   nebius compute instance create --help
# The two-step form below is the most portable: create a boot disk from the image,
# then create the instance attaching it. Adjust SUBNET to your project's subnet
# (nebius vpc subnet list).
SUBNET="${SUBNET:?set SUBNET to your project subnet id (nebius vpc subnet list)}"

echo "Creating boot disk from image $IMAGE..."
DISK_ID=$(nebius compute disk create \
  --name "$NAME-boot" \
  --source-image-id "$IMAGE" \
  --size-gibibytes "$DISK_GB" \
  --format json 2>/dev/null | python3 -c 'import sys,json;print(json.load(sys.stdin)["metadata"]["id"])')

echo "Launching $NAME on $PLATFORM/$PRESET (disk $DISK_ID)..."
nebius compute instance create \
  --name "$NAME" \
  --resources-platform "$PLATFORM" \
  --resources-preset "$PRESET" \
  --boot-disk-existing-disk-id "$DISK_ID" \
  --network-interfaces "[{\"name\":\"eth0\",\"subnet_id\":\"$SUBNET\",\"ip_address\":{},\"public_ip_address\":{}}]" \
  --cloud-init-user-data "$(cat "$USERDATA")"

echo
echo "Watch progress:   ssh ubuntu@<instance-ip> 'tail -f /var/log/pg-bootstrap.log'"
echo "Results when done: scp -r ubuntu@<instance-ip>:/root/pg-results ."
echo "DESTROY when done (stop billing): nebius compute instance delete --id <instance-id>"
