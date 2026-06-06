#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

remote="${ARKLIB_SYNC_REMOTE:-fork}"
target_branch="${ARKLIB_SYNC_TARGET_BRANCH:-main}"
lock_dir="$repo_dir/.codex/arklib-auto-sync.lock"

if ! mkdir "$lock_dir" 2>/dev/null; then
  printf '[%s] previous sync still running; skipping\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  exit 0
fi
trap 'rmdir "$lock_dir" 2>/dev/null || true' EXIT

stamp="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
printf '[%s] sync start\n' "$stamp"

git config rerere.enabled true
git config pull.rebase false

if [ -d .git/rebase-merge ] || [ -d .git/rebase-apply ]; then
  printf '[%s] rebase in progress; refusing to continue\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  exit 1
fi

if [ -f .git/MERGE_HEAD ]; then
  printf '[%s] merge in progress; staging resolved files and committing if possible\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  git add -A
  git commit --no-edit || true
fi

git add -A
if ! git diff --cached --quiet; then
  git commit -m "auto-sync: save ArkLib work ${stamp}"
else
  printf '[%s] no local changes to commit\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
fi

git fetch "$remote" "$target_branch"

if ! git merge --no-edit -X ours "$remote/$target_branch"; then
  printf '[%s] merge reported conflicts; applying local-preferred resolution\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  conflicted="$(git diff --name-only --diff-filter=U || true)"
  if [ -n "$conflicted" ]; then
    printf '%s\n' "$conflicted" | while IFS= read -r path; do
      [ -n "$path" ] || continue
      git checkout --ours -- "$path" || true
      git add -- "$path"
    done
  fi
  git add -A
  git commit --no-edit || git commit -m "auto-sync: merge ${remote}/${target_branch} ${stamp}"
fi

git add -A
if ! git diff --cached --quiet; then
  git commit -m "auto-sync: post-merge cleanup ${stamp}"
fi

git push "$remote" "HEAD:${target_branch}"
printf '[%s] sync pushed HEAD to %s/%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$remote" "$target_branch"
