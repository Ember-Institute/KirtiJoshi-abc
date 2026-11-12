#!/usr/bin/env bash
set -euo pipefail

# Apply the Lean 4.33.1 compatibility patch to the locked upstream dependency.
# Upstream: https://github.com/lana-agents/formal-schemes
# Revision: 51aa935079537bf4dc580751a6e70727fb23ca93
# This script does not compile Lean sources.
patch_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
project_dir=$(dirname -- "$patch_dir")
formal_dir="$project_dir/.lake/packages/formal-schemes"
formal_revision=51aa935079537bf4dc580751a6e70727fb23ca93
formal_patch="$patch_dir/patches/formal-schemes-lean433.patch"

if [ "$(git -C "$formal_dir" rev-parse HEAD)" != "$formal_revision" ]; then
  printf '%s\n' "formal-schemes must be checked out at $formal_revision." >&2
  exit 1
fi

if git -C "$formal_dir" apply --reverse --check "$formal_patch" 2>/dev/null; then
  printf '%s\n' 'The formal-schemes compatibility patch is already applied.'
else
  git -C "$formal_dir" apply --check "$formal_patch"
  git -C "$formal_dir" apply "$formal_patch"
  printf '%s\n' 'Applied the formal-schemes compatibility patch.'
fi
