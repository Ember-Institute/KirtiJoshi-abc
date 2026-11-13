#!/usr/bin/env bash
set -euo pipefail

# Apply the Lean 4.33.1 compatibility patches to the locked dependencies.
# Upstream: https://github.com/lana-agents/formal-schemes
# Revision: 51aa935079537bf4dc580751a6e70727fb23ca93
# This script does not compile Lean sources.
patch_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
project_dir=$(dirname -- "$patch_dir")
formal_dir="$project_dir/.lake/packages/formal-schemes"
formal_revision=51aa935079537bf4dc580751a6e70727fb23ca93
formal_patch="$patch_dir/patches/formal-schemes-lean433.patch"

if [ "$(git -c safe.directory="$formal_dir" -C "$formal_dir" rev-parse HEAD)" != "$formal_revision" ]; then
  printf '%s\n' "formal-schemes must be checked out at $formal_revision." >&2
  exit 1
fi

if git -c safe.directory="$formal_dir" -C "$formal_dir" apply --reverse --check "$formal_patch" 2>/dev/null; then
  printf '%s\n' 'The formal-schemes compatibility patch is already applied.'
else
  git -c safe.directory="$formal_dir" -C "$formal_dir" apply --check "$formal_patch"
  git -c safe.directory="$formal_dir" -C "$formal_dir" apply "$formal_patch"
  printf '%s\n' 'Applied the formal-schemes compatibility patch.'
fi

tate_dir="$project_dir/.lake/packages/tate-curves-theta"
tate_revision=ca6c2279d3cea0690cdb01328e727118d5485d68
tate_patch="$patch_dir/patches/tate-curves-theta-lean433.patch"
if [ "$(git -c safe.directory="$tate_dir" -C "$tate_dir" rev-parse HEAD)" != "$tate_revision" ]; then
  printf '%s\n' "tate-curves-theta must be checked out at $tate_revision." >&2
  exit 1
fi
if git -c safe.directory="$tate_dir" -C "$tate_dir" apply --reverse --check "$tate_patch" 2>/dev/null; then
  printf '%s\n' 'The tate-curves-theta compatibility patch is already applied.'
else
  git -c safe.directory="$tate_dir" -C "$tate_dir" apply --check "$tate_patch"
  git -c safe.directory="$tate_dir" -C "$tate_dir" apply "$tate_patch"
  printf '%s\n' 'Applied the tate-curves-theta compatibility patch.'
fi
