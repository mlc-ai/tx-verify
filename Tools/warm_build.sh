#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Take another worktree's build artifacts instead of compiling them.
#
#   Tools/warm_build.sh SOURCE_WORKTREE             # copy its build directory into this one
#   Tools/warm_build.sh SOURCE_WORKTREE Mod.A ...   # and check that Lake has nothing to build
#
# Lake decides by content: a trace holds hashes of the sources, options, toolchain and imported
# artifacts, and the absolute paths in it (log lines, input captions) do not enter the hash. So a
# copy is accepted as it is, at another commit too; Lake then rebuilds what differs. The copy
# replaces this worktree's build directory. Both build locks are held while copying, so neither
# worktree builds through Tools/build.sh meanwhile; the source is only read.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
[[ $# -ge 1 ]] || { sed -n '3,7p' "${BASH_SOURCE[0]}"; exit 2; }
SRC="$(cd "$1" && pwd)"
shift
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
[[ "$SRC" != "$ROOT" ]] || { echo "warm_build.sh: the source is this worktree" >&2; exit 2; }
FROM="$(readlink -f "$SRC/.lake/build")"
[[ -d "$FROM/lib/lean" ]] || { echo "warm_build.sh: no build in $SRC" >&2; exit 1; }
mkdir -p "$(readlink -m .lake/build)"
TO="$(readlink -f .lake/build)"
[[ "$FROM" != "$TO" ]] || { echo "warm_build.sh: both worktrees use $TO" >&2; exit 1; }

exec 9>.lake/build.lock
flock -n 9 || { echo "warm_build.sh: this worktree is building" >&2; exit 1; }
if [[ -e "$SRC/.lake/build.lock" ]]; then
  exec 8<"$SRC/.lake/build.lock"
  flock -n -s 8 || { echo "warm_build.sh: $SRC is building" >&2; exit 1; }
fi
here="$(git rev-parse HEAD)" there="$(git -C "$SRC" rev-parse HEAD)"
[[ "$here" == "$there" ]] || echo "warm_build.sh: commits differ: ${there:0:9} -> ${here:0:9}" >&2
rsync -a --delete "$FROM/" "$TO/"
[[ $# -eq 0 ]] || lake build --no-build "$@" >/dev/null || {
  echo "warm_build.sh: copied, but Lake still has modules to build" >&2
  exit 3
}
echo "warm_build.sh: $FROM -> $TO"
