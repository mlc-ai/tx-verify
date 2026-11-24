#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Serialized Lake build. Every session and helper builds through this script so that
# two builds never compete for the machine; the per-file timings in the log stay usable.
#
#   Tools/build.sh                  # lake --wfail build (all default targets)
#   Tools/build.sh Mod.A Mod.B      # lake --wfail build Mod.A Mod.B
#
# Environment: TXVERIFY_BUILD_LOG (log path, default .lake/build-logs/<timestamp>.log),
# TXVERIFY_BUILD_NOWFAIL=1 (plain `lake build`).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake/build-logs
LOG="${TXVERIFY_BUILD_LOG:-.lake/build-logs/$(date +%Y%m%d-%H%M%S)-$$.log}"
FLAGS=(--wfail)
[[ "${TXVERIFY_BUILD_NOWFAIL:-0}" == 1 ]] && FLAGS=()

# Lean asks for 2 MiB huge pages. On a host whose memory is too fragmented to supply them the
# kernel spends its time in memory compaction instead, and a module that takes seconds takes
# minutes: on one such host the same 18 modules took 299 s on average with huge pages and 2.6 s
# without, with 13,346 compaction stalls meanwhile. Disabling huge pages for the build's process
# tree fixes it and changes no output. `prctl(PR_SET_THP_DISABLE)` is per address space, so it has
# to be set in the process that becomes `lake` (`exec` keeps the setting); a helper that sets it
# and exits would not affect its parent. Check with `grep AnonHugePages /proc/<pid>/smaps`.
run_lake() {
  if command -v python3 >/dev/null 2>&1; then
    python3 -c 'import ctypes, os, sys
try:
    ctypes.CDLL("libc.so.6", use_errno=True).prctl(41, 1, 0, 0, 0)
except Exception:
    pass
os.execvp(sys.argv[1], sys.argv[1:])' lake "$@"
  else
    lake "$@"
  fi
}

exec 9>.lake/build.lock
if ! flock -n 9; then
  echo "build.sh: waiting for another build to finish" >&2
  flock 9
fi
set +e
run_lake "${FLAGS[@]}" build "$@" >"$LOG" 2>&1
rc=$?
set -e
ln -sf "$(basename "$LOG")" .lake/build-logs/latest.log
tail -n 40 "$LOG"
echo "build.sh: rc=$rc log=$LOG"
exit $rc
