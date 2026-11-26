#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Serialized Lake build. Every session and helper builds through this script so that
# two builds never compete for the machine; the per-file timings in the log stay usable.
#
#   Tools/build.sh                  # lake --wfail build (all default targets)
#   Tools/build.sh Mod.A Mod.B      # lake --wfail build Mod.A Mod.B
#
# Environment: TXVERIFY_BUILD_LOG (log path, default .lake/build-logs/<timestamp>.log),
# TXVERIFY_BUILD_NOWFAIL=1 (plain `lake build`), TXVERIFY_BUILD_SLOTS (builds through this script
# that may run at once on the machine, across worktrees; default 2), TXVERIFY_BUILD_SLOT_DIR
# (where the slot locks live; default /dev/shm/txverify-build-slots).
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

# Machine-wide build slots: at most TXVERIFY_BUILD_SLOTS builds started through this script run at
# once, so that the per-file times of the logs are not a measure of the machine's load. A slot is
# an exclusive `flock` on one file of a fixed directory, held (fd 8) until this script exits.
SLOTS="${TXVERIFY_BUILD_SLOTS:-2}"
SLOT_DIR="${TXVERIFY_BUILD_SLOT_DIR:-/dev/shm/txverify-build-slots}"
if [[ ! -d "$SLOT_DIR" ]]; then
  mkdir -p "$SLOT_DIR" && chmod 1777 "$SLOT_DIR" 2>/dev/null || true
fi
waited=0
while :; do
  for ((i = 0; i < SLOTS; i++)); do
    exec 8>>"$SLOT_DIR/slot.$i"
    if flock -n 8; then
      break 2
    fi
    exec 8>&-
  done
  if [[ $waited == 0 ]]; then
    echo "build.sh: waiting for a build slot (all $SLOTS in use, $SLOT_DIR)" >&2
    waited=1
  fi
  sleep 5
done
[[ $waited == 1 ]] && echo "build.sh: got build slot $i" >&2

# The SHA-1 of the sources and the 1-minute load average (and cores) at the start and the end go
# to <log>.hashes.json: Tools/check_times.py takes a time as evidence only from a quiet log of the
# module's current text.
python3 Tools/check_times.py --record-start "$LOG" 2>/dev/null || true
set +e
run_lake "${FLAGS[@]}" build "$@" >"$LOG" 2>&1
rc=$?
set -e
python3 Tools/check_times.py --record "$LOG" 2>/dev/null || true
ln -sf "$(basename "$LOG")" .lake/build-logs/latest.log
tail -n 40 "$LOG"
echo "build.sh: rc=$rc log=$LOG"
exit $rc
