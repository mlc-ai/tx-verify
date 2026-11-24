#!/bin/bash
# Run gen_ptx.py in a private mount namespace where the build venv appears at
# /tmp/inkling-decode-source/venv, the path recorded in the reference PTX debug info.
# The real /tmp is only hidden inside the namespace; nothing outside the build directory is written.
# usage: ns_run.sh <build-dir> <attention.py, absolute> <out.ptx> [last-line, default 1100; 1101 for the patched file]
set -e
exec unshare -Urm bash -c '
set -e
B="$1"; ATT="$2"; OUT="$3"
SP=$(dirname "$B")
exec 9< "$SP"
mount -t tmpfs tmpfs /tmp
mkdir -p /tmp/inkling-decode-source/venv /tmp/inkling-decode-source/sp
mount --bind /proc/self/fd/9 /tmp/inkling-decode-source/sp
N=/tmp/inkling-decode-source/sp/$(basename "$B")
mount --bind $N/venv /tmp/inkling-decode-source/venv
export TRITON_CACHE_DIR=$N/triton-cache
cd /tmp/inkling-decode-source
/tmp/inkling-decode-source/venv/bin/python $N/gen_ptx.py --attention /tmp/inkling-decode-source/sp${ATT#$SP} -o /tmp/inkling-decode-source/sp${OUT#$SP} --workdir /tmp/inkling-decode-source --last $4 --keep-module /tmp/inkling-decode-source/sp${OUT#$SP}.module.py
' _ "$1" "$2" "$3" "${4:-1100}"
