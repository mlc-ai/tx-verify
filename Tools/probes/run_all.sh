# SPDX-License-Identifier: Apache-2.0


# Reproduces every hardware probe cited in the Core contract (EXT-* evidence) on one GPU and
# checks each case's expected outcome: zero mismatches against the TxVerify model, or the
# expected fault (illegal instruction, misaligned address) for inputs the model rejects.
# Needs an sm_100a GPU (B200), nvcc and the CUDA driver.
#
# Usage: GPU=2 Tools/probes/run_all.sh   (default GPU 0; NVCC defaults to nvcc on PATH)
# Prints one line per case and the output of any case that does not match its expectation;
# exits nonzero if one does not. Nothing is written outside a temporary directory.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
nvcc="${NVCC:-nvcc}"
export CUDA_VISIBLE_DEVICES="${GPU:-0}"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
fail=0

compile() {  # runner name
  "$nvcc" -o "$build/$1" "$here/$1.cu" -lcuda 2> "$build/$1.err" ||
    { echo "BUILD FAILED: $1"; cat "$build/$1.err"; fail=1; }
}

substitute() {  # ptx placeholder value target
  sed "s/$2/$3/g" "$here/$1" > "$build/$4"
}

check() {  # name expected-pattern command...
  local name="$1" pattern="$2"; shift 2
  local output
  output="$(timeout 60 "$@" 2>&1)"
  if grep -Eq "$pattern" <<< "$output"; then
    echo "ok    $name"
  else
    echo "FAIL  $name (expected /$pattern/):"; sed 's/^/      /' <<< "$output"; fail=1
  fi
}

zero_total='^total mismatched bytes: 0$'
illegal='illegal instruction'
misaligned='misaligned address'

for r in run_tma2d run_tmand run_tma_mc run_tma_gather4 run_tma_mc_gather4 run_tma_scatter4 \
    run_tma_reduce run_tcgen05_ws_ts_i8 run_tcgen05_ws_ts_tf32; do compile "$r"; done

# Tiled loads of rank 1 to 5, multicast, swizzles and box alignment (THREAD-TENSOR-TILE-SHARED,
# THREAD-TENSOR-ISSUE, EXT-TMA-BOX-ALIGN).
check tma2d "$zero_total" "$build/run_tma2d" "$here/tma2d.ptx"
check tma2d-unaligned "$illegal" "$build/run_tma2d" "$here/tma2d.ptx" 64 8 0 0 8 0
check tma2d-store "^box" "$build/run_tma2d" "$here/tma2d_store.ptx" 64 8 0 0 16 0 store
check tma2d-store-unaligned "$illegal" "$build/run_tma2d" "$here/tma2d_store.ptx" 64 8 0 0 8 0 store
check tmand "$zero_total" "$build/run_tmand" "$here"
check tma-mc "$zero_total" "$build/run_tma_mc" "$here/tma_mc.ptx"

# .tile::gather4 and .tile::scatter4 (EXT-TMA-GATHER4, EXT-TMA-SCATTER4).
check gather4 "$zero_total" "$build/run_tma_gather4" "$here/tma_gather4.ptx"
check gather4-box2 "$illegal" "$build/run_tma_gather4" "$here/tma_gather4.ptx" 64 2 0 0 0 0 1 2 3
check gather4-unaligned "$illegal" "$build/run_tma_gather4" "$here/tma_gather4.ptx" 64 1 0 0 8 0 1 2 3
check gather4-misaligned "$misaligned" "$build/run_tma_gather4" "$here/tma_gather4.ptx" 64 1 0 64 0 0 1 2 3
check gather4-mc "$zero_total" "$build/run_tma_mc_gather4" "$here/tma_mc_gather4.ptx"
check scatter4 "$zero_total" "$build/run_tma_scatter4" "$here/tma_scatter4.ptx"
check scatter4-negative-x "$illegal" "$build/run_tma_scatter4" "$here/tma_scatter4.ptx" 64 1 3 0 -16 3 5 6 7
check scatter4-negative-row "$illegal" "$build/run_tma_scatter4" "$here/tma_scatter4.ptx" 64 1 3 0 0 -1 5 6 7
check scatter4-unaligned "$illegal" "$build/run_tma_scatter4" "$here/tma_scatter4.ptx" 64 1 3 0 8 3 5 6 7
check scatter4-box2 "$illegal" "$build/run_tma_scatter4" "$here/tma_scatter4.ptx" 64 2 3 0 0 3 5 6 7
check scatter4-misaligned "$misaligned" "$build/run_tma_scatter4" "$here/tma_scatter4.ptx" 64 1 0 64 0 3 5 6 7

# cp.reduce.async.bulk.tensor (EXT-TMA-REDUCE): op type box-width box-height swizzle offset x y.
reduce_zero=': 0 mismatched elements'
while read -r name args; do
  check "reduce-$name" "$reduce_zero" "$build/run_tma_reduce" "$here/tma_reduce.ptx" $args
done <<'CASES'
add-u32 add u32 16 8 0 0 0 0
add-u32-128b add u32 32 8 3 384 16 3
min-s32-oob min s32 16 8 2 640 48 25
max-u32-oob max u32 32 4 3 0 48 30
and-u32 and u32 16 8 0 256 0 0
or-s32-32b or s32 8 8 1 128 8 2
xor-u32 xor u32 16 8 0 0 0 0
xor-s32 xor s32 16 8 0 0 0 0
inc-u32 inc u32 16 8 0 0 0 0
dec-u32 dec u32 16 8 0 0 0 0
add-s32-bottom add s32 16 8 0 0 0 30
CASES
check reduce-inc-s32 "$illegal" "$build/run_tma_reduce" "$here/tma_reduce.ptx" inc s32 16 8 0 0 0 0
check reduce-dec-s32 "$illegal" "$build/run_tma_reduce" "$here/tma_reduce.ptx" dec s32 16 8 0 0 0 0
check reduce-negative "$illegal" "$build/run_tma_reduce" "$here/tma_reduce.ptx" add s32 16 8 0 0 -4 0
check reduce-unaligned "$illegal" "$build/run_tma_reduce" "$here/tma_reduce.ptx" add u32 16 8 0 0 2 0
check reduce-misaligned "$misaligned" "$build/run_tma_reduce" "$here/tma_reduce.ptx" add u32 16 8 0 64 0 0

# tcgen05.mma.ws with A in Tensor Memory: per-lane A rows and A packing (EXT-TCFIG);
# kind::tf32 input truncation (EXT-TCTF32).
for case in 128:135267488 64:68158624 32:34604192; do
  m="${case%%:*}"; idesc="${case##*:}"
  substitute tcgen05_ws_ts_i8.ptx IDESC "$idesc" "ws$m.ptx"
  for seed in 1 2; do
    check "ws-i8-m$m-s$seed" '^hypothesis 1: 0 mismatches' "$build/run_tcgen05_ws_ts_i8" "$build/ws$m.ptx" "$m" "$seed"
  done
done
substitute tcgen05_ws_ts_tf32.ptx IDESC 135268624 tf32.ptx
for seed in 1 2 3; do
  check "tf32-s$seed" '^truncate: 0 mismatches' "$build/run_tcgen05_ws_ts_tf32" "$build/tf32.ptx" "$seed"
done
for seed in 1 2; do
  check "tf32-lowb-s$seed" '^truncate: 0 mismatches' "$build/run_tcgen05_ws_ts_tf32" "$build/tf32.ptx" "$seed" lowb
done

if [ "$fail" -eq 0 ]; then echo "all probes match"; else echo "some probes differ"; fi
exit "$fail"
