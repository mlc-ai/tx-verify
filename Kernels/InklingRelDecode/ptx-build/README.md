# Rebuilding the kernel's PTX

The frozen PTX of this kernel (`../rel_verify_sm100a.ptx`) is the output of Triton 3.8.0 and the
`ptxas` of CUDA 13.2.51 (sm_100a) on the Gluon kernel `_rel_verify_kernel` of vLLM, with the one
synchronization fix of `attention-sync.patch`. No GPU is needed to rebuild it. The scripts here
generate PTX; they generate no proof.

The kernel is vLLM pull request 67325, commit `d664cd1e96052857aea2aa844eeba571c24758b4`,
`vllm/models/inkling2/ops/attention.py` (sha256 `4e8bd916...`, see `../manifest.json`), plus this
patch. The patch makes the softmax warps wait for `o_done` in every iteration `i > 0` (PTX ISA 9.5,
§9.7.15.16.5.1).

## Inputs

* the pinned `attention.py` of the commit above (not part of this repository);
* a Python 3.11 virtual environment with Triton 3.8.0 (`BUILD_DIR/venv`);
* `ptxas` of CUDA 13.2.51, given by `TRITON_PTXAS_BLACKWELL_PATH` or `--ptxas`;
* `../manifest.json` (its `config` gives the constexpr arguments).

## Commands

All paths are arguments; nothing here names a local directory.

```
# 1. apply the patch to a copy of the pinned file
cp PINNED/attention.py BUILD_DIR/attention_patched.py
patch BUILD_DIR/attention_patched.py attention-sync.patch

# 2. rebuild the unmodified kernel (the previous frozen reference, sha256 fa719b76...)
./ns_run.sh BUILD_DIR PINNED/attention.py BUILD_DIR/repro.ptx 1100

# 3. rebuild the patched kernel (the frozen PTX, sha256 7be78764...)
./ns_run.sh BUILD_DIR BUILD_DIR/attention_patched.py BUILD_DIR/patched.ptx 1101
```

`BUILD_DIR` holds `venv/`, `gen_ptx.py` (copy of this directory's) and an empty `triton-cache/`.
`ns_run.sh` mounts the build directory at `/tmp/inkling-decode-source` in a private mount namespace
(the debug section of the PTX records that path), so the PTX is reproduced byte for byte.
`MANIFEST=../manifest.json` (or `--manifest`) selects the manifest.

## A build is valid only through `ns_run.sh`

The debug sections of the PTX name the directory the sources were read from, as `.b8` bytes. A
build made outside the mount namespace of `ns_run.sh` writes a machine-local absolute path there
(and different section lengths). Only the `/tmp/inkling-decode-source` build is the frozen PTX;
`tests/test_ptx_debug_paths.py` fails when a debug path starts with anything else.

## Hardware check of two builds

`hw_check.py MODULE_A.py MODULE_B.py [--timing]` compares `OPart` and `LsePart` of two builds
bit for bit on random inputs, including splits with no key block (`num_iters = 0`), on a B200.
