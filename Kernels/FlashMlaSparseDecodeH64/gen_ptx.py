#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regenerate `v41_h64_no_split_plain.ptx` from the pinned FlashMLA source.

The command line mirrors `surveys/flashmla/scripts/build_ptx.sh`: nvcc emits PTX for
`sm_100a`, without `-lineinfo` and without `--source-in-ptx`, and the CUDA sources are
compiled by the same flags as the production build (minus the ptxas options, which a
`-ptx` compilation does not run).  The checked-in file is byte-identical to the archived
one; `--check` verifies its SHA256 without needing nvcc.

    python gen_ptx.py --flash-mla <FlashMLA checkout> [-o v41_h64_no_split_plain.ptx]
    python gen_ptx.py --check
"""

import argparse
import hashlib
import os
import shutil
import subprocess
import sys
from pathlib import Path

COMMIT = "395cb3afbb331fef7b1b21e9340861b9436b42d8"
SOURCE = "csrc/cuda_kernels/sm100/decode/sparse/head64/instantiations/v41_h64_no_split.cu"
SHA256 = "7bc254103f5f5593dce7b94729b715738b7fe2de3550cd18fe1ff82dd841a28d"
INSTRUCTIONS = 3612

FLAGS = [
    "-ptx",
    "-gencode",
    "arch=compute_100a,code=sm_100a",
    "-DTORCH_TARGET_VERSION=0x020a000000000000",
    "-DUSE_CUDA",
    "-O3",
    "-std=c++20",
    "-Wno-deprecated-declarations",
    "-U__CUDA_NO_HALF_OPERATORS__",
    "-U__CUDA_NO_HALF_CONVERSIONS__",
    "-U__CUDA_NO_HALF2_OPERATORS__",
    "-U__CUDA_NO_BFLOAT16_CONVERSIONS__",
    "--expt-relaxed-constexpr",
    "--expt-extended-lambda",
    "--use_fast_math",
    "--diag-suppress=445",
    "-DNDEBUG",
    "-DFLASH_MLA_IS_BUILD_ON_CUDA",
]
INCLUDES = [
    "csrc",
    "csrc/3rdparty/cutlass/include",
    "csrc/3rdparty/cutlass/tools/util/include",
    "csrc/3rdparty/kerutils/include",
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--flash-mla", type=Path, help="FlashMLA checkout at the pinned commit")
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent / "v41_h64_no_split_plain.ptx",
    )
    parser.add_argument(
        "--check", action="store_true", help="verify the checked-in file without running nvcc"
    )
    args = parser.parse_args()

    if args.check:
        if not args.output.exists():
            sys.exit(f"missing {args.output}")
        actual = digest(args.output)
        if actual != SHA256:
            sys.exit(f"{args.output}: sha256 {actual}, expected {SHA256}")
        print(f"{args.output}: sha256 {actual}, {INSTRUCTIONS} instructions")
        return 0

    if args.flash_mla is None:
        sys.exit("--flash-mla is required unless --check is given")
    root = args.flash_mla.resolve()
    source = root / SOURCE
    if not source.exists():
        sys.exit(f"missing {source}")
    head = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, text=True, check=True
    ).stdout.strip()
    if head != COMMIT:
        print(f"warning: FlashMLA HEAD is {head}, the pinned commit is {COMMIT}")
    command = ["nvcc", *FLAGS]
    for include in INCLUDES:
        command += ["-I", str(root / include)]
    cuda_home = os.environ.get("CUDA_HOME")
    if not cuda_home:
        nvcc = shutil.which("nvcc")
        if nvcc:
            cuda_home = str(Path(nvcc).resolve().parents[1])
    if cuda_home:
        command += ["-I", str(Path(cuda_home) / "targets/x86_64-linux/include/cccl")]
    command += [str(source), "-o", str(args.output)]
    subprocess.run(command, check=True)
    actual = digest(args.output)
    if actual != SHA256:
        sys.exit(f"{args.output}: sha256 {actual}, expected {SHA256}")
    print(f"{args.output}: sha256 {actual}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
