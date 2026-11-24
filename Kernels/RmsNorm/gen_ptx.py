# SPDX-License-Identifier: Apache-2.0
"""Regenerate rmsnorm.ptx: compile tirx-kernels' rmsnorm (hidden size 4096) to PTX.

``rmsnorm.py`` next to this script is a copy of ``tirx_kernels/norm/rmsnorm.py``
(tirx-kernels 7ab6f52); this script compiles the installed ``tirx_kernels`` module, so the
two must agree. Needs TVM-TIRx and tirx-kernels on ``PYTHONPATH`` and nvcc; no GPU.
"""

import argparse
import sys
import types
from pathlib import Path

import tvm_tirx  # noqa: F401  (load before stubbing torch)

# The kernel module imports torch only for its test and benchmark helpers.
sys.modules.setdefault("torch", types.SimpleNamespace(float16="float16"))

from tirx_kernels.norm import rmsnorm  # noqa: E402
from tirx_kernels.runner import compile_kernel  # noqa: E402

HERE = Path(__file__).resolve().parent
LICENSE = (HERE.parent / "BlockSum" / "block_sum.cu").read_text().split("\n")[0] + "\n"


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("-o", "--output", type=Path, default=HERE / "rmsnorm.ptx")
    args = cli.parse_args()
    config = {"cuda": {"compiler": "nvcc", "target_format": "ptx", "arch": "sm_100a"}}
    kernel = rmsnorm.make_kernel(4096, backend_config=config)
    executable = compile_kernel(kernel.func, backend_config=config)
    cuda = next(m for m in executable.mod.imports if m.kind == "cuda")
    args.output.write_text(LICENSE + "\n" + cuda.inspect_source("ptx"))
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
