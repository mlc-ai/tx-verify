# SPDX-License-Identifier: Apache-2.0
"""Regenerate flash_fwd_sm100.ptx: compile Tri Dao's FlashAttention-4 forward (CuTeDSL) for
the frozen configuration in manifest.json and keep the PTX CuTeDSL produces.

Needs an sm_100 GPU, torch, the pinned nvidia-cutlass-dsl and quack-kernels versions and a
flash-attention checkout at the pinned commit (manifest.json). Only compilation is used:
the PTX is dumped before launch, and a launch-wrapper error of mismatched helper versions
does not affect it. The package's ``__init__`` imports the FlashAttention-2 CUDA extension, so
``flash_attn`` is registered as a bare namespace over the checkout.

Usage: CUDA_VISIBLE_DEVICES=<gpu> python gen_ptx.py --flash-attention <checkout>
"""

import argparse
import glob
import json
import os
import sys
import tempfile
import types
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--flash-attention", type=Path, required=True)
    cli.add_argument("-o", "--output", type=Path, default=HERE / "flash_fwd_sm100.ptx")
    args = cli.parse_args()
    config = json.loads((HERE / "manifest.json").read_text())["config"]
    dump = tempfile.mkdtemp(prefix="fa4-ptx-")
    os.environ["CUTE_DSL_KEEP_PTX"] = "1"
    os.environ["CUTE_DSL_DUMP_DIR"] = dump
    package = types.ModuleType("flash_attn")
    package.__path__ = [str(args.flash_attention / "flash_attn")]
    sys.modules["flash_attn"] = package

    import torch
    from flash_attn.cute.interface import flash_attn_func

    shape = (config["batch"], config["seqlen"], config["num_heads"], config["head_dim"])
    kv_shape = (config["batch"], config["seqlen"], config["num_kv_heads"], config["head_dim"])
    q = torch.randn(shape, dtype=torch.float16, device="cuda")
    k = torch.randn(kv_shape, dtype=torch.float16, device="cuda")
    v = torch.randn(kv_shape, dtype=torch.float16, device="cuda")
    try:
        flash_attn_func(q, k, v, causal=config["causal"])
    except TypeError as error:  # launch wrapper of mismatched helper versions, after compile
        print(f"note: launch skipped ({error})")
    ptx = sorted(glob.glob(os.path.join(dump, "*FlashAttentionForwardSm100*.ptx")))
    if len(ptx) != 1:
        raise SystemExit(f"expected one forward PTX in {dump}, found {ptx}")
    args.output.write_text(Path(ptx[0]).read_text())
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
