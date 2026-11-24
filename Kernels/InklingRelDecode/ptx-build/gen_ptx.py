# SPDX-License-Identifier: Apache-2.0
"""Rebuild the PTX of vLLM Inkling 2 `_rel_verify_kernel` offline (Triton 3.8.0, no GPU needed).

kernel_module.py is rebuilt as 31 header lines (host imports replaced by Triton's own
gl/gluon/tl/tldevice/triton) followed by attention.py lines 492..1100 unchanged and, after them, the inline-asm string constants (lines 403..421), so every
source line L of attention.py sits on line L-460, matching the frozen reference's .loc lines.
The reference's debug info records /tmp/inkling-decode-source/{kernel_module.py,venv/...}; ns_run.sh runs this script
in a private mount namespace where those paths exist, so no rewriting of the PTX is needed (the replace calls below are no-ops there).

Usage: python gen_ptx.py --attention <attention.py> -o <out.ptx> --workdir DIR
       [--manifest manifest.json] [--ptxas PATH] [--last N]

This script generates the PTX of the kernel, not a proof.
"""

import argparse
import json
import os
import sys
from pathlib import Path

HEADER = '''# SPDX-License-Identifier: Apache-2.0
"""Offline slice of vllm/models/inkling2/ops/attention.py (lines 492..1100) for PTX generation."""
import triton
import triton.language as tl
from triton.experimental import gluon
from triton.experimental.gluon import language as gl
from triton.language.extra import libdevice as tldevice
'''
FIRST, LAST, OFFSET = 492, 1100, 460
REF_ROOT = "/tmp/inkling-decode-source"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--attention", type=Path, required=True)
    ap.add_argument("-o", "--output", type=Path, required=True)
    ap.add_argument("--workdir", type=Path, required=True)
    ap.add_argument(
        "--last",
        type=int,
        default=LAST,
        help="last attention.py line of the slice (1100 for the unmodified file)",
    )
    ap.add_argument("--keep-module", type=Path, default=None)
    ap.add_argument(
        "--manifest",
        type=Path,
        default=Path(os.environ.get("MANIFEST", "manifest.json")),
        help="manifest.json of the kernel (its config gives the constexprs)",
    )
    ap.add_argument(
        "--ptxas",
        default=os.environ.get("TRITON_PTXAS_BLACKWELL_PATH", "ptxas"),
        help="the ptxas of CUDA 13.2 for sm_100a (default: \/usr/local/cuda/bin/ptxas)",
    )
    a = ap.parse_args()
    os.environ["TRITON_PTXAS_BLACKWELL_PATH"] = a.ptxas
    os.environ.setdefault("TRITON_CACHE_DIR", str(a.workdir / "triton-cache"))
    lines = a.attention.read_text().split("\n")
    head = HEADER.rstrip("\n").split("\n")
    head += [""] * (FIRST - OFFSET - 1 - len(head))
    assert len(head) == FIRST - OFFSET - 1, len(head)
    body = lines[FIRST - 1 : a.last]
    a.workdir.mkdir(parents=True, exist_ok=True)
    mod = a.workdir / "kernel_module.py"
    consts = lines[
        402:421
    ]  # _EX2_ASM, _EX2_EMU_ASM, _RCP_ASM, _LG2_ASM; module globals, read at JIT time
    mod.write_text("\n".join(head + body + ["", ""] + consts) + "\n")
    sys.path.insert(0, str(a.workdir))
    import importlib

    km = importlib.import_module("kernel_module")
    import triton
    from triton.backends.compiler import GPUTarget
    from triton.experimental.gluon._runtime import GluonASTSource

    layout = km.gl.NVMMASharedLayout.get_default_for([64, 128], km.gl.bfloat16)
    sig = {
        "Q": "*bf16",
        "kv_desc": f"tensordesc<bf16[64,128],{layout!r}>",
        "Rel": "*bf16",
        "BlockTable": "*i32",
        "SeqLens": "*i32",
        "CuSeqlensQ": "*i32",
        "OPart": "*fp32",
        "LsePart": "*fp32",
        "Gate": "*bf16",
        "Sink": "*fp32",
        "Y": "*bf16",
        "softmax_scale": "fp32",
        "stride_q_t": "i32",
        "stride_rel_t": "i32",
        "stride_bt": "i32",
        "stride_gate": "i32",
        "stride_sink": "i32",
        "page_rows": "i32",
        "head_rows": "i32",
        "head_cols": "i32",
        "num_splits": "i32",
        "num_tokens": "i32",
    }
    cfg = json.loads(a.manifest.read_text())["config"]
    constexprs = dict(cfg)
    for k in list(constexprs):
        sig[k] = "constexpr"
    src = GluonASTSource(km._rel_verify_kernel, sig, constexprs)
    ck = triton.compile(
        src,
        target=GPUTarget("cuda", 100, 32),
        options={"num_warps": 4, "num_ctas": 1, "launch_pdl": True},
    )
    ptx = ck.asm["ptx"]
    ptx = ptx.replace(str(mod), f"{REF_ROOT}/kernel_module.py")
    import triton.language.standard as std

    ptx = ptx.replace(
        std.__file__, f"{REF_ROOT}/venv/lib/python3.11/site-packages/triton/language/standard.py"
    )
    a.output.write_text(ptx)
    if a.keep_module:
        a.keep_module.write_text(mod.read_text())
    print("wrote", a.output)


if __name__ == "__main__":
    main()
