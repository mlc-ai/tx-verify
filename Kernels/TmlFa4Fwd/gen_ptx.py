"""Compile the tml-fa4 (+ vLLM inkling2 patch) SM100 forward kernel exactly the way vLLM's
Inkling2FA4RelAttentionKernel.compile() does (FakeTensorMode, compile only, no launch), and keep
the PTX CuTeDSL produces.

Usage: CUDA_VISIBLE_DEVICES=<gpu> python -I gen_ptx_inkling2.py --tml-fa4 <patched checkout>
       --layer full|local --page-size 16|128 --max-seqlen-q N --num-splits S
       [--use-scheduler] --heads 12 --kv-heads 2 -o out.ptx
"""

import argparse
import glob
import os
import sys
import tempfile
import types
from pathlib import Path


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("--tml-fa4", type=Path, required=True)
    cli.add_argument("--layer", choices=["full", "local"], required=True)
    cli.add_argument("--page-size", type=int, default=16)
    cli.add_argument("--max-seqlen-q", type=int, default=8192)
    cli.add_argument("--num-splits", type=int, default=1)
    cli.add_argument("--use-scheduler", action="store_true")
    cli.add_argument("--heads", type=int, default=12)
    cli.add_argument("--kv-heads", type=int, default=2)
    cli.add_argument("--num-reqs", type=int, default=1)
    cli.add_argument("-o", "--output", type=Path, required=True)
    a = cli.parse_args()

    dump = tempfile.mkdtemp(prefix="tmlfa4-ptx-")
    os.environ["CUTE_DSL_KEEP_PTX"] = "1"
    os.environ["CUTE_DSL_DUMP_DIR"] = dump
    pkg = types.ModuleType("flash_attn")
    pkg.__path__ = [str(a.tml_fa4 / "flash_attn")]
    sys.modules["flash_attn"] = pkg

    import torch
    from torch._subclasses.fake_tensor import FakeTensorMode
    import flash_attn.cute.interface as iface
    from flash_attn.cute.interface import _flash_attn_fwd

    # This host's CUDA runtime cannot initialize (driver error); compilation needs no device,
    # so fix the target to sm_100 (B200) instead of querying it.
    if not torch.cuda.is_available():
        iface._get_device_arch = lambda: 100
        os.environ.setdefault("CUTE_DSL_ARCH", "sm_100a")

    # LOGCFG: print the kernel-class options the interface selects.
    import flash_attn.cute.flash_fwd_sm100 as fwd

    _init = fwd.FlashAttentionForwardSm100.__init__

    def _logged(self, *args, **kw):
        print("FlashAttentionForwardSm100 args:", args, kw)
        _init(self, *args, **kw)

    fwd.FlashAttentionForwardSm100.__init__ = _logged
    head_dim, rel_extent, dtype = 128, 1024, torch.bfloat16  # Inkling 2 Small config
    window = (rel_extent - 1, 0) if a.layer == "local" else (-1, -1)
    left, right = (None, None) if window == (-1, -1) else window
    num_reqs = a.num_reqs
    with FakeTensorMode():
        dev = torch.device("cuda")
        total_q = a.max_seqlen_q + num_reqs - 1
        q = torch.empty(total_q, a.heads, head_dim, dtype=dtype, device=dev)
        kv = torch.empty(1, 2, a.page_size, a.kv_heads, head_dim, dtype=dtype, device=dev)
        key_cache, value_cache = kv.unbind(1)

        def it(*s):
            return torch.empty(*s, dtype=torch.int32, device=dev)

        out = torch.empty_like(q, dtype=torch.float32)
        lse = torch.empty(a.heads, total_q, dtype=torch.float32, device=dev)
        bias = torch.empty(total_q + 128, a.heads, rel_extent + 256, dtype=dtype, device=dev)
        # Same call as vllm/models/inkling2/ops/attention.py Inkling2FA4RelAttentionKernel.kernel
        _flash_attn_fwd(
            q,
            key_cache,
            value_cache,
            bias=bias,
            bias_ex2_emu=True,
            cu_seqlens_q=it(num_reqs + 1),
            seqused_k=it(num_reqs),
            max_seqlen_q=a.max_seqlen_q,
            page_table=it(num_reqs, 1),
            softmax_scale=head_dim**-0.5,
            causal=True,
            window_size_left=left,
            window_size_right=right,
            pack_gqa=False,
            num_splits=a.num_splits,
            disable_scheduler_metadata=not a.use_scheduler,
            return_lse=True,
            out=out,
            lse=lse,
        )
    ptx = sorted(glob.glob(os.path.join(dump, "*FlashAttentionForwardSm100*.ptx")))
    print("dumped:", sorted(os.listdir(dump)))
    if len(ptx) != 1:
        raise SystemExit(f"expected one forward PTX in {dump}, found {ptx}")
    a.output.write_text(Path(ptx[0]).read_text())
    print(f"wrote {a.output}")


if __name__ == "__main__":
    main()
