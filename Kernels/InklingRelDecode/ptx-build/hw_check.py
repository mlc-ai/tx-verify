"""Hardware check of two builds of `_rel_verify_kernel` on random inputs (needs a B200).

usage: python hw_check.py MODULE_A.py MODULE_B.py [--timing]

MODULE_A and MODULE_B are the `kernel_module.py` slices that gen_ptx.py writes (`--keep-module`),
for example the build before and after a synchronization fix. The outputs of the two kernels
(`OPart` and `LsePart`) are compared bit for bit on random inputs, including splits with no key
block (`num_iters = 0`), and optionally timed. torch is taken from the environment; if it is
installed elsewhere, put its site-packages directory in EXTRA_SITE_PACKAGES. This script is a
check of the generated kernel, not a proof.
"""

import importlib.util
import os
import sys
import statistics

if os.environ.get("EXTRA_SITE_PACKAGES"):
    sys.path.append(os.environ["EXTRA_SITE_PACKAGES"])
os.environ.setdefault("TRITON_PTXAS_BLACKWELL_PATH", "ptxas")
import torch
import triton
from triton.experimental import gluon
from triton.experimental.gluon import language as gl

assert triton.__version__ == "3.8.0", triton.__version__


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    sys.modules[name] = m
    spec.loader.exec_module(m)
    return m


orig = load("km_a", sys.argv[1])
patched = load("km_b", sys.argv[2])

H, HKV, D, REL, REL_PAD, PAGE = 12, 2, 128, 1024, 1280, 64
CFG = dict(
    H=H,
    HKV=HKV,
    D=D,
    REL=REL,
    REL_PAD=REL_PAD,
    PAGE=PAGE,
    IS_LOCAL=False,
    BLOCK_M=64,
    BLOCK_N=128,
    FA_BLOCK=128,
    STAGES=3,
    FUSE_GATE=False,
    DRAFT=False,
    WINDOW=0,
)


def make_inputs(
    batch, seqlen_k, q_len_max, num_splits, seed, qscale=3.0, kmult=(1, 1, 1, 3, 1, 6, 1, 1)
):
    g = torch.Generator(device="cuda").manual_seed(seed)
    dev = "cuda"
    q_lens = torch.randint(1, q_len_max + 1, (batch,), generator=g, device=dev, dtype=torch.int32)
    q_lens[0] = q_len_max
    cu = torch.zeros(batch + 1, dtype=torch.int32, device=dev)
    cu[1:] = torch.cumsum(q_lens, 0)
    T = int(cu[-1])
    seqs = torch.full((batch,), seqlen_k, dtype=torch.int32, device=dev) - torch.randint(
        0, 128, (batch,), generator=g, device=dev, dtype=torch.int32
    )
    nblk = (seqlen_k + PAGE - 1) // PAGE
    num_blocks = batch * nblk
    perm = torch.randperm(num_blocks, generator=g, device=dev).to(torch.int32)
    block_table = perm.view(batch, nblk).contiguous()
    cache = torch.randn(num_blocks, PAGE, HKV, 2 * D, generator=g, device=dev, dtype=torch.float32)
    # key magnitude varies per 128-key block so the running max jumps in some iterations only
    mult = torch.tensor(kmult, device=dev, dtype=torch.float32)
    bm = mult[torch.randint(0, len(kmult), (num_blocks,), generator=g, device=dev)]
    cache[..., :D] *= bm.view(-1, 1, 1, 1)
    cache = cache.to(torch.bfloat16)
    q = (torch.randn(T, H, D, generator=g, device=dev) * qscale).to(torch.bfloat16)
    rel = (torch.randn(T, H, REL_PAD, generator=g, device=dev) * 2).to(torch.bfloat16)
    return dict(
        q=q,
        cache=cache,
        rel=rel,
        block_table=block_table,
        seqs=seqs,
        cu=cu,
        T=T,
        num_splits=num_splits,
        num_blocks=num_blocks,
    )


def launch(mod, inp, scale=1 / 128**0.5):
    q, cache, rel = inp["q"], inp["cache"], inp["rel"]
    T, ns = inp["T"], inp["num_splits"]
    batch = inp["seqs"].shape[0]
    slot_stride = HKV * 2 * D
    kv_rows = cache.as_strided((inp["num_blocks"] * PAGE, slot_stride), (slot_stride, 1))
    layout = gl.NVMMASharedLayout.get_default_for([64, D], gl.bfloat16)
    desc = gluon.nvidia.hopper.TensorDescriptor.from_tensor(kv_rows, [64, D], layout)
    o_part = torch.zeros(ns, T, H, D, dtype=torch.float32, device="cuda")
    lse = torch.zeros(ns, T, H, dtype=torch.float32, device="cuda")
    gate = torch.zeros(T, H, dtype=torch.bfloat16, device="cuda")
    sinks = torch.zeros(T, H, dtype=torch.float32, device="cuda")
    out = torch.zeros(T, H * D, dtype=torch.bfloat16, device="cuda")
    bt = inp["block_table"]

    def run():
        mod._rel_verify_kernel[(ns, HKV, batch)](
            q,
            desc,
            rel,
            bt,
            inp["seqs"],
            inp["cu"],
            o_part,
            lse,
            gate,
            sinks,
            out,
            scale,
            q.stride(0),
            rel.stride(0),
            bt.stride(0),
            gate.stride(0),
            sinks.stride(0),
            slot_stride // slot_stride * PAGE,
            0,
            2 * D,
            ns,
            T,
            **CFG,
            num_warps=4,
            launch_pdl=True,
        )

    return run, o_part, lse


def timeit(run, n=300, warm=30):
    for _ in range(warm):
        run()
    torch.cuda.synchronize()
    ts = []
    for _ in range(n):
        a = torch.cuda.Event(enable_timing=True)
        b = torch.cuda.Event(enable_timing=True)
        a.record()
        run()
        b.record()
        b.synchronize()
        ts.append(a.elapsed_time(b) * 1000)
    return statistics.median(ts), min(ts)


if __name__ == "__main__":
    print("device", torch.cuda.get_device_name(), "triton", triton.__version__)
    worst = {"o_abs": 0.0, "o_rel": 0.0, "l_abs": 0.0, "l_rel": 0.0}
    cases = [
        (4, 1024, 10, 2),
        (8, 2048, 10, 4),
        (8, 4096, 7, 8),
        (3, 1500, 10, 2),
        (8, 16384, 10, 9),
        (4, 256, 10, 9),
        (3, 128, 10, 4),
        (5, 640, 10, 9),
    ]  # the last three: splits with no key block
    for ci, (batch, sk, ql, ns) in enumerate(cases):
        for seed in range(3):
            inp = make_inputs(batch, sk, ql, ns, seed=100 * ci + seed)
            ro, oo, lo = launch(orig, inp)
            rp, op, lp = launch(patched, inp)
            ro()
            rp()
            torch.cuda.synchronize()
            assert torch.isfinite(oo).all() and torch.isfinite(op).all(), "non-finite output"
            assert oo.abs().max() > 0
            d = (oo - op).abs()
            dl = (lo - lp).abs()
            rel = d.max() / oo.abs().max()
            lrel = dl.max() / lo.abs().max()
            bit = bool(torch.equal(oo, op) and torch.equal(lo, lp))
            print(
                f"case batch={batch} seqlen_k={sk} q_len<= {ql} splits={ns} iters~{(sk // 128) // ns} seed={seed} "
                f"|O|max={oo.abs().max():.3f} O maxabs={d.max():.3e} (rel to |O|max {rel:.3e}) "
                f"Lse maxabs={dl.max():.3e} (rel {lrel:.3e}) bitwise_equal={bit}"
            )
            worst["o_abs"] = max(worst["o_abs"], d.max().item())
            worst["l_abs"] = max(worst["l_abs"], dl.max().item())
    print("worst", worst)
    if "--timing" not in sys.argv:
        sys.exit(0 if worst["o_abs"] == 0.0 and worst["l_abs"] == 0.0 else 1)
    for batch, sk, ql, ns in [(8, 16384, 10, 9), (16, 8192, 10, 9), (8, 4096, 4, 9)]:
        inp = make_inputs(batch, sk, ql, ns, seed=7)
        ro, *_ = launch(orig, inp)
        rp, *_ = launch(patched, inp)
        res = []
        for rep in range(3):  # alternate to cancel clock drift
            res.append((timeit(ro), timeit(rp)))
        mo = statistics.median(r[0][0] for r in res)
        mp = statistics.median(r[1][0] for r in res)
        print(
            f"timing batch={batch} seqlen_k={sk} q_len<={ql} splits={ns}: A median {mo:.2f} us, B median {mp:.2f} us, ratio {mp / mo:.4f}; "
            f"per-round medians A {[round(r[0][0], 2) for r in res]} B {[round(r[1][0], 2) for r in res]}"
        )
