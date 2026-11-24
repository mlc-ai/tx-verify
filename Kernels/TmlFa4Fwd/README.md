# tml-fa4 SM100 forward (CuTeDSL), paged KV with relative bias

The kernel is proved: [Theorem.lean](Theorem.lean) exports `correct` (safe, progress, terminates,
and the attention output and log-sum-exp of `Post`), `completed_execution` and
`realizable_result` for every launch that satisfies `Pre` ([Spec.lean](Spec.lean)), under the
kernel assumptions `Assumptions.all` ([Assumptions.lean](Assumptions.lean) and the files under
[Assumptions/](Assumptions), justified in [DECISIONS.md](DECISIONS.md)). `Theorem.lean` also
lists the readings of the specification the result depends on; the same list is kept in
[READINGS.md](READINGS.md).

## Verification target

- Source: vllm-project/tml-fa4 at revision `75765e76a9c2c012c1f6ecd64577eb646eb4d303`, with the
  vLLM Inkling 2 patch (PR 67325); the hashes are recorded in [DECISIONS.md](DECISIONS.md),
  section "Frozen program".
- [full_p16_s1.ptx](full_p16_s1.ptx): the device PTX emitted by CuTeDSL for `sm_100a`, kept
  byte for byte; [gen_ptx.py](gen_ptx.py) preserves the generator's compile arguments.
- Compile instance: BF16 Q, K, V and relative bias, FP32 output and LSE, head dimension 128,
  scale `128 ** -0.5`, causal full attention, page size 16, one split, unpacked GQA, a
  512-thread CTA. These values fix the PTX; they are not the proof scope.
- [Ptx.lean](Ptx.lean): generated from the PTX by `Tools/export_lean.py`.

## Scope of the proof

`Pre` admits any batch, any ragged query and key lengths with `qLength ≤ kLength`, any number of
KV heads and pages, and any page table within its stated bounds, together with the launch,
parameter, tensor-map, alignment and region-separation obligations listed in `Spec.lean`. Tiles
with one key block and tiles with any number of key blocks are both covered.

## Assumptions

`Assumptions.all` is the list below; each entry is stated in Lean with the instruction forms or
program positions it covers.

- `idealArith`: the BF16 QK and PV MMAs and the listed FP32 operations, maximums and comparisons
  are exact real operations.
- `approx`, `lg2`, `swExp2`: `ex2.approx`, `rcp.approx`, the LSE `lg2.approx` and the software
  `exp2` sequences are the exact functions on their finite inputs.
- `bf16Convert`: the Bias widening and the probability packing preserve their finite real values.
- `pollAgree`: at the listed poll branches, lanes of a warp spinning on one mbarrier get the same
  poll result.
- `commitOrder`: the selected Q-empty commit completes in order with the next commit of the same
  lane.
- `tcLdDataflow`: the listed `tcgen05.ld` without a wait are complete once their results are
  consumed.
- `delayedTmem`: the biased score loads have completed by the first probability store of their
  round.
- `inputReadOnly`: the kernel never writes its input tensors.

## How to check

```bash
Tools/build.sh Kernels.TmlFa4Fwd.Theorem Tests.Kernel.Statements
```

`Tests/Kernel/Statements.lean` checks that the three theorems use only the axioms `propext`,
`Classical.choice` and `Quot.sound`, and that their statements mention only reviewed
definitions. `Tools/build.sh` with no arguments builds every target with warnings as errors.
