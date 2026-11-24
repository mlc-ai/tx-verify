# Kimi Delta Attention backward

This verification targets Flash Linear Attention (FLA) at commit
[`7cecb923`](https://github.com/fla-org/flash-linear-attention/blob/7cecb9233b2331f725585d0f868a541f1a478388/fla/ops/kda/chunk.py#L155-L209).
FLA's public `chunk_kda` custom autograd function runs a chunked backward pass. The configuration
examined here enables query/key normalization, the bounded gate and the sigmoid on the raw
update logit. MoonshotAI's FlashKDA extension at the [forward pin](../FlashKdaFwd/manifest.json)
exports a forward entry.

## What Lean checks

- [Step.lean](Step.lean) derives a reverse step for the state decay, key prediction and update,
  and scaled query readout. The proof transposes the actual directional change of the state.
- [Sequence.lean](Sequence.lean) runs that step backwards through an arbitrary-length sequence
  with independent weights on every output and on the final state. Its theorem identifies
  the resulting input gradient with the derivative of the real block forward model. The initial
  state can be arbitrary. The zero-length case propagates the final-state weight to the input.
- [Activation.lean](Activation.lean) differentiates normalization with epsilon 0.000001, the
  sigmoid and the bounded per-coordinate gate. [Public.lean](Public.lean) composes these results
  for every value channel of a head. Shared parameters receive contributions from every use.
  The theorem gives the derivative along any differentiable path through the raw inputs.
- [FlaStages.lean](FlaStages.lean) checks the real-arithmetic identities for FLA's masked causal
  product, inverse triangular solve, chunk-state gradient propagation, reverse cumulative sum and
  stable evaluation of the bounded gate derivative. These correspond to the
  [chunk backward](https://github.com/fla-org/flash-linear-attention/blob/7cecb9233b2331f725585d0f868a541f1a478388/fla/ops/kda/chunk_bwd.py)
  and [gate backward](https://github.com/fla-org/flash-linear-attention/blob/7cecb9233b2331f725585d0f868a541f1a478388/fla/ops/kda/gate.py#L214-L245).

## Evidence for the compiled implementation

The [gradient check](checks/gradients.py) invokes FLA through PyTorch autograd on GB300 and
compares each of eight tensor gradients to a separate double-precision token recurrence.
It covers length 1 with only an output weight, length 17 with only a final-state weight,
length 65 with both weights, and packed lengths 17 and 65. The fixed random seeds produce
synthetic test tensors. The maximum observed ratio of the Euclidean error norm to the
reference gradient norm was 0.0481 (rounded up), for the log-gate parameter in the length-17
case. The script's 0.05 threshold is a regression check for these inputs.
[Device measurements](checks/gradients_gb300.json)

A separate [one-token probe](checks/saturation.py) uses unit query and key, zero initial state,
first value coordinate 2³⁰ and an update logit of 20. The public GPU backward returns zero
for the update-logit gradient. The independent real derivative is approximately 2.21314.
[Saturation.lean](Saturation.lean) proves this derivative exceeds two. The control sets the
logit to zero and the GPU returns the correctly rounded reference gradient.
[Device measurements](checks/saturation_gb300.json)

[Compiled.lean](Compiled.lean) resolves the registers of the FLA sigmoid backward
[specialization](beta_bwd_sm103a.ptx) captured from the public call. In one unrolled lane the
code adds one to the exponential, divides one by the result, subtracts the sigmoid from one
and multiplies. Lean checks that any positive exponential below 2⁻²⁴ rounds away in that
single-precision addition. The complete GPU launch and its final stores are measured.
A whole-program PTX proof of all kernels, numerical agreement on all inputs, and memory safety
and progress of the launch remain open.

## Reproduce

From TxVerify with the pinned FLA source checkout available on the Python path, a GB300 and
the PyTorch/Triton versions in the records, run:

```sh
kda=Kernels/FlashKdaBwd
lake --wfail build +Kernels.FlashKdaBwd.Public +Kernels.FlashKdaBwd.FlaStages \
  +Kernels.FlashKdaBwd.Compiled +Kernels.FlashKdaBwd.Saturation
python "$kda/checks/gradients.py"
python "$kda/checks/saturation.py" --ptx /tmp/fla-beta-bwd.ptx
cmp /tmp/fla-beta-bwd.ptx "$kda/beta_bwd_sm103a.ptx"
python3 Tools/export_lean.py "$kda/beta_bwd_sm103a.ptx" --namespace PTX.Generated.FlaKdaBwd \
  -o /tmp/fla-beta-bwd.lean
cmp /tmp/fla-beta-bwd.lean "$kda/Ptx.lean"
```
