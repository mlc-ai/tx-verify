# FlashKDA packed forward recurrence

The selected entry processes a batch of variable-length sequences at head dimension 128.
Each thread block reads one FP32 initial state, processes that sequence and head in tiles of
16 tokens, writes each live output row, and writes the final FP32 state. The preceding
preparation kernel supplies the workspace. Its implementation is outside this single-entry target.

The [PTX](packed_fp32_sm100a.ptx) contains only this entry and its shared memory declaration.
It has 3,835 instructions and no debug directives or comments. The [manifest](manifest.json)
identifies the compiler, source, specialization and file fingerprints. Assembling the selected
entry with the upstream assembler flags gives the same 72,064 machine-code bytes in its text
section as assembling the complete compiler module.

[Sequence.lean](Sequence.lean) proves the real block algorithm agrees with the independent
token recurrence at every output and the outgoing state for every length. The end-to-end
theorem for the compiled entry, from launch and initialized memory to the global writes,
is in progress.

## Reproduction

Build the public extension from the pinned source and its CUTLASS submodule with CUDA 13.2.51.
Use the upstream compiler command for `csrc/smxx/fwd_launch.cu` with the `sm_100a` target,
remove `-lineinfo`, and retain the PTX with `--keep`. The selector checks the function name,
the entire parsed body, the module directives and the shared memory declaration.

```sh
kda=Kernels/FlashKdaFwd
python3 "$kda/checks/select_packed.py" /path/to/fwd_launch.ptx /tmp/packed.ptx
cmp "$kda/packed_fp32_sm100a.ptx" /tmp/packed.ptx
ptxas -arch=sm_100a -m64 --register-usage-level=10 --warn-on-spills /tmp/packed.ptx -o /tmp/packed.cubin
python3 Tools/export_lean.py /tmp/packed.ptx --namespace PTX.Generated.FlashKdaPacked -o /tmp/packed.lean
cmp "$kda/Packed/Ptx.lean" /tmp/packed.lean
```

## Checked parts of the compiled entry

[The memory specification](Packed/Spec.lean) gives the required value at every output and final
state coordinate, including the outgoing state of an empty sequence. It also specifies the bytes
each launch must preserve. The query, key and decay coefficients come from the preceding stage.

[The update-gate proof](Packed/Activation.lean) evaluates both four-instruction gate sequences
with exact multiplication, base-two exponential, addition and reciprocal. Their recorded binary32
multiplier is exactly −12102203/8388608. At a logit of one this gives a strictly smaller result
than the textbook sigmoid. The upstream test reference uses the same multiplier as the kernel.

[The transfer sequences](Packed/Transfers.lean) identify all sixteen initial-state loads and
sixteen final-state stores in the parsed entry. [The issue rules](Packed/StateIssue.lean)
derive the actual copy events from operand registers, aligned parameter objects and valid state
descriptors. [The address proof](Packed/StateMap.lean) maps each byte of the 128-by-128 state
to one strip and connects completed copy effects to those bytes. [The shared-memory layout
proof](Packed/StateSwizzle.lean) establishes that the three bit operations used to address
a state element implement the same 32-byte swizzle as the tensor map.

[The warp matrix proof](Packed/Matrix.lean) follows the operand bytes contributed by all 32
threads to one 16-by-8 matrix multiply. For arbitrary real inputs in those registers, each
thread receives its four entries of the product plus the accumulator, including all sixteen
terms in each dot product. Instruction 2,199 (numbering from zero) uses this operation.
