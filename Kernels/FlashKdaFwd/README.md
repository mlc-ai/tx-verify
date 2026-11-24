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

[The decoding proof](Packed/Program.lean) establishes that the TxVerify decoder returns one
program with all 3,835 instructions from the exported PTX syntax. Each checked instruction
sequence is also a slice of that same program. [The entry proof](Packed/Entry.lean) starts
at instruction zero, binds the host parameters and traces the input-copy warp to its first
election at instruction 32.

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
terms in each dot product. At instruction 2,199 (numbering from zero), the compiler supplies
the same all-zero 32-bit register for all four accumulators. The
[register proof](Packed/MatrixRegs.lean) derives the bytes sent by each lane, the real dot
products returned by a matrix event, and their placement in the four destination registers.

[The workspace contract](Packed/Workspace.lean) specifies the six arrays supplied by the
preparation kernel, their byte addresses, and the values, logits, sequence offsets and initial
states read by the recurrence. Lean proves that multiplying these matrices gives the sequential
output on every live row and the outgoing state. The unused rows in a partial tile may contain
arbitrary finite values and update strengths.

[The shared-pointer proof](Packed/Pointer.lean) checks instructions 470 through 472. TxVerify's
default rule keeps a shared pointer symbolic and reports an unsupported operation on the first
right shift. The proof gives the generic shared window an explicit 256-byte-aligned base and
evaluates the shift, mask and XOR on its 64-bit address. The resulting pointer keeps the same
owner and has exactly the tensor-map byte offset. This local address interpretation is an
additional machine assumption.

[The projection proof](Packed/Projection.lean) checks all 112 instructions in the first
projection block. It tracks which of 32 shared loads supplies each of the 64 matrix products
and which prior result supplies its accumulator. [The matrix load proof](Packed/MatrixLoad.lean)
derives the 16-byte read of each thread from its address register and follows the bytes through
the warp exchange into the matrix operand layout. [The address calculation](Packed/ProjectionAddress.lean)
relates thread, feature and token indices to the shared bytes of the coefficient and state arrays.
The ordering of writes and reads across warps still has to be established.

[The bfloat16 proof](Packed/Bfloat.lean) checks both gate load and shift sequences. Moving a
16-bit stored pattern into the high half of a 32-bit register preserves its decoded value, also
for subnormal inputs. The separate real-arithmetic assumption for narrowing a computed FP32 value
to bfloat16 preserves its value in the ideal model.

[The output map](Packed/OutputMap.lean) relates a completed bulk copy of a 16-token tile to
the global address of each output byte. Distinct live sequence, head, token, feature and byte
coordinates have distinct addresses. [The partial-tile stores](Packed/Tail.lean) write eight
consecutive bfloat16 values, two bytes each, at the corresponding addresses. These theorems
give the global destination of each store. The [shared load and unpack proof](Packed/PartialOutput.lean)
follows the four 32-bit words in shared memory through the four register unpacks to the bytes
of all eight stores. The computation producing those words and their availability to the
store warp still need a proof.

The first block's input-copy warp consists of threads 128 through 159. At instruction 32,
all 32 threads elect a leader. The [execution proof](Packed/Prefix.lean) starts from the
decoded entry and establishes a consistent execution through that election for each possible
leader. All participants agree, every participant has arrived, and the elected thread
records its producer flag before reaching instruction 48. NVIDIA specifies a deterministic
choice for each member mask and leaves the particular lane unspecified.

CUTLASS checks the elected producer's lane number later, when acquiring a pipeline stage.
The compiler retains this check with source-line information disabled. If thread 129,
whose lane number is one, reaches the check as leader, it executes a breakpoint. Establishing
whether a valid execution reaches that breakpoint requires following the intervening
synchronization and control flow. [Local proof](Packed/Election.lean) ·
[FlashKDA producer selection](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/csrc/smxx/utils.cuh#L98-L109) ·
[CUTLASS producer check](https://github.com/NVIDIA/cutlass/blob/5c149f52a436782210263fb2f19b354443a61c6a/include/cutlass/pipeline/sm90_pipeline.hpp#L515-L526) ·
[PTX election semantics](https://docs.nvidia.com/cuda/parallel-thread-execution/#parallel-synchronization-and-communication-instructions-elect-sync).
