# FlashKDA forward verification

The 16-token block algorithm over the reals produces the same output at every live token and the
same final state as the Kimi Delta Attention (KDA) token recurrence, for any sequence length.
The production floating-point implementation has finite inputs for which this conclusion fails
even after rounding the real answer to the output format. On an NVIDIA GB300 the compiled
public entry also disagrees with the upstream mixed-precision reference on ordinary finite
inputs. A constructed 33-token call with default zero initial state illustrates both failures. At the last
token, the public kernel returns 1.0078125 and the upstream reference returns 1.015625.
Lean proves that the exact recurrence rounds to 1.015625 in bfloat16. A second constructed finite input
rules out every finite absolute or relative error tolerance over the full documented domain.
The mathematical answer is zero, while all observed outputs and requested states are NaN.
[Finite-tolerance proof](Audit/FiniteTolerance.lean) and [all eight launch modes](checks/gb300.json).

Sequence isolation also has a hardware counterexample when another sequence contains a NaN
(a floating-point value for an undefined numerical result). With two one-token sequences,
changing one 16-bit word of the second key changes the first output from 0.5 to NaN in both
public batch modes. All inputs of the first sequence stay finite and identical. This experiment
allows a nonfinite input in the second sequence. [Hardware record](checks/tail_isolation_gb300.json)

## What Lean checks

| Claim | Evidence |
| --- | --- |
| For the 33-token default-state input, the exact recurrence lies strictly between 259/256 and 65/64. Its correctly rounded bfloat16 output equals 65/64. On GB300 the public launch returns 129/128. | [Evaluation of all 33 tokens](Audit/StatelessForward.lean), [rigorous bounds and rounding](Audit/StatelessBounds.lean), and [hardware measurements](checks/stateless_output_gb300.json) |
| Two 8-by-8 triangular solves and their combination invert the 16-by-16 system over the reals. | [Register updates](Proof/Inverse.lean) and [block inverse](Proof/Block.lean) |
| The same block identity holds when query normalization and base-two exponentials retain the compiler's exact binary32 literals. The stored normalization epsilon is strictly less than the real decimal 0.000001. | [Frozen literals and resulting recurrence](Audit/Literals.lean) |
| Each 16-token block produces the sequential outputs and outgoing state, including a partially filled last block. | [Residual equations](Proof/Chunk.lean) and [block outputs](Algorithm.lean) |
| Composing blocks preserves those outputs and state for any sequence length. Each theorem instance covers one head and one value channel. | The `forward` theorem in [Sequence.lean](Sequence.lean) |
| Prefix counts allocate enough tiles and binary search assigns each live tile to its sequence, including repeated offsets for empty sequences. | [Batch indexing over natural numbers](Batches.lean) |
| The complete compiled tile-prefix entry decodes to the cached list of 173 typed instructions. Lean reduces the decoder on the imported entry to check equality. | [Prefix decode theorem](Audit/Prefix.lean) and [typed instruction data](Data/Prefix.lean) |
| In the packed prefix kernel all 31 nonzero threads return without a memory event for arbitrary host argument values. For ten concrete batches, every complete consistent execution leaves the expected prefix array in final memory and preserves every other byte. | [Thread runs](Audit/PrefixCases.lean), [connection to the memory model](Audit/PrefixMemory.lean), and [final memory theorem](Audit/PrefixResult.lean) |
| The prefix increment's signed 32-bit arithmetic agrees with the natural-number formula for any length whose sum with 15 fits in signed 32 bits and whose outgoing prefix fits in 32 bits. This covers independently narrowed offsets on either side of a 32-bit boundary. | [Word arithmetic](Proof/PrefixWords.lean) |
| The production state update rounds once. At the recorded ordinary operands the upstream helper rounds in binary64, then in binary32, producing adjacent states. | [Decoded instruction](Audit/CarryDecode.lean), [rounding rules](Audit/CarryRound.lean), and [fused result](Audit/StateUpdate.lean) |
| The adjacent states in the 17-token example round to distinct bfloat16 values for the next tile. | [Output rounding](Audit/OutputRound.lean) |
| The real recurrence cannot amplify an incoming state discrepancy in Euclidean norm. Initial state error plus the sum of local tile errors bounds the final error. | [State and output stability](Proof/Stability.lean) |
| Rounding the incoming state near one can give relative output error exactly one on a one-token input. | [Cancellation proof](Audit/Cancellation.lean) and [hardware results](checks/cancellation_gb300.json) |
| The public query in the second hardware probe is exactly representable as a 16-bit bfloat input. Its real answer lies in (511/512, 1], and its first single-precision square overflows. | [Finite inputs](Audit/FiniteInputs.lean) |
| Two statements in the imported fixed-length preparation entry decode to the fused square and approximate reciprocal square root used by normalization. Applied to the stated operands, they return positive infinity and positive zero respectively. | The `production_sites` theorem in [FullDecode.lean](Audit/FullDecode.lean) |
| A complete 32-thread warp with thread 1 within the warp elected satisfies TxVerify's election contract. | [Election.lean](Audit/Election.lean) |

The mathematical recurrence first decays the incoming state coordinatewise. It then adds the
normalized key times the gated difference between the value and the decayed state's prediction.
The output is the scaled inner product of the updated state with the normalized query.
The proofs use independent token and block definitions. They cover the seven elimination pivots
in each diagonal block and derive the residual solution from the resulting inverse.

## From the compiled program to a Lean statement

The [manifest](manifest.json) pins FlashKDA, CUTLASS (the NVIDIA kernel library), the compiler,
target architecture, generated entry names and input/output state variants. The checked-in PTX comes from the public Python extension build.
The [normalizer](checks/normalize_ptx.py) makes source paths in the compiler's debug file
records relative to the FlashKDA and CUDA roots and strips trailing whitespace. The manifest
records the raw and normalized SHA-256 fingerprints. After normalization the GB300 PTX differs
from the checked-in file only in its architecture directive, `sm_103a` versus `sm_100a`.

A fresh build from the pinned FlashKDA and CUTLASS sources reproduced the GB300 PTX and the
native GPU program byte for byte. CUDA's binary inspector found a single native image in
each loaded Python extension. Its SHA-256 matched the image used for the instruction audit.
The host libraries differed in the build identifier and three debug sections. All executable
host sections agreed. With runtime PTX compilation and the CUDA cache disabled, both builds
returned 1.0078125 on both GB300 devices for the 33-token input. The control returned 1.015625
in all four runs. [Build fingerprints](manifest.json) and [instruction-audit fingerprint](Data/NormMachine.lean).

1. [The Python parser](../../Tools/parse_ptx.py) reads the PTX syntax. The
   [exporter](../../Tools/export_lean.py) writes [Ptx.lean](Ptx.lean) with the source hash, the
   declarations, the instruction spellings and their operands. Python's import and the NVIDIA
   toolchain are external to the Lean proof.
2. [The Lean decoder](../../Core/Source/Decode.lean) resolves register declarations, labels,
   predicates, literal bit patterns and opcode modifiers into instructions. For example, the first
   query square in the fixed-length entry is `fma.rn.ftz.f32 %r101, %r69, %r69, 0f00000000`.
   Its destination is register number 303 and both inputs read register 271. The final operand
   encodes positive zero. [FullDecode.lean](Audit/FullDecode.lean) checks the two instructions at program
   counters 92 and 143 by reduction, using the declarations and resolved scopes of the whole entry.
3. TxVerify's [floating-point rule for one lane](../../Core/Thread/Float.lean) gives this
   instruction one fused multiply-add in single precision, round-to-nearest-even, with flushing
   of subnormal inputs and results. The local instruction theorem supplies the operand values.
   A proof from the public launch would additionally have to derive those values from the input
   buffers, track the other lanes and shared memory, and establish the final stores and progress.

For example, the generated Lean syntax node for that first query square is

```lean
.instruction none "fma.rn.ftz.f32" [(.register "%r101"), (.register "%r69"),
  (.register "%r69"), (.literal "0f00000000")]
```

Here `none` means the instruction has no predicate guarding execution. After decoding, its
two register reads use index 271 and the write uses index 303 in the function's register table.
For the input 2⁶⁴, which is representable in both bfloat16 and single precision, Lean proves
that this instruction produces positive infinity. The proof first multiplies and adds exactly,
then applies the instruction's rounding rule once. The source text, generated node, and
proof can be inspected side by side. [Original assembly](flash_kda_sm100a.ptx#L52424),
[generated syntax](Ptx.lean#L73039) and [floating-point proof](Audit/Normalize.lean).

Lean checks the compilation target and counts **41,607 static instructions in 17 entries** by traversing the imported syntax tree. [Import theorems](Audit/Import.lean).
The fixed-length and packed preparation kernels use different registers and instruction
indices for the first query square and both reciprocal square roots. Lean checks that their
three decoded operations have identical single-lane results for every supplied operand list.
[Packed and fixed-length sites](Audit/PackedNormalize.lean).

### How query and key bytes enter normalization

The host asks the NVIDIA Tensor Memory Accelerator to copy a 16-token by 128-channel
query tile and an equally sized key tile to shared memory. Each element occupies two bytes.
Lean checks the production copy instructions, their common coordinates and completion barrier,
the 4,096-byte displacement of the key, the wait, the memory fence, and both 16-byte
thread loads. For all 256 threads, both preparation kernels compute the same byte offset.
[Decoded instructions and address arithmetic](Audit/InputSites.lean).

For the host descriptor, the three axes are channel, token, and head. The global byte offset
of a channel is twice its index plus 256 times the head index plus the token index times
the number of heads times 256. In the TxVerify copy model Lean proves the correspondence for
every byte of every thread. Given a completed valid transfer and stable public input bytes,
each globally live slot writes the source byte and each slot past the allocation receives zero
fill. The proof takes the tile origin and the host descriptor as supplied. Establishing
completion, visibility to each consumer in an arbitrary concurrent execution, and deriving
all origins from the public launch remain separate obligations.
[Global addresses, shared offsets, and completion effects](Audit/InputTile.lean).

On GB300, a debugger at the CUDA driver boundary identified the two tensor maps by the
actual query and key pointers in a 17-token, two-head public call. The extents were
128 by 17 by 2, the outer byte strides were 512 and 256, and the box was 128 by 16 by 1,
with unit traversal and swizzle disabled. At normalization the debugger compared all 8,192
shared bytes against host copies of those public inputs for each of three tiles on head one.
The fixed-length tail had 15 zero-filled rows. With packed sequence lengths one and 16,
the first tile contained 15 rows from the next sequence; the second tile began at token one
and held all of its 16 rows. Downstream masking must therefore use the logical sequence end.
[Reproducible debugger comparison](checks/input_tile.py) and
[recorded map arguments and shared-byte hashes](checks/input_tile_gb300.json).

### What the tail mask clears

The two preparation kernels first compute one inverse key length per row. Later, threads
128 through 255 clear the raw keys for rows beyond the logical end of the sequence. Starting
at that clearing interval of the first tile of the first sequence, Lean follows the actual
conditional branches, register arithmetic and two-byte shared-memory stores through the
instruction where the threads rejoin. The fixed-length interval has 64 instructions and the
packed interval has 71. The certificate covers all 16 possible positive live lengths and all
128 writers in each mode. Each byte in an inactive key row has exactly one writer. These
writers preserve every byte in a live row. The entry theorem takes a successful full decode
and the stated starting registers and shared base as hypotheses.
[Decoder equality](Audit/TailDecode.lean), [thread paths](Audit/Tail.lean) and
[byte ownership](Audit/TailEntry.lean).

Every finite 16-bit bfloat16 word widens exactly by appending sixteen zero bits, including
both signed zeros and the smallest nonzero input. The conversion proof follows the source
register through the single-thread rule to the destination register.
[Widening proof](Audit/WidenFinite.lean).

For finite bfloat16 key words, the arithmetic proof covers every specified single-precision
square accumulation and four-stage cross-thread reduction, using the separate additions in
the inspected machine binary. Adding the compiled epsilon gives a positive normal argument
or positive infinity. Any inverse length allowed by the reciprocal-square-root contract then
leaves a cleared key at positive zero, including when the square sum overflows. This result
concerns the key normalization arithmetic. An end-to-end isolation theorem for finite
public calls would also have to cover the other operands, memory visibility and subsequent
matrix operations. [Floating-point range proof](Proof/NormRange.lean) and
[finite-key mask theorem](Audit/FiniteMask.lean).

For the hardware counterexample the query, key and value of each sequence start as unit
vectors. The gates use zero logits, the output scale is one, and the public call uses a zero
initial state. The only change is channel 7 (counting from zero) of the following sequence's
first key, from positive zero to a quiet NaN with bits `0x7fc1`. Lean evaluates the first
sequence's exact output at channel zero to 500000/1000001, which rounds to 0.5 in bfloat16.
On two GB300 devices the baseline output word is `0x3f00`, and the changed call produces
`0x7fff`. All 128 output coordinates and all 16,384 entries of the optional first final state
become NaN. The output also changes when the final state is omitted. Substituting the largest
finite bfloat16 word at the same location preserves every bit of the first output and state.

The debugger compared all 4,096 shared key bytes immediately before normalization and after
the tail clear. The foreign key word becomes zero, while its previously computed inverse
length is NaN. Multiplication by that inverse gives NaN on all 128 coordinates of the padded
row in the stored decayed keys. For every first sequence length from 1 through 32 in both
batch modes, the complete 16-token blocks keep their output bits. All live outputs of the
final partial block become NaN. The public output and intermediate memory are hardware
observations. Lean checks the arithmetic on the recorded words and proves that no function
of the unchanged first sequence alone can produce both observed outputs.
[Arithmetic and independence statement](Audit/TailIsolation.lean),
[reproducer](checks/tail_isolation.py) and [measurements](checks/tail_isolation_gb300.json).

The instruction audit decodes each entry in its own register and label environment. The prefix and both
preparation entries have a rule identifier for every instruction. Each of the 14 recurrence
entries contains 14 breakpoint instructions, yielding 196 occurrences with no execution rule.
A rule identifier itself only selects the semantics. For example, the derived
`positive_one_unspecified` theorem shows that the reciprocal square root of positive one has
no result under the current default approximate-instruction table. Its positive infinity case
does specify positive zero.

CUTLASS contains a device-debug check for an elected pipeline producer whose thread number is
nonzero modulo 32. NVIDIA specifies that the election selects a participating thread. The local
election theorem illustrates why the election rule alone cannot establish the breakpoint's
unreachability. Reaching it along a complete production execution would require a separate
control-flow proof. [CUTLASS check](https://github.com/NVIDIA/cutlass/blob/5c149f52a436782210263fb2f19b354443a61c6a/include/cutlass/pipeline/sm90_pipeline.hpp#L516-L526)
and [NVIDIA election semantics](https://docs.nvidia.com/cuda/parallel-thread-execution/#parallel-synchronization-and-communication-instructions-elect-sync).

### Packed prefix launch

The NVIDIA compiler unrolls the prefix loop eight sequences at a time, then handles four,
two and one. The [certified replay](Audit/PrefixRun.lean) starts in the empty register state,
uses TxVerify's instruction semantics, reads bytes from the caller's cumulative-length array,
and returns a proof of the thread's event trace. It uses the existing read-only assumption
for the compiled non-coherent loads. The [memory proof](Audit/PrefixMemory.lean) discharges
the replay's input observation from the initialized array and that assumption. The remaining
31 threads each produce a single exit event at instruction 172.

The checked sequence counts are 0 through 8 and 23. Sequence lengths repeat
`[0, 1, 15, 16, 17, 31, 32, 33]`. This exercises all eight possible remainder sizes, a second
pass through the eight-sequence loop, and empty sequences. For these launches, Lean proves
that every complete, consistent execution with a final memory writes the mathematical prefix
counts and preserves every byte outside the output array. Each checked thread admits a
completed trace. Global scheduling progress and existence of a complete consistent execution
are separate obligations. The [general theorem](Audit/PrefixResult.lean) also accepts a
successful checked replay at other sequence lengths and buffer addresses. On GB300, launching
the prefix entry directly from the compiled extension binary reproduced every checked prefix.
Both neighboring sentinel words and the input array retained their values.
[Driver probe](checks/prefix.py) and [hardware results](checks/prefix_gb300.json).

## Checking every returned word of a captured call

An independent Lean program reads the public input, output and final-state bit patterns.
It computes rational intervals containing the exact-real KDA outputs and final state. The
lower and upper ends of each reported maximum are rounded outward to integer millionths.
The checker uses the raw queries, keys, values, strength logits, gates, biases, per-head
log-gate parameter, scale, gate lower bound and optional entering state. It needs no
internal GPU register or workspace measurements. [Full-sequence soundness and maximum-error
proofs](Proof/CheckForward.lean) and [raw-word reader](checks/check_public.lean).

The inverse normalization length is bounded by checking rational squared inequalities.
For exponentials, the evaluator halves the argument, uses twelve Taylor terms and a proved
remainder, then repeatedly squares the resulting interval. It bounds each sigmoid and
the coordinatewise gate decay through these operations. For every token it encloses the
decayed state, key projection, delta update and scaled query readout. The theorem covers
every live output and every coordinate of the outgoing state at any sequence length.
[Rational operations and outward grid rounding](Proof/Enclosure.lean),
[nonlinear operations](Proof/EnclosureGates.lean) and [the public recurrence](Proof/PublicEnclosure.lean).

Two GB300 devices produced identical captures for a packed call with lengths 1 and 17 and
for the two corresponding fixed-length calls. The inputs have two heads, 128 key and
value channels, dense signed queries and keys, varying per-coordinate gates, nonconstant
strengths and a nonzero binary32 initial state. In both launch modes the gate lower bound
is −2.25. The Python call supplies 1/√128 in binary64. The public C++ entry takes a
binary32 scale, so the exact reference uses the received value, 11,863,283/134,217,728.
Lean checks the input words and this rounding. [Scalar conversion proof](Audit/OutputFormat.lean)
and [C++ entry](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/csrc/flash_kda.cpp#L34).
All 128 value channels are represented for each head and sequence. Four groups suffice because each group's entire
value history, initial row, observed output history and final row match bit for bit.
Both modes give the following maximum absolute error intervals, in millionths.

| Sequence length | Head | Maximum output error | Maximum final-state error |
| ---: | ---: | ---: | ---: |
| 1 | 0 | [21, 22] | [118, 119] |
| 1 | 1 | [26, 27] | [57, 58] |
| 17 | 0 | [19, 20] | [95, 96] |
| 17 | 1 | [38, 39] | [159, 160] |

Across both modes the reader covers **9,216 output elements and 131,072 final-state
elements**. The measured words are external inputs to the mathematical proof. The table
was obtained by running the Lean evaluator on these words. A separate 80-decimal-digit
calculation gives overall maxima of approximately 0.000038392614 and 0.000159087950.
The intervals quantify these particular invocations. [Raw capture](checks/public_enclosure_gb300.json.gz)
and [GPU reproducer](checks/public_enclosure.py).

From the TxVerify root, run the checker on a CPU with the pinned Lean toolchain:

```sh
kda=Kernels/FlashKdaFwd
gzip -dc "$kda/checks/public_enclosure_gb300.json.gz" > /tmp/flashkda-public.json
lake --wfail build Kernels.FlashKdaFwd.Proof.CheckForward
lake env lean --run "$kda/checks/check_public.lean" /tmp/flashkda-public.json
```

Captures record the Python scale and its binary32 value at the C++ interface. Given an
older capture with only the binary64 scale, the reader also checks the narrowed value
against the exact halfway points and the ties-to-even rule. The gate lower bound is a
binary64 argument at the C++ interface.

The optional final arguments set the number of fractional grid bits and the number of
argument halvings. The defaults are 48 and 4. An exponential endpoint outside the supported
range for that halving count, a reciprocal interval reaching zero, an invalid shape or a
nonfinite observed word makes the reader return an error. The mathematical soundness
proof applies whenever the activation checks succeed. A zero-length input carries its
initial state through unchanged. Omitting the initial state selects zero, and omitting the
final state leaves only the output comparison. To capture again with the pinned extension
installed, run `python Kernels/FlashKdaFwd/checks/public_enclosure.py /tmp/public.json.gz`.

## Absolute errors across blocks

For each value channel, reconstruct a candidate state from an entering state and one
candidate correction per token. Substituting a correction into its triangular equation
gives a scalar residual. Multiplying its absolute value by the normalized key length gives
the exact Euclidean error introduced by that correction in one state update. Add these
errors within the block, plus the distance from the reconstructed exit state to the
reported next state at each boundary. For normalized keys and queries, strengths in
[0, 1] and decay factors in [0, 1], the resulting sum bounds the final state error for
any sequence length. Multiplying the accumulated error by the absolute output scale and
adding the local output discrepancy bounds each live output. Both bounds accept arbitrary
candidate corrections. [Residual and accumulation theorems](Proof/Residual.lean).

For positive update strengths, the correction residuals also admit a sequence-wide
root-sum-of-squares bound. Write $r_t$ for a proposed correction minus the right-hand side
of its triangular equation and $b_t$ for its update strength. Adding $r_t/b_t$ to the
input value makes that correction exact within its block. A change $w_t$ in the value
can add at most $b_t w_t^2$ to squared state error per token. Consequently, if $D_0$ is
the Euclidean error in the entering state, the final state error is at most

$$
\sum_{\text{blocks}} \text{exit gap}
+ \sqrt{D_0^2 + \sum_{t} r_t^2 / b_t}.
$$

The exit gap is the distance between the reported next state and the state reconstructed
from that block's corrections. For a live output the two sums stop at the preceding block
boundary and the current token, respectively. Multiply this prefix bound by the absolute
scale and add the local readout discrepancy. The theorem covers arbitrary input lengths
and partially filled blocks. The real sigmoid of every finite strength logit is strictly
positive. Very small strengths can make this bound larger than the absolute-residual
bound. [Perturbation proof and the two forward bounds](Proof/ValuePerturbation.lean).

A 33-token GB300 run exercises two full blocks and a one-token tail. It has one head,
three active key coordinates, one active value channel, a nonzero FP32 initial state,
unit decay and update strength one half. Its raw keys and queries are signed permutations
of (125/128, 1/32, 1/32). Adding the normalization epsilon to their squared lengths gives
(15641/16000)² exactly. This permits independent rational verification of all live outputs.

| Quantity | Sum of absolute residuals and gaps | Gate-weighted square-sum bound | Independent recurrence certificate |
| --- | ---: | ---: | ---: |
| Maximum absolute error over 33 active-channel outputs | 0.020906 | 0.007576 | 0.002414 |
| Euclidean error of the active final state row | 0.020684 | 0.007354 | 0.000444 |

The buffer-based calculation reads the compiled preparation arrays, uses separate public
prefix calls for candidate states, and recomputes candidate corrections with GPU matrix
products. Lean decodes all 33 correction words and the three active components of all
four boundary states. It checks the squared residual and boundary budgets using rational
arithmetic and applies the general perturbation theorem to the captured outputs and final
state. [Buffer-based Lean certificate](Audit/WeightedSample.lean). The independent Lean certificate decodes every recorded output word and the
three active final-state words using TxVerify's floating-point formats. It checks
a dyadic approximation for each token against the real recurrence using rational
arithmetic, then applies nonexpansiveness. The other value channels start at zero and
receive zero values, and the hardware probe checks their outputs and states are zero.
A second launch packs the 33-token sequence after a distinct seven-token sequence. All output and final-state words matched the two separate launches, and Lean checks the active packed words against the same bounds. These numerical bounds concern the recorded launches. Source-to-binary compilation and
observation of the GPU buffers are external to Lean.
[Device record](checks/residual_sequence_gb300.json),
[measurement and rational calculation](checks/residual_sequence.py) and
[Lean certificate](Audit/ResidualSample.lean).

### Error in the triangular solve

For every 16-token block with normalized keys, decay factors in [0, 1] and strengths in
[0, 1], the sum of the squared entries of the ideal triangular inverse is at most 31.
The proof follows a unit impulse through the token recurrence and bounds the sum of the
squared corrections in each column. For a candidate solution, the Euclidean error is at most
√31 times the Euclidean norm of its equation residual. The same factor bounds the error of a
candidate inverse in Frobenius norm, the square root of the sum of its squared entries.
[Energy and residual proof](Proof/InverseStability.lean).

The fixed-length 33-token run above records all 256 bfloat16 inverse words per block. Lean
decodes the 768 finite words, forms the exact triangular coefficients from the raw keys, and
checks the matrix residual using rationals. The resulting Frobenius error bounds for the three
blocks are 0.023358, 0.022586 and zero, respectively. The last block contains one live token
and has the identity matrix as its inverse. [Raw words](Data/ResidualSample.lean) and
[certificate](Audit/InverseSample.lean).

The preparation kernel forms each strict-lower coefficient from two weighted keys. For
a causal pair their sum of absolute coordinate products is at most one, including when the
individual coordinates decay at different rates. If each operand has componentwise relative
error at most 1/256 and the remaining dot-product and gate arithmetic contributes at most
1/1024 absolute error per entry, the entire coefficient matrix differs from the ideal one by
less than 0.1 in Frobenius norm, assuming the upper triangle and diagonal are exact. Lean
separately proves the 1/256 relative bound for a nearest-even bfloat16 conversion throughout
the finite normal input range. The complete preparation path also computes normalization,
exponentials and matrix products, each of which has its own rounding behavior.
[Coefficient and inverse perturbation](Proof/Seed.lean) and [conversion proof](Proof/OperandRound.lean).

## A finite input rejected by both upstream comparisons

The upstream suite compares outputs to a mixed-precision PyTorch reference by elementwise
equality. Its other output check compares the root mean square of the error to the root mean
square of the recurrent reference plus 10⁻⁸. The limits for this ratio are 0.005 for fixed
lengths and 0.006 for packed sequences. The recurrent reference comes from Flash Linear
Attention v0.5.0. [Equality check](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/tests/test_fwd.py#L258-L261),
[fixed-length limit](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/tests/test_fwd.py#L359-L362),
[packed limit](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/tests/test_fwd.py#L420-L423)
and [comparison function](https://github.com/fla-org/flash-linear-attention/blob/3a9ce1c83a13994d824dbb3421e2989d330bb38b/fla/utils.py#L92-L111).

A 33-token input combines the zero-state, three-block rounding example in the first head with
the one-token cancellation example in the second head. All 128 value channels of the second
head receive 1024 at the first token. The packed run appends an independent all-zero sequence
of length one. Each call uses zero bfloat16 input state and a scale of one.

| Output on GB300 | Public kernel | Upstream PyTorch | Upstream recurrent reference |
| --- | ---: | ---: | ---: |
| First head, last token, first channel | 1.0078125 | 1.015625 | 1.0117254257202148 |
| Second head, first token, every channel | 0.26953125 | 0.26953125 | −0.308380126953125 |

All remaining output entries are zero. The upstream comparisons reject the output under both
launch modes. The full-tensor ratios are 1.7998746354 for fixed length and 1.7998745870
for packed sequences. The maximum absolute difference is 0.577911376953125. Starting from
the raw inputs and the recorded output words, a separate Lean proof gives a full-tensor
ratio above 1.75 relative to the exact real recurrence in each case. Twelve selected
unmodified upstream fixed-length tests at lengths 16, 17 and 37 passed on the same system.
[Reproduction](checks/upstream_criteria.py), [device record](checks/upstream_criteria_gb300.json)
and [tensor and recurrence proof](Audit/UpstreamCriteria.lean).

The references themselves disagree enough to make the two criteria mutually exclusive if
both are required on every input. On this input the unmodified recurrent-reference assertion
rejects the upstream PyTorch output directly, with an RMS ratio of 1.799875 in both launch
modes. Lean proves that any candidate equal to the PyTorch reference at every live coordinate
has a real-arithmetic RMS ratio above 1.75 against the recorded recurrent reference. The
maximum absolute difference exceeds 0.3, so the continuous-integration exceptions also
cannot admit the candidate. The original upstream tests choose their own sample inputs.
[Universal incompatibility for this pair of recorded references](Audit/UpstreamCriteria.lean#L140)
and [direct comparisons on GB300](checks/upstream_criteria_gb300.json).

## A gate-only change with unit-length inputs

With zero initial state, an exact one-token readout equals the scaled query-key inner
product times the update strength and the value. Every gate acts on the entering zero state.
Take four query coordinates (1/2, 1/2, 1/2, 1/2) and four key coordinates
(1/2, 1/2, −1/2, −1/2), with zeros elsewhere. Each vector has unit length and their
inner product is exactly zero. The exact output is therefore zero for every gate and
every scale. The experiment uses one head, unit values in all 128 channels, the upstream
scale 1/√128, a gate lower bound of −5, zero strength logit, and zero gate bias and log
parameter. Changing only the first raw gate word from zero to −1/2 changes all 128 outputs.
[Exact first state and output](Audit/Orthogonal.lean).

| Quantity | All gate coordinates zero | First gate coordinate −1/2 |
| --- | ---: | ---: |
| Real output, each channel | 0 | 0 |
| Public GB300 output, each channel | 0 | −201/4194304 |
| Upstream mixed-precision reference, each channel | 0 | −201/4194304 |
| Maximum absolute difference from the upstream recurrent reference | 6.392×10⁻¹⁰ | 4.79228×10⁻⁵ |
| RMS ratio against the recurrent reference | 0.02210 | 4686.32 |

Fixed-length and packed calls agree on both GB300 devices. Requesting a final state gives
the same outputs. In both calls every measured final-state row begins (1/4, 1/4, −1/4, −1/4)
and its other coordinates are zero. The upstream recurrent reference produces 112 zero
outputs and 16 outputs of about 6.392×10⁻¹⁰ in both calls. The upstream comparison accepts
the control by absolute error. The changed case exceeds the usual fixed-length and packed
ratio limits. In the upstream CI-specific comparison mode its small absolute error qualifies
for a warning. [Reproducer](checks/orthogonal_gate.py), [two-mode measurements and GPU register
words](checks/orthogonal_gate_gb300.json) and [upstream comparison code](https://github.com/fla-org/flash-linear-attention/blob/3a9ce1c83a13994d824dbb3421e2989d330bb38b/fla/utils.py#L92-L111).

In both compiled entries the debugger found four nonzero pairs among the two entire
shared-memory operand tiles. In the changed coordinate the bfloat16 operands are 219/32768 and 211/64.
In the control they are 119/32768 and 195/32. The other three pairs retain their words.
The exact dot of the four changed pairs is −201/2097152. It equals the observed binary32
accumulator and is exactly representable in bfloat16. Multiplication by the update
strength 1/2 gives the observed output, also exactly representable. Starting from the
recorded binary32 gate prefixes and inverse length, Lean bounds the true exponentials
using rational powers and verifies that every allowed approximation forces these same
rounded operands. For every independent choice of those allowed exponentials, the exact
four-term dot followed by the two measured-format conversions and the strength factor
gives the recorded output. [Operand and readout proof](Audit/GateWindow.lean) and
[contraction and final rounding](Audit/Orthogonal.lean).

The eight matrix instructions for output coordinate (0,0) each consume 16 query and key
coordinates. On both devices, in both launch modes, the debugger read the four source
lanes' registers immediately before each instruction and its accumulator immediately after.
In the changed case the first group contains all four nonzero products and yields
`0xb8c90000`. Each of the remaining seven groups has zero operands and preserves that word.
The control accumulator stays zero throughout. Lean verifies the row and column coordinates
from the warp fragment layout, the zero seed, both interleaved register chains, and the
first output conversion in each compiled preparation kernel. Every subset of the four
products is representable in binary32, so every binary reduction tree with arbitrary IEEE
rounding directions, permutations, and inserted zeros produces this same numerical result.
The observed matrix instruction agrees with this calculation at all eight stages.
[Decoded instruction chains and fragment layout](Audit/WarpDot.lean),
[order-independent arithmetic](Audit/OrthogonalOrder.lean) and
[per-instruction registers](checks/orthogonal_gate_gb300.json).

### A bound on the gated product

At each of eight paired sites in both preparation kernels, the compiled virtual assembly
uses opposite exponents for the query decay and key restoration. The query undergoes a
second binary32 multiplication for the output scale. Both operands then narrow to bfloat16.
For a gate prefix of magnitude at most 120, Lean bounds each approximate exponential
using the PTX limit of two units in the last place from the correctly rounded value.
For query and key at the same position, their product differs from one by at most one
part in a million. For different positions its relative error against the exact ratio
of exponentials has the same bound.
For up to 16 updates, a device gate scale in [−7.25, 0] and finite activations in
[0, 1025/1024] keep the rounded prefix in [−120, 0]. This bound accepts either a fused
update or separately rounded multiplication and addition. Later positions have a smaller or equal
computed prefix at every coordinate. [Eight instruction pairs in both
kernels](Audit/GateSites.lean), [prefix range](Proof/GateRange.lean),
[prefix order](Proof/GateOrder.lean), [exponential bounds](Proof/GatePair.lean) and [NVIDIA PTX 9.2 exponential specification](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html#floating-point-instructions-ex2).

Choose a query and any earlier or equal key position within the same 16-token tile.
Let `q` and `k` be their normalized coordinates entering the gate multiplications, `s`
the output scale, and `z[i]` and `w[i]` their computed gate prefixes at coordinate `i`.
The exact dot of the stored bfloat16 operands differs from
`s × sum(q[i] × k[i] × 2^(z[i] − w[i]))` by at most **0.00783 × |s| × sum(|q[i] × k[i]|)**.
At equal positions each exponential in the target is exactly one.
The bound includes both query products, the key product and both bfloat16 conversions.
It assumes round-to-nearest for the binary32 products, with zero or magnitudes in
[2⁻¹²⁰, 2¹²⁰] and zero or normal-range inputs to the bfloat16 conversions. It measures the
dot before matrix accumulation against the supplied normalized coordinates.
[Machine-rounding and dot theorem](Proof/GatedOperands.lean).

For a reduction with at most 129 rounding steps along any path, suppose each rounded
product incurs at most 2⁻²³ times its magnitude in error and each addition incurs at
most 2⁻²³ times the sum of the magnitudes of its two inputs. The same coefficient then
has absolute error at most **0.00785 × |s| × sum(|q[i] × k[i]|)** after accumulation.
After the final bfloat16 store the factor is **0.01179** if the conversion input is zero
or in the normal representable range. These are absolute bounds even under cancellation.
The reduction hypothesis is explicit. PTX specifies at least single-precision accumulation
and leaves the internal order and rounding unspecified. Extending the result to public
outputs requires quantifying actual reductions, normalization and the remaining state and
output operations on a specified input domain. [Accumulation and store proof](Proof/GateAccumulation.lean)
and [NVIDIA matrix instruction specification](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html#warp-level-matrix-instructions-mma).

## A one-token sign reversal

Use one token, one head, output scale one and the default zero starting state. Set the first four
query coordinates to `(1, 1, −1, −d)` and the first four key coordinates to `(1/4, 1/2, 3/4, d)`.
Set the first value coordinate to one and all other coordinates, logits, gate parameters and
the gate lower bound to zero. The unnormalized inner product is exactly −d². Normalization
divides by positive lengths, and the strength is one half. The first output is strictly negative
for positive d. [One-token derivation from the recurrence](Audit/OneToken.lean).

| Fourth coordinate magnitude d | Exact first output, approximately | Public extension and upstream reference on GB300 |
| --- | ---: | ---: |
| 0 | 0 exactly | 37/65536 |
| 1/32 | −0.00030115646 | 69/262144 |
| 1/64 | −0.00007532980 | 1/2048 |

The public entry and the upstream reference agree on each bfloat16 output bit. Reading the
compiled extension's intermediate buffer at d = 1/32 localizes the sign flip. The exact
inner product of the stored normalized vectors is already positive, 4403/8388608.
It rounds to 69/131072, the observed stored dot product. Multiplication by one half gives
the observed public output. Lean checks the buffer-word decoding and these rounding steps.
At d = 0 the nonzero device result rules out a universal error bound proportional only to
the absolute exact output. At d = 1/64 the error exceeds seven times its absolute exact
output. All input magnitudes are at most one. [Rounding and error proofs](Audit/OneTokenRound.lean),
[public and intermediate buffer probe](checks/one_token.py) and [GB300 results](checks/one_token_gb300.json).

The [normalization instruction proof](Audit/NormalizeWarp.lean) checks the consecutive 58
instructions at positions 80 through 137 in the compiled fixed-length preparation entry.
Eight coordinates from each of 16 lanes contribute once to each row's squared norm.
The proof checks register routing, shared-memory load offsets and the butterfly shuffles.
The [address and result-store proof](Audit/NormalizeIndex.lean) also checks the instructions
that fetch the thread identifier, compute the shared addresses and publish the two inverse norms.
It decodes the whole interval from instruction 76 through instruction 149.
The [reciprocal-square-root analysis](Audit/OneTokenNormalize.lean) shows that the measured
normalized coordinates at d = 1/32 are stable under any relative error up to 2⁻²² in the
reciprocal square roots, allowing an additional absolute perturbation of 2⁻²² in each product
before conversion to bfloat16. Under these hypotheses the [arithmetic pipeline proof](Audit/OneTokenPipeline.lean)
derives the positive final output without using measured buffer words as premises. Its dot
product is defined as an exact sum followed by bfloat16 rounding. The PTX 9.2 reciprocal
square root contract is tighter for positive normal inputs.
This arithmetic theorem assumes the prescribed approximation contract. The kernel-scoped rule described below now connects the root operation to the thread model. A complete execution still needs the shared-memory inputs and their ordering. [NVIDIA reciprocal square root](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html#floating-point-instructions-rsqrt).

### Square sums in the compiled binaries

For the one-token input with fourth coordinate magnitude 1/32, the eight fused updates in
each lane and the four cross-lane additions produce exactly 3 + 1/1024 for the query and
7/8 + 1/1024 for the key. Adding the compiled single-precision constant produces the
reciprocal-square-root operands `0x40401004` and `0x3f604011`.
[Certified fused updates and shuffles](Audit/NormSums.lean) and
[the two exact operand words](Audit/NormArguments.lean).

The PTX additions have no explicit rounding suffix. TxVerify deliberately leaves their
default semantics open to account for compiler contraction. The disassembly of both
`sm_100a` and `sm_103a` contains ten standalone single-precision additions in this
region. The [binary extraction](checks/norm_binary.py) checks that the two instruction
streams agree, checks both immediate fields, and records both binary hashes. Lean follows
the physical registers from the two shared loads through the sixteen fused square updates,
eight butterfly exchanges, ten additions and two inverse roots to their two shared stores.
Its [symbolic evaluation](Audit/NormMachine.lean) checks the expression trees and its
[numerical evaluation](Audit/NormArguments.lean) interprets the separate additions with
nearest-even rounding. It assumes the described shared-memory input and the first lane's
path. The NVIDIA disassembler and the small interpretation of these machine instructions
are additional trust boundaries. [NVIDIA single-precision addition](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html#floating-point-instructions-add).

The [debugger probe](checks/norm_trace.py) stopped the public GB300 kernel on thread zero
of the first block. The registers contained the two certified squared norms, then the two
certified regularized arguments, then inverse norms `0x3f13c710` and `0x3f88c2e9`.
At the final tensor-core conversion in thread 32 the accumulator was `0x3a099800`
(4403/8388608) and its packed bfloat16 result was `0x3a0a`. The call completed with public
output `0x398a`. [Captured register words](checks/norm_trace_gb300.json).

For each squared norm just four positive binary32 reciprocal-square-root results meet a
relative error bound of 2⁻²², which includes the tighter PTX bound. The query fields span
`0x3f13c70f` through `0x3f13c712`; the key fields span `0x3f88c2e8` through
`0x3f88c2eb`. Lean checks both neighbors outside each interval and uses monotonicity to
exclude all more distant fields. Every one of the sixteen combinations gives the same
bfloat16 vectors after binary32 multiplication. The only possibly inexact component is
three quarters of the key inverse norm. Its absolute error is at most 2⁻²⁵.
[All admissible words](Audit/NormRoots.lean) and [product rounding](Audit/NormProducts.lean).

PTX 9.2 gives the single-precision reciprocal square root a maximum relative error of
$2^{-22.9}$. The FlashKDA thread rule uses this exact bound for a positive normal register operand.
Lean proves that a normal binary32 result satisfying the bound exists for every such input.
It also proves that any result within the bound lies in the normal range, so output flushing
cannot change it. The rule permits every eligible result word as a possible successor state
of the thread. The positive-infinity, signed-zero, subnormal, negative and NaN cases fall
through to the original TxVerify semantics. [Format and existence proof](Proof/RootContract.lean),
[thread execution and fallback](Audit/RootExecution.lean) and
[NVIDIA PTX 9.2](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html#floating-point-instructions-rsqrt).

At the two fixed-length and two packed normalization sites, the exact bound leaves two
possible words per input in the one-token example. The query words are 0x3f13c710 and
0x3f13c711. The key words are 0x3f88c2e9 and 0x3f88c2ea. From the two source registers,
Lean checks the actual destination states. Feeding any of the four pairs into the verified
scalar arithmetic produces 69/262144, while the real one-token answer is negative.
[Decoded sites and destination-register proof](Audit/NormChoices.lean).

An independent single-instruction probe evaluated all 2,130,706,432 positive normal
binary32 inputs on each of two GB300 GPUs. The two sweeps produced identical extrema.
Across all inputs the maximum relative error is at most 124669 parts per trillion and
exceeds 124668 parts per trillion. The probe multiplies the exact integer significands
and tracks the extrema of the squared ratio on a common denominator of 2⁷². Lean verifies
the input partition, the interpretation of that integer, the two witness word pairs, and
the comparison with the PTX limit. Execution of the exhaustive GPU reduction and capture
of its extrema are external to Lean. [CUDA sweep](checks/root_sweep.cu),
[device record](checks/root_sweep_gb300.json) and [Lean certificate](Audit/RootSweep.lean).

The four nonzero products of the normalized bfloat16 vectors have sixteen distinct subsets.
Every subset sum is representable in binary32. The [dot-product proof](Audit/DotOrder.lean)
covers any addition tree that uses each product once, any number of zero terms, and all
four IEEE rounding directions at each product or addition. Every such tree gives the
accumulator observed on the device. The proof assumes that the matrix instruction supplies
the stated operands and covers these products once. The execution of the full matrix kernel,
shared-memory initialization and the second kernel's output store still require a separate
whole-program proof.

## Accuracy permitted by the output format

The public forward result uses bfloat16. For each of the following one-token calls,
Lean computes the exact recurrence and the smallest numerical error permitted by any
of the 65,536 output words. Both calls omit the initial state, use zero gates, logits,
bias and log-gate parameter, and set the gate lower bound to −1. All 128 value
channels are identical. The input tensor components are finite.

| Input | Exact output per channel | Closest finite output | Least relative error | Correctly rounded word |
| --- | --- | --- | ---: | --- |
| Query `(1,0,a,…)`, key `(0,1,a,…)`, value and scale 1, with `a=2⁻⁶⁷` and all other coordinates zero | a² / (2(1 + a² + 10⁻⁶)) | zero of either sign | 100% | positive zero |
| Unit query and key on the same coordinate, value 2¹²⁷ and scale 8 | 2¹²⁹ × 1,000,000 / 1,000,001 | (255/128) × 2¹²⁷ | 50.1952626953125% | positive infinity |

The first call has only zeros and normal input values of magnitude at most one. Its
positive exact output lies below half the smallest positive bfloat16 value. In the
second call every finite output misses the exact result by more than one plus half the
exact result. For a tensor consisting entirely of finite words, the root mean square
error divided by the exact reference root mean square plus 10⁻⁸ also exceeds one half.
Infinity and NaN have no finite numerical error under this criterion. The best
attainable errors follow from the output format alone. The exact recurrence rounded to
nearest-even gives the last column. [Proof over all output words](Audit/OutputFormat.lean)
and [public output type](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/csrc/flash_kda.cpp#L54).

Both GB300 devices returned the correctly rounded word in all 128 channels, in both
fixed-length and packed calls. To check the optimum independently on a CPU, run
`python Kernels/FlashKdaFwd/checks/output_format.py`. It enumerates the entire format
using exact fractions. Adding `--gpu` also checks the public calls. [Independent program](checks/output_format.py)
and [recorded outputs and exact minimum errors](checks/output_format_gb300.json).

## Numerical observations

The following two overflow probes use a single head, 16 tokens, 128 key and value coordinates, scale one, bfloat16
queries, keys, values, gates and strength logits, and FP32 input and output state. All inputs
are finite and both gate lower bounds are within the documented range. [Public API](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/README.md#kernel-api).

| Input | Real answer | Public extension on GB300 |
| --- | --- | --- |
| Log-gate parameter 100 and lower bound −5. Every other tensor input is zero. | All outputs and final-state entries are exactly zero. | All 2,048 outputs and 16,384 final-state entries are NaN. |
| First query coordinate 2⁶⁴ at every token. Initial state has only its first diagonal entry set to one. All other tensors and the lower bound are zero. | Each first output channel is greater than 511/512 and at most 1, which rounds to bfloat16 one. State equals its input. | All outputs are zero. All final-state entries equal their inputs. |

In the first case every measured output word is `0x7fff`, and every measured state word
is `0x7fffffff`. Lean checks that these words cannot satisfy any finite absolute or
relative tolerance against their zero real answers. This rules out a finite uniform
error guarantee on the documented input domain. Both GB300 devices produced the same
output word in all eight combinations of fixed or packed layout, supplied or omitted
zero initial state, and requested or omitted final state. All four calls requesting a state
returned the same state word at every coordinate. The experiment also checks that every
input tensor is finite. [Tolerance theorem](Audit/FiniteTolerance.lean).
The kernel forms the gate parameter exponential in single precision before
multiplication by a zero gate. In the second case the squared coordinate overflows before
normalization. The observed error exceeds 511/512 for every first-channel output in that case.
[Preparation source](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/csrc/smxx/fwd_kernel1.cuh#L260-L299)
and [raw probe results and controls](checks/gb300.json).

**First nonfinite gate on the zero-input probe.** At a log-gate parameter of 100, the
production preparation kernel multiplies 100 by its base-conversion constant. Lean gives
the binary32 result exactly as 4,727,423 / 32,768. The corresponding power of two exceeds
the largest finite binary32 value. On two GB300 devices, the exponential instruction
returned positive infinity in both fixed and packed calls. The subsequent multiply read
that infinity and positive zero. The debugger observed a NaN after the multiply, in the
register about to publish the first cumulative gate, and in shared memory after the store.
The zero-parameter control had exponential one and every public output and state entry zero.
[Raw register, shared-memory and public words](checks/gate_overflow_gb300.json) and
[debugger reproducer](checks/gate_overflow.py).

There is also an interval of 5,148,136 distinct positive finite binary32 parameters for
which the first multiplication itself already rounds to positive infinity. Its inclusive
word endpoints are `0x7f317218` and `0x7f7fffff`. For each parameter in that interval,
Lean follows the decoded register operands in both preparation entries. With the two zero
gate operands, a lower bound of −5, and the separate single-precision adds and multiplies
seen in the binary, the exponential's specified result on infinity and the subsequent
scalar instructions force a NaN in the first prefix register. The next decoded instruction
stores that register to shared memory. This proof starts at the scalar operands of a live
coordinate. The complete returned buffer contents are measured. The immediately preceding
parameter word `0x7f317217` still yields a finite first product, followed by an infinite
exponential on the same devices. The interval boundary therefore refers specifically to
overflow in the multiplication. In the exact recurrence, the natural-log gate is −5/2
and the state and outputs remain zero at any sequence length for every real parameter.
[Decoded data flow and overflow proof](Audit/GateOverflow.lean),
[real state and output](Audit/FiniteInputs.lean) and
[NVIDIA's base-two exponential special cases](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html#floating-point-instructions-ex2).

To reproduce the traces on the pinned GB300 build with CUDA-GDB available, run
`python Kernels/FlashKdaFwd/checks/gate_overflow.py` for the fixed-length call and add
`--packed` for the packed call. Each prints the same four records as the archived JSON.

For a one-token example at ordinary magnitudes, take the first two query coordinates equal
to one and the first state row equal to `(1 + 1/512, −1, 0, …)`. The key, value, gate and gate
lower bound are zero. The real output is `(1/512) / sqrt(2 + 0.000001)`, about 0.00138107.
The bfloat16 copy of the first state row is `(1, −1, 0, …)`. Both the kernel and the upstream
reference produce exactly zero and preserve the full-precision final state. The relative error
of the nonzero real output is one. All input magnitudes are at most 513/512.
[Real calculation and rounding](Audit/Cancellation.lean) and [hardware control](checks/cancellation_gb300.json).

### Default-state output after three tiles

The [33-token probe](checks/stateless_output.py) calls both public functions with the optional
initial and final states omitted. It uses one head, 128 coordinates, a scale of one, and zeros
for the gate bias and log parameter. Counting tokens from one, token 16 writes a unit key, a
value of three and a strength logit of 2⁻¹⁶. Token 32 has key (2⁻²⁸, 1, 0, …). Token 33 queries
the first coordinate. The unactivated gate is −40 except at token 32 where it is zero.
The gate lower bound is −825889/1048576. All unspecified query, key, value and logit entries
are zero.

| Source of the last token's first output | Result |
| --- | --- |
| Exact token recurrence | Strictly above the midpoint 259/256 and below 65/64 |
| Round the exact result once to nearest bfloat16 | 65/64 = 1.015625 |
| Unmodified upstream mixed-precision reference | 65/64 = 1.015625 |
| Compiled public extension on NVIDIA GB300 | 129/128 = 1.0078125 |

The [recurrence theorem](Audit/StatelessForward.lean) evaluates the same raw input from zero at
each step. The [rounding proof](Audit/StatelessBounds.lean) bounds the exponentials with rational
intervals. The [device probe](checks/stateless_output_gb300.json) observes the output through
the ordinary public entry. To explain the size of the discrepancy, the reference trace records
the second tile's first-coordinate multiply-add operands as binary32 words
`0x3fc00000`, `0x3f2caaaa`, and `0xa3020000`. The [stateless instruction](Audit/StatelessDecode.lean)
is a fused multiply-add. Applied to those operands, it yields a state just below the bfloat16
midpoint. The reference rounds to the midpoint and then up to the even neighbor.
[Instruction and reference rounding for this input](Audit/StatelessCarry.lean).
All other output elements are zero. Setting the small key component
at token 32 to zero makes the extension and reference agree on 1.015625.

### Following the last output through a public launch

The debugger runs the unmodified public extension on the 33-token default-state input.
The host probe reads all input tensor words before the launch and retains the wrapper's
preparation buffer when the call returns. The first two blocks have one nonzero key row
each. The last block has just one nonzero query coordinate. All three triangular inverses
are identities and all three query–key product blocks are zero. These observations reduce
the last output to a scalar calculation. The calculation takes its strengths from the
debugger and uses the preparation arrays to recompute the corrections and state updates.
[Source and workspace capture](checks/stateless_trace.py) and [raw record](checks/stateless_trace_gb300.json).

| Register or buffer | First block | Second block | Last block |
| --- | --- | --- | --- |
| State entering the fused update, binary32 | 0x00000000 | 0x3fc00000 | 0x3f817fff |
| Decay operand, binary32 | 0x3f800000 | 0x3f2caaaa | 0x3f800000 |
| Additive correction, binary32 | 0x3fc00000 | 0xa3020000 | 0x00000000 |
| State leaving the fused update, binary32 | 0x3fc00000 | 0x3f817fff | 0x3f817fff |
| State used by the next block, bfloat16 | 0x3fc0 | 0x3f81 | 0x3f81 |

In the last block the output accumulator is exactly 1.0078125. The store thread writes its
16-bit encoding at byte offset 8192 in the caller's output tensor. CUDA-GDB read the same
address immediately before and after that machine store. The value changed from the sentinel
0xc0e0 (−7) to 0x3f81 (1.0078125). The public API returned that same word.

Lean executes the two consecutive PTX carry instructions from their observed inputs. It also
proves that the decoded tail store, given its address and data registers, writes the two bytes
0x81 and 0x3f in that order for any aligned nonwrapping output allocation. A separate
calculation checks the recorded operands, the bfloat16 conversions, and the mathematically
correct output 1.015625 from the input tensor words. The debugger supplies execution order,
data transfers, and the actual register and memory observations. These theorems cover
selected instruction windows and the numerical path for this output.
[Instruction execution](Audit/TraceExecution.lean), [workspace calculation](Audit/TraceArithmetic.lean),
[register and publication checks](Audit/TraceObservations.lean) and [input tensor theorem](Audit/TraceInput.lean).

### Agreement with the upstream reference

The upstream tests require exact equality of outputs and final state for their reference cases.
That claim cannot be generalized to all finite inputs. The limited-precision reference helper
multiplies and adds in binary64 before conversion to binary32. Hardware executes one binary32
fused multiply-add. A small negative correction near a rounding midpoint makes them disagree.
[Upstream equality check](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/tests/test_fwd.py#L258-L261)
and [reference helper](https://github.com/MoonshotAI/FlashKDA/blob/b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2/tests/torch_ref.py#L56-L60).

| GB300 probe | Kernel | Upstream PyTorch reference |
| --- | --- | --- |
| One token, normal operands. First FP32 state entry after the update. | `0x3f900001` | `0x3f900002` |
| Packed sequence lengths 1, 0, 1. Each nonempty sequence has that same first state entry. | `0x3f900001` | `0x3f900002` |
| 17 tokens. The first channel at token 17 reads the stored bfloat16 state view. | `0x3f81` = 1.0078125 | `0x3f82` = 1.015625 |
| One token, initial FP32 state 2⁻¹²⁶ and decay one half. | Positive zero | `0x00400000` = 2⁻¹²⁷ |

The 17-token probe has one head and 128 coordinates. The only nonzero query is a unit vector at
token 17. The key at token 16 starts with `(2⁻²⁸, 1)` and all other keys and values are zero.
The unactivated gate is −40 except at token 16 where it is zero. The lower bound is the exact
binary number `-0x1.269620p-1`; the logits, gate parameter and bias are zero and the output scale
is one. The FP32 initial state has first diagonal entry `0x3facaaaa`, third diagonal entry one
and zeros elsewhere. The reference's first-tile multiply-add operands have binary32 encodings
`0x3facaaaa`, `0x3f400000`, and `0xa3020000`. Lean gives the fused result `0x3f817fff` and
the two-stage result `0x3f818000`. They land on opposite bfloat16 rounding outcomes. Setting the
tiny key coordinate to zero makes both implementations return `0x3f82`.
[Reproducible calls including controls](checks/state_rounding.py) and [bitwise outputs](checks/state_rounding_gb300.json).

The local machine theorems take the register operands as inputs. The public launches establish
end-to-end counterexamples on the tested architecture. A positive theorem for a specified
absolute error bound still requires bounding the numerical defect created inside each tile and
showing that execution and memory accesses implement the modeled tile. The stability theorem
allows those defects to be added across arbitrary sequence length with coefficient one.
[State error accumulation](Proof/Stability.lean).

## Reproduction

From the TxVerify root with the pinned Lean toolchain and dependencies installed:

```sh
kda=Kernels/FlashKdaFwd
python3 Tools/export_lean.py "$kda/flash_kda_sm100a.ptx" --namespace PTX.Generated.FlashKdaFwd -o /tmp/flashkda-ptx-syntax.lean
cmp /tmp/flashkda-ptx-syntax.lean "$kda/Ptx.lean"
lake --wfail build +Kernels.FlashKdaFwd.Audit.Axioms
python3 Tools/export_decoded.py --ptx-module Kernels.FlashKdaFwd.Ptx \
  --function PTX.Generated.FlashKdaFwd._Z28_flash_kda_build_tile_prefixPKliiPi \
  --globals PTX.Generated.FlashKdaFwd.module.globals --namespace FlashKda.Prefix.Decoded \
  -o "$kda/Data/Prefix.lean" --check
lake env lean --run "$kda/Coverage.lean"
```

With both compiled binary paths in `SM100_CUBIN` and `SM103_CUBIN`, compare their
disassembly against the Lean input using the same CUDA compiler tools. The register probe
runs on GB300 with the compiled extension and upstream reference on the Python path. It
uses CUDA-GDB source-line information from the pinned build.

```sh
python "$kda/checks/norm_binary.py" "$SM100_CUBIN" "$SM103_CUBIN" --check
python "$kda/checks/norm_trace.py"
nvcc -std=c++17 -O3 -arch=sm_103a "$kda/checks/root_sweep.cu" -o /tmp/flashkda-root-sweep
python "$kda/checks/root_sweep.py" --binary /tmp/flashkda-root-sweep | cmp - "$kda/checks/root_sweep_gb300.json"
python "$kda/checks/root_sweep.py" --record "$kda/checks/root_sweep_gb300.json" --lean-data | cmp - "$kda/Data/RootSweep.lean"
python "$kda/checks/stateless_trace.py" > /tmp/stateless_trace.json
cmp /tmp/stateless_trace.json "$kda/checks/stateless_trace_gb300.json"
python "$kda/checks/stateless_trace.py" --lean-data /tmp/stateless_trace.json | cmp - "$kda/Data/StatelessTrace.lean"
python "$kda/checks/residual_data.py" "$kda/checks/residual_sequence_gb300.json" | cmp - "$kda/Data/ResidualSample.lean"
```

The axiom audit reports the dependencies of the main theorems. The coverage command exits with a
failure after reporting the breakpoint counts, so missing semantics stays visible.

For fresh PTX and a hardware run, check out the FlashKDA commit in the manifest with its
submodules and use a Python environment with the matching PyTorch and CUDA compiler. Set
`FLASHKDA_SRC` and `TXVERIFY_SRC` to the absolute paths of those checkouts. Run in a fresh build
directory on a compatible system, choosing architecture `103a` for GB300 or `100a` for the
frozen target:

```sh
build_dir=$(mktemp -d)
mkdir -p "$build_dir/keep"
cd "$FLASHKDA_SRC"
export FLASH_KDA_CUDA_ARCHS=103a
export NVCC_APPEND_FLAGS="--keep --keep-dir $build_dir/keep"
python setup.py build_ext --build-lib "$build_dir/lib" --build-temp "$build_dir/obj"
python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/normalize_ptx.py" \
  "$build_dir/keep/fwd_launch.ptx" "$build_dir/normalized.ptx" \
  --flashkda "$FLASHKDA_SRC" --cuda "${CUDA_HOME:-/usr/local/cuda}"
sha256sum "$build_dir/keep/fwd_launch.ptx" "$build_dir/normalized.ptx"
export PYTHONPATH="$FLASHKDA_SRC:$FLASHKDA_SRC/tests:$build_dir/lib"
extension=$(python -c 'import pathlib, sys, torch, flash_kda_C
p = pathlib.Path(flash_kda_C.__file__).resolve()
assert p.parent.samefile(sys.argv[1])
print(p)' "$build_dir/lib")
mkdir -p "$build_dir/embedded"
(cd "$build_dir/embedded" && cuobjdump --extract-elf all "$extension" &&
  cmp "fwd_launch.sm_${FLASH_KDA_CUDA_ARCHS}.cubin" "$build_dir/keep/fwd_launch.cubin")
sha256sum "$build_dir/keep/fwd_launch.cubin"
python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/tail_isolation.py" --shared
python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/finite_inputs.py" --reference
python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/state_rounding.py"
python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/cancellation.py"
python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/one_token.py"
CUDA_DISABLE_PTX_JIT=1 CUDA_CACHE_DISABLE=1 python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/stateless_output.py"
python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/residual_sequence.py"
# FLA_SRC holds Flash Linear Attention v0.5.0.
PYTHONPATH="$FLA_SRC:$PYTHONPATH" python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/upstream_criteria.py"
PYTHONPATH="$FLA_SRC:$PYTHONPATH" python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/orthogonal_gate.py" --trace
python "$TXVERIFY_SRC/Kernels/FlashKdaFwd/checks/prefix.py" "$build_dir/keep/fwd_launch.cubin"
```
