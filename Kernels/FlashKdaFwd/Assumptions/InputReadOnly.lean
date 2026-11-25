-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Data.Decoded
public import Core.Assembly.Execution
public import Assumption.ClusterScopeMbar

@[expose] public section

/-!
# The packed-offsets array is read-only (kernel-local assumption)

The kernel reads the host array `cu_seqlens` (`N + 1` 64-bit entries: entry `i` is the global
index of the first token of sequence `i`) with plain `ld.global.b64` loads. A plain `ld.global`
at one of these 21 loads returns the launch content of the bytes it reads, and a write of a byte
of that array by any operation of the execution is undefined behaviour. Modelled on
`Assumption/NcReadOnly.lean` (ASM-NC) and on the same assumption of the Inkling kernel
(`Kernels/InklingRelDecode/Assumptions/InputReadOnly.lean`), for plain loads: the model's memory
consistency rules stay in force for these reads (they have reads-from sources and take part in
races); the assumption only removes the executions in which such a read returns anything but the
launch content.

The 21 sites are every `ld.global` of the frozen program (instruction indices of
`packed_fp32_sm100a.ptx`, counted from zero):

* 115, 116: `cu_seqlens[seq]` and `cu_seqlens[seq + 1]`, the first token and the end of the
  CTA's sequence;
* 126 to 291: the loop that adds up the tile counts of the sequences before this one (the
  workspace slot of the sequence's first tile), unrolled by eight, four and two.

The program has no other load of global memory and no `ld.global.nc`.
-/

namespace PTX.Kernels.FlashKdaFwd.Assumptions
open PTX PTX.Assumption

/-- The name of the kernel's `cu_seqlens` parameter (parameter 15, a 64-bit pointer). -/
def offsetsParam : String := Decoded.kernel.name ++ "_param_15"

/-- The instruction indices of the 21 `ld.global.b64` instructions of the program. -/
def inputReadSites : List Nat :=
  [115, 116, 126, 131, 141, 150, 159, 168, 177, 186, 196, 215, 216, 226, 235, 245, 260, 264, 265,
   276, 291]

/-- `l` is a byte of the packed-offsets array of the launch: a global byte among the
`8 * (N + 1)` bytes at the address the launch passes as `cu_seqlens`, where `N` is the first
extent of the grid (the kernel runs one CTA per sequence and head, `seq = %ctaid.x`). -/
def OffsetByte (L : Launch) (l : Loc) : Prop :=
  l.space = .global ∧ l.cta = 0 ∧ ∃ base, L.params offsetsParam = some base ∧
    base.toNat ≤ l.addr ∧ l.addr < base.toNat + 8 * (L.nctaid.x + 1)

/-- **The packed-offsets array is read-only** (kernel-local).

* `wf` (removes executions): a plain read (`.rd`) at one of `inputReadSites` returns, at every
  byte of the offsets array (`OffsetByte`) whose launch content is known (`mem0` gives a
  byte), that byte. A read at one of these sites of any other byte is not constrained (the
  proof shows there is none: the addresses are the parameter plus `8 * i` with `i` at most the
  CTA's sequence index plus one, and depend on no loaded value).
* `ub` (only stricter, and independent of the reads): undefined if an issued ordinary or
  asynchronous operation of the execution writes a byte of the offsets array (`OffsetByte`).

Why `wf` cannot hide a kernel that writes the array. Suppose a run on the hardware writes a byte
of it, and take the first such write in real time. Before it no write has touched the array, so
every read at a site before it returned the launch content. The prefix of the run up to and
including that write satisfies `wf` and contains a write of an array byte, so it has `ub`. The
safety theorem (`Correct.safe`: every consistent execution is not `Unsafe`) covers that prefix:
`Consistent.thr` asks only for a finite run of each thread, with no completion requirement. So
the theorem would fail; the assumption cannot mask such a kernel. This is why `ub` does not
mention the reads.

Why the kernel needs it. The addresses of the kernel's global writes are computed from the
loaded entries: the coordinates of every TMA store of a full output tile, and the addresses of
the `st.global.b16` stores of a partial last tile. Nothing orders the events of two CTAs of this
kernel, and Core has no no-thin-air clause, so the model's memory clauses alone do not exclude
an execution in which two CTAs each load an entry from the other's output store (a value cycle
through global memory). With the assumption a read at these sites returns the launch content, so
no such cycle exists, and the proof shows that no operation writes the array. -/
def inputReadOnly : Assumption where
  name := "flash-kda-offsets-read-only"
  statement := s!"The kernel never writes the packed-offsets array cu_seqlens (the N + 1 64-bit \
    entries at the address passed as parameter 15, N being the grid's first extent): a plain \
    ld.global at exactly these sites: {siteText inputReadSites} returns the launch content of \
    every byte of that array whose launch content is known, and writing a byte of this array, \
    by any operation of the execution, whether or not a read reads it, is undefined. This is a \
    kernel-local reading of the frozen PTX, whose global writes all have addresses computed \
    from the loaded entries; without it the model does not exclude a value cycle through \
    global memory between two CTAs."
  wf L mem0 X := ∀ e pc a bs, X.get e = some ⟨pc, .rd a bs⟩ → inputReadSites.contains pc →
    ∀ k < a.size, OffsetByte L (a.loc.at k) →
      ∀ c, mem0 (a.loc.at k) = some (some c) → bs[k]? = some (some c)
  ub L _ X := ∃ w a' l, X.Intent w a' true ∧ a'.Covers l ∧ OffsetByte L l

end PTX.Kernels.FlashKdaFwd.Assumptions
