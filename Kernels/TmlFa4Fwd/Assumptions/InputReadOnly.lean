-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Core.Assembly.Execution
public import Core.Assumption.ClusterScopeMbar

@[expose] public section

/-!
# The kernel's metadata inputs are read-only (kernel-local assumption)

A plain `ld.global` read at one of the 37 global loads of the frozen PTX returns the launch
content of the input bytes it reads, and a write of a byte of an input array by any operation of
the execution is undefined behaviour. Modelled on `Core/Assumption/NcReadOnly.lean` (ASM-NC), for
plain loads: the model's memory consistency rules stay in force for these reads (they have
reads-from sources and take part in races); the assumption only removes the executions in which
such a read returns anything but the launch content of an input byte.

The 37 sites (pc, PTX line of `full_p16_s1.ptx`), all `ld.global.b32`:

* 30 loads of `cu_seqlens_q` (parameters 5 and 24): pc 186, 245, 381, 382, 1750, 1805, 1940,
  1999, 2112, 2113, 2653, 2707, 2776, 2835, 2953, 2954, 2989, 3043, 3110, 3169, 3369, 3370, 7621,
  7677, 7761, 7821, 7955, 7956, 9089, 9144 (PTX 258, 320, 462, 463, 1975, 2033, 2216, 2278, 2397,
  2398, 3139, 3196, 3272, 3334, 3458, 3459, 3508, 3565, 3638, 3700, 3906, 3907, 8442, 8501, 8601,
  8664, 8804, 8805, 9973, 10031);
* 4 loads of the used key lengths (parameter 6): pc 385, 2116, 3373, 7959 (PTX 466, 2401,
  3910, 8808);
* 3 loads of the page table (parameter 7): pc 503, 946, 1416 (PTX 590, 1096, 1621).

The program has no other load of global memory and no generic (space-less) load
(`Proof/InputRead.lean`, `kernel_nonShared_reads` and `kernel_sites_global`).

The input arrays are `Params.inputRegions` of a parameter set the launch satisfies (`Pre`): the
Q tensor, the bias tensor, the K and V caches, `cu_seqlens_q`, the used key lengths and the page
table. The output arrays O and LSE are fixed by the launch, and `Pre` keeps them apart from the
input arrays (`Pre.separate`).
-/

namespace PTX.Kernels.TmlFa4Fwd.Assumptions
open PTX PTX.Assumption

/-- The pcs of the 37 `ld.global` instructions of the program. -/
def inputReadSites : List Nat :=
  [186, 245, 381, 382, 385, 503, 946, 1416, 1750, 1805, 1940, 1999, 2112, 2113, 2116, 2653, 2707,
   2776, 2835, 2953, 2954, 2989, 3043, 3110, 3169, 3369, 3370, 3373, 7621, 7677, 7761, 7821, 7955,
   7956, 7959, 9089, 9144]

/-- A byte of an input array of some parameter set the launch satisfies. -/
def InputByte (L : Launch) (mem0 : Mem0) (l : Loc) : Prop :=
  ∃ P, Pre P L mem0 ∧ ∃ r ∈ P.inputRegions, r.Contains l

/-- **The kernel's metadata inputs are read-only** (kernel-local; approved by the user as the
standing resolution for a value cycle through plain loads of inputs, 2026-11-19).

* `wf` (removes executions): a plain read (`.rd`) at one of `inputReadSites` returns, at every
  byte of an input array whose launch content is known (`mem0` gives a byte), that byte.
* `ub` (only stricter, and independent of the reads): undefined if an issued ordinary or
  asynchronous operation of the execution writes a byte of an input array, that is a byte that
  `Params.inputRegions` names for some `P` with `Pre P L mem0`. The O and LSE regions are fixed
  by the launch (the head count of `param_17`, the O and Q tensor maps of `param_10` and
  `param_9`, the LSE base and stride of `param_4`; `Pre.outputs_pinned`), so every such `P`
  keeps them apart from its inputs (`Pre.separate`).

Why `wf` cannot hide a kernel that writes its inputs. Suppose a run on the hardware writes an
input byte, and take the first such write in real time. Before it no write has touched an input
byte, so every read at a site before it returned the launch content of the input bytes it read.
The prefix of the run up to and including that write satisfies `wf` and contains a write of an
input byte, so it has `ub`. The safety theorem (`Correct.safe`: every consistent execution is not
`Unsafe`) covers that prefix: `Consistent.thr` asks only `Produces K A L g (X.tr g)`, a finite
run with no completion requirement, and `Maximal`, `Complete` are used only by progress and the
result. So the theorem would fail; the assumption cannot mask such a kernel. Premise, as for
every safety claim: the real-time prefix is a consistent execution of the model. This is why
`ub` does not mention the reads: with `NcReadOnly`'s form (a site read of a byte that some
operation writes) a run whose read of the written byte comes after the write would have no `ub`
on the prefix through the write, and the full run would be removed by `wf`. The constraint is
limited to input bytes, the bytes `ub` protects: a site read of any other byte keeps the
model's reads-from rules alone.

Why the kernel needs it: the output stores and the LSE stores have addresses computed from the
loaded `cu_seqlens_q` words, so an execution in which two CTAs each load such a word from the
other's output store (a value cycle across CTAs) is not excluded by the model's clauses: Core has
no no-thin-air clause, and nothing orders events of two CTAs of this kernel. With the assumption
a read at these sites returns the launch content, so no such cycle exists.

Evidence: the kernel treats these arrays as read-only inputs, which is the contract of a CUDA
`const __restrict__` pointer argument: the object it points to is not modified while the kernel
runs. The frozen PTX writes global memory only by the LSE stores and the O tensor stores. -/
def inputReadOnly : Assumption where
  name := "tml-fa4-fwd-input-read-only"
  statement := s!"The kernel never writes its input tensors (Q, the sheared bias, the K and V \
    caches, cu_seqlens_q, the used key lengths and the page table): a plain ld.global at \
    exactly these sites: {siteText inputReadSites} returns the launch content of every byte of \
    these input arrays whose launch content is known, and writing a byte of these input \
    arrays, by any operation of the execution, whether or not a read reads it, is undefined. \
    This is the contract of a CUDA const __restrict__ input, and the frozen PTX writes global \
    memory only by its O and LSE stores; without this the model does not exclude a value \
    cycle through global memory between two CTAs."
  wf L mem0 X := ∀ e pc a bs, X.get e = some ⟨pc, .rd a bs⟩ → inputReadSites.contains pc →
    ∀ k < a.size, InputByte L mem0 (a.loc.at k) →
      ∀ c, mem0 (a.loc.at k) = some (some c) → bs[k]? = some (some c)
  ub L mem0 X := ∃ w a' l, X.Intent w a' true ∧ a'.Covers l ∧ InputByte L mem0 l

end PTX.Kernels.TmlFa4Fwd.Assumptions
