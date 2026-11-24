-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Core.Assembly.Execution
public import Assumption.ClusterScopeMbar

@[expose] public section

/-!
# The kernel's input tensors are read-only (kernel-local assumption)

A plain `ld.global` read at one of the 203 global loads of the frozen PTX returns the launch
content of the bytes it reads, and a write of a byte of an input array by any operation of the
execution is undefined behaviour. Modelled on `Assumption/NcReadOnly.lean` (ASM-NC), for
plain loads: the model's memory consistency rules stay in force for these reads (they have
reads-from sources and take part in races); the assumption only removes the executions in which
such a read returns anything but the launch content.

The 203 sites (pc, PTX line of `rel_verify_sm100a.ptx`):

* 3 `ld.global.b32` of the prologue's request words: pc 34, 37 (PTX 107, 117: `cu_seqlens_q` at
  the request and the next one) and pc 41 (PTX 128: `seq_lens`);
* 6 `ld.global.b32` of the prologue's block-table words: pc 197, 220, 241, 262, 283, 304
  (PTX 400, 441, 490, 527, 575, 612);
* 64 predicated `ld.global.b16` of the query tile: pc 388 to 514, step 2 (PTX 719 to 1097,
  step 6);
* 128 predicated `ld.global.b16` of the bias (`Rel`) tensor: pc 680 to 806 and 1124 to 1250,
  step 2 (PTX 1325 to 1703 and 2050 to 2428, step 6);
* 2 `ld.global.b32` of the loader's block-table words: pc 2382, 2399 (PTX 4301, 4341).

The program has no other load of global memory, no generic (space-less) load and no
`ld.global.nc` (`Audit/AssumptionSites.lean`, `inputRead_sites`).
-/

namespace PTX.Kernels.InklingRelDecode.Assumptions
open PTX PTX.Assumption

/-- The pcs of the 203 `ld.global` instructions of the program. -/
def inputReadSites : List Nat :=
  [34, 37, 41, 197, 220, 241, 262, 283, 304, 388, 390, 392, 394, 396, 398, 400, 402, 404, 406, 408,
   410, 412, 414, 416, 418, 420, 422, 424, 426, 428, 430, 432, 434, 436, 438, 440, 442, 444, 446,
   448, 450, 452, 454, 456, 458, 460, 462, 464, 466, 468, 470, 472, 474, 476, 478, 480, 482, 484,
   486, 488, 490, 492, 494, 496, 498, 500, 502, 504, 506, 508, 510, 512, 514, 680, 682, 684, 686,
   688, 690, 692, 694, 696, 698, 700, 702, 704, 706, 708, 710, 712, 714, 716, 718, 720, 722, 724,
   726, 728, 730, 732, 734, 736, 738, 740, 742, 744, 746, 748, 750, 752, 754, 756, 758, 760, 762,
   764, 766, 768, 770, 772, 774, 776, 778, 780, 782, 784, 786, 788, 790, 792, 794, 796, 798, 800,
   802, 804, 806, 1124, 1126, 1128, 1130, 1132, 1134, 1136, 1138, 1140, 1142, 1144, 1146, 1148,
   1150, 1152, 1154, 1156, 1158, 1160, 1162, 1164, 1166, 1168, 1170, 1172, 1174, 1176, 1178, 1180,
   1182, 1184, 1186, 1188, 1190, 1192, 1194, 1196, 1198, 1200, 1202, 1204, 1206, 1208, 1210, 1212,
   1214, 1216, 1218, 1220, 1222, 1224, 1226, 1228, 1230, 1232, 1234, 1236, 1238, 1240, 1242, 1244,
   1246, 1248, 1250, 2382, 2399]

/-- **The kernel's input tensors are read-only** (kernel-local; approved by the user, relayed by
the peer session, 2026-11-19).

* `wf` (removes executions): a plain read (`.rd`) at one of `inputReadSites` returns, at every
  byte whose launch content is known (`mem0` gives a byte), that byte.
* `ub` (only stricter, and independent of the reads): undefined if an issued ordinary or
  asynchronous operation of the execution writes a byte of an input array, that is a global byte
  of CTA 0 that `Params.reads` names for some `P` with `Pre P L mem0`. The output arrays are
  fixed by the launch (`param_10`, `param_11`, `param_24`, `param_25`), so every such `P` keeps
  them apart from its inputs (`Pre.outputsApart`).

Why `wf` cannot hide a kernel that writes its inputs. Suppose a run on the hardware writes an
input byte, and take the first such write in real time. Before it no write has touched an input
byte, so every read at a site before it returned the launch content. The prefix of the run up to
and including that write satisfies `wf` and contains a write of an input byte, so it has `ub`.
The safety theorem (`Correct.safe`: every consistent execution is not `Unsafe`) covers that
prefix: `Consistent.thr` asks only `Produces K A L g (X.tr g)`, a finite run with no completion
requirement, and `Maximal`, `Complete` are used only by progress and the result. So the theorem
would fail; the assumption cannot mask such a kernel. Premise, as for every safety claim: the
real-time prefix is a consistent execution of the model. This is why `ub` does not mention the
reads: with `NcReadOnly`'s form (a site read of a byte that some operation writes) a run whose
read of the written byte comes after the write would have no `ub` on the prefix through the write,
and the full run would be removed by `wf`.

Why the kernel needs it: the epilogue's output stores have addresses computed from the loaded
`cu_seqlens_q` word, so an execution in which two CTAs each load that word from the other's
output store (a value cycle across CTAs) is not excluded by the model's clauses: Core has no
no-thin-air clause, and nothing orders events of two CTAs of this kernel. With the assumption a
read at these sites returns the launch content, so no such cycle exists. -/
def inputReadOnly : Assumption where
  name := "inkling-input-read-only"
  statement := s!"The kernel never writes its input tensors cu_seqlens_q, seq_lens, the block \
    table, the query tensor and the bias (Rel) tensor: a plain ld.global at exactly these \
    sites: {siteText inputReadSites} returns the launch content of every byte whose launch \
    content is known, and writing a byte of these input arrays, by any operation of the \
    execution, whether or not a read reads it, is undefined. This is a kernel-local reading \
    of the frozen PTX, whose only global stores are the stores into the two output arrays; \
    without it the model does not exclude a value cycle through global memory between two \
    CTAs."
  wf _ mem0 X := ∀ e pc a bs, X.get e = some ⟨pc, .rd a bs⟩ → inputReadSites.contains pc →
    ∀ k < a.size, ∀ c, mem0 (a.loc.at k) = some (some c) → bs[k]? = some (some c)
  ub L mem0 X := ∃ P w a' l, Pre P L mem0 ∧ X.Intent w a' true ∧ a'.Covers l ∧
    l.space = .global ∧ l.cta = 0 ∧ P.reads l.addr

end PTX.Kernels.InklingRelDecode.Assumptions
