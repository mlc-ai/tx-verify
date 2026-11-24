-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Spec
public import Core.Assumption.IdealReal
public import Core.Assumption.ClusterScopeMbar
public import Core.Assumption.ApproxExact
public import Core.Assumption.SegmentExact
public import Kernels.FlashAttn4Fwd.Assumptions.Exp2Template
public import Core.Assumption.PairEven
public import Core.Assumption.TcLdDataflow
public import Core.Assumption.CommitOrder
public import Core.Assumption.PollAgree

@[expose] public section

/-!
# The assumptions of the FlashAttention-4 forward kernel

Each assumption is built from a constructor in `Core/Assumption/` and narrowed to the
instruction forms or the instruction indices (pcs) where the kernel needs it. `Audit/` checks the
pc lists against the decoded program. The reasons for each, the alternatives and their kind are
recorded in `DECISIONS.md`.
-/

namespace PTX.Kernels.FlashAttn4Fwd.Assumptions
open PTX

/-- The kernel's floating computation that has an exact `.rn` (or rounding-free) meaning is read
as exact real arithmetic: the `kind::f16` MMAs (f16 inputs, f32 accumulator, §9.7.18) for
`S = Q Kᵀ` and `O += P V`; `.f32` `add`, `mul`, `sub.rn`; `.f32x2` `add.rn`, `sub.rn`,
`fma.rn` and `mul`; two- and three-input `max.f32`; floating `setp`; and the
`cvt.rn.f16x2.f32` that packs P and O. The kernel has no `min.f32`, no scalar `fma.f32` and no
`cvt.f32.f16`. -/
noncomputable def idealArith : Assumption :=
  Assumption.idealReal "fa4-fwd-ideal-arith"
    { float := [.add .f32, .mul .f32, .subRn .f32, .addRnF32x2, .subRnF32x2, .fmaRnF32x2,
        .mulF32x2, .max .f32, .setp .f32, .setpInf .f32, .cvtRnF16x2F32],
      mma := [.f16 .f16 .f32] }
    "FlashAttention-4 computes S = Q K^T and O += P V with kind::f16 MMAs, the softmax \
    exponent arguments, row maxima, row sums and rescaling with f32 and f32x2 arithmetic, and \
    packs P and the output with cvt.rn.f16x2.f32; PTX rounds these (\".rn mantissa LSB rounds \
    to nearest even\") while the theorem states the exact real attention."

/-- The remote arrivals: every `mbarrier.arrive.shared::cluster.b64` of the kernel, all with the
default `.release.cta` (PTX lines 1509, 3131, 3147, 4309, 4325, 4528, 4531, 4839, 5059, 5375,
5685): the MMA warp's TMEM-dealloc handshake on the peer CTA (`+320`), the softmax warps' P-ready
arrivals (`+144/+152`, `+160/+168`) and the correction warps' O-free arrivals (`+144/+152`) on
the leader CTA. -/
def remoteArrives : List Nat :=
  [1121, 2550, 2566, 3565, 3581, 3762, 3765, 4069, 4288, 4589, 4885]

/-- `remoteArrives` are exactly the kernel's `.shared::cluster` mbarrier arrivals. -/
theorem remoteArrives_eq : remoteArrives = (kernel.code.zipIdx.filter
    (fun p => match p.1.op with
      | .mbarArrive _ _ _ _ true .. => true
      | _ => false)).map (·.2) := by
  decide +kernel

/-- The waits (default `.acquire.cta`) on the barriers the remote arrivals reach: the leader
MMA warp's waits on `+144/+152` (PTX 1000, 1166, 1345, 1421) and, inside the PV inline
assembly, on `+160/+168` (1053, 1213, 1398, 1468), and the MMA warp's handshake wait on `+320`
(1514). -/
def remoteArriveWaits : List Nat := [754, 791, 876, 907, 1006, 1043, 1057, 1088, 1122]

/-- The waits on the barriers the leader's multicast `tcgen05.commit` (mask 3) arrives on in
both CTAs: Q empty `+16/+24` (PTX 364, 404, 696), KV empty `+80 .. +120` (324, 444, 486, 536 and
the loader tail 596, 614, 632, 650, 668, 686), S full `+128/+136` (1687, 3320) and O full
`+192/+200` (5077, 5387). -/
def commitWaits : List Nat :=
  [261, 291, 321, 351, 382, 422, 471, 482, 493, 504, 515, 526, 529, 1263, 2725, 4301, 4597]

/-- The leader MMA warp's waits on the full barriers that both CTAs' `cta_group::2` tensor
loads complete on: Q full `+0/+8` (PTX 784, 886) and KV full `+32 .. +72` (797, 990, 1078,
1335). The odd CTA's loads name the leader's barrier, so their complete-tx comes from a thread
of the peer CTA. -/
def fullWaits : List Nat := [595, 601, 670, 751, 808, 1003]

/-- The sites of `clusterMbar`. -/
def clusterMbarSites : List Nat := remoteArrives ++ remoteArriveWaits ++ commitWaits ++ fullWaits

/-- Every listed wait site is an acquire `mbarrier.try_wait` at the default `.cta` scope. -/
theorem waits_are_cta_waits : ∀ pc ∈ remoteArriveWaits ++ commitWaits ++ fullWaits,
    (match (kernel.code[pc]?).map Instr.op with
      | some (.mbarWait _ _ _ _ true .cta) => true
      | _ => false) = true := by
  decide +kernel

/-- The `.cta`-scoped arrivals and waits through which the CTA pair hands off data synchronize at
cluster scope: the remote arrivals on the peer CTA's barriers with the waits on those barriers,
the odd CTA's waits on the leader's multicast commits, and the leader's waits on the full
barriers that the odd CTA's tensor loads complete on. At a site whose barrier is in the
issuing CTA it adds no edge. -/
def clusterMbar : Assumption :=
  Assumption.clusterScopeMbarAt "fa4-fwd-cluster-mbar" clusterMbarSites
    "FlashAttention-4's CTA pair hands off data through mbarrier arrivals on the peer CTA's \
    barrier (mbarrier.arrive.shared::cluster) and acquire waits, all with the default scope \
    (\"If the .scope qualifier is not specified then it defaults to .cta\"), which does not \
    include the peer CTA's threads; the odd CTA also waits at .cta scope on the leader's \
    multicast tcgen05.commit arrivals, and the leader's MMA warp waits at .cta scope on the \
    full barriers that the odd CTA's cta_group::2 tensor loads complete on."

/-- `ex2.approx.ftz.f32` (209 sites: the softmax exponentials and the rescale factor) is read as
the exact `2 ^ x` and `rcp.approx.ftz.f32` (2 sites: the final normalization) as the exact
`1 / x`. -/
noncomputable def approx : Assumption :=
  Assumption.approxExact "fa4-fwd-approx-exp2-rcp" [.ex2 .f32, .rcp .f32]
    "FlashAttention-4 computes most softmax exponentials with ex2.approx.ftz.f32 and the final \
    row-sum reciprocal with rcp.approx.ftz.f32; the theorem states the exact attention, so these \
    are read as the exact 2^x and 1/x, ignoring their ulp error and the flush of subnormal \
    results to zero."

/-- The 24 software `exp2` segments (CuTeDSL's exp2 emulation): the defining shape at 2121 and
3136, the reusing shape at the other 22. -/
def swExp2Sites : List Nat := [2121, 2152, 2179, 2200, 2227, 2248, 2301, 2322, 2349, 2370, 2397,
  2418, 3136, 3167, 3194, 3215, 3242, 3263, 3316, 3337, 3364, 3385, 3412, 3433]

/-- Each software-`exp2` segment is read, per lane, as the exact `2 ^ x` of its input. -/
noncomputable def swExp2 : Assumption :=
  Assumption.segmentExact kernel "fa4-fwd-sw-exp2" Assumption.cuteExp2 swExp2Sites
    "FlashAttention-4 computes 24 of every 128 softmax exponentials with a software exp2 \
    (clamp at -127, add.rm.f32x2 with 1.5*2^23 to split off the integer part, a degree-3 \
    polynomial for the fraction, and an integer add into the exponent field); the whole \
    straight-line segment is read as the exact 2^x per lane. The clamp and the polynomial error \
    are approximations of 2^x that the theorem does not model."

/-- The `and.b32 x, a, -16777217` instructions that clear bit 24 of the CTA's own shared address
to name the even CTA's mbarrier for the `cta_group::2` tensor loads. -/
def peerBitSites : List Nat := [222, 225, 273, 365, 396, 436]

/-- Clearing bit 24 of a CTA's shared address gives the same offset in the even CTA of its pair,
as a `.shared::cluster` address. -/
noncomputable def peerBit : Assumption :=
  Assumption.pairEvenAt kernel "fa4-fwd-pair-peer-bit" peerBitSites
    "FlashAttention-4's odd CTA signals the leader CTA's full barriers for its cta_group::2 \
    tensor loads by clearing bit 24 of its own shared address (CUTLASS Sm100MmaPeerBitMask); the \
    ISA defines no bit encoding of shared::cluster addresses."

/-- The kernel's 40 `tcgen05.ld` sites; none is followed by `tcgen05.wait::ld`. -/
def tcLdSites : List Nat := [1266, 1283, 1300, 1317, 2728, 2745, 2762, 2779, 3858, 3885, 3911,
  3937, 3963, 3989, 4015, 4041, 4077, 4104, 4130, 4156, 4182, 4208, 4234, 4260, 4308, 4343, 4378,
  4413, 4448, 4483, 4518, 4553, 4604, 4639, 4674, 4709, 4744, 4779, 4814, 4849]

/-- Each listed `tcgen05.ld` is complete, for ordering, as if a `tcgen05.wait::ld` followed it. -/
def tcLd : Assumption :=
  Assumption.tcLdDataflowAt kernel "fa4-fwd-tcld-dataflow" tcLdSites
    "FlashAttention-4 uses no tcgen05.wait::ld: every tcgen05.ld's destination registers are \
    consumed by computing instructions before the thread's next event, and the kernel relies on \
    that data dependency to order the load's Tensor Memory read before later writes of the \
    cells and before the deallocation."

/-- The arrive-on of the last Q-empty commit (pc 995) is ordered before that of the issuing
thread's next commit. -/
def commitOrder : Assumption :=
  Assumption.commitOrderAt "fa4-fwd-commit-order" [995]
    "FlashAttention-4 never waits for its last Q-empty tcgen05.commit arrive-on in the odd CTA; \
    its exit relies on that arrive-on being performed before the arrive-on of the MMA thread's \
    next commit, which is observed."

/-- The kernel's poll branches: every guarded `bra.uni`, each on the predicate of the
`mbarrier.try_wait` right before it. Each warp that polls runs its polls on all 32 lanes: the
loader warp (14) and the MMA warp (12) at their ring, tail and handshake waits, the store warp (13)
at pcs 1164 and 1174, and the softmax (0-7) and correction (8-11) warps. -/
def pollAgreeSites : List Nat :=
  [262, 292, 322, 352, 383, 423, 472, 483, 494, 505, 516, 527, 530, 596, 602, 671, 752, 755, 809,
    877, 1004, 1007, 1058, 1123, 1164, 1174, 1260, 1264, 2575, 2726, 3588, 3747, 4302, 4305, 4598,
    4601, 4893]

/-- At the listed poll branches, two lanes' executions after polls of one mbarrier are not
compared, whatever the polls' parities. -/
def pollAgree : Assumption :=
  Assumption.pollAgreeAt "fa4-fwd-poll-agree" pollAgreeSites
    "FlashAttention-4 spins on all 32 lanes of a warp at each of its waits with \
    mbarrier.try_wait P; @P bra.uni: lanes polling one phase in one round are not ordered, and \
    the store warp (13) has no warp collective between its rounds, so nothing orders one lane's \
    failed poll of an item's phase before another lane's successful poll of the next item's \
    phase."

/-- All assumptions of the FA4 theorems. -/
noncomputable def all : List Assumption :=
  [idealArith, clusterMbar, approx, swExp2, peerBit, tcLd, commitOrder, pollAgree]

/-- Only `commitOrder` selects commit sites. -/
theorem all_commitInOrder (pc : Nat) :
    all.any (·.commitInOrder pc) = [995].contains pc := by
  simp [all, idealArith, clusterMbar, approx, swExp2, peerBit, tcLd, commitOrder, pollAgree,
    Assumption.idealReal, Assumption.clusterScopeMbarAt, Assumption.approxExact,
    Assumption.segmentExact, Assumption.pairEvenAt, Assumption.tcLdDataflowAt,
    Assumption.commitOrderAt, Assumption.pollAgreeAt]

/-- Only `pollAgree` selects poll branches. -/
theorem all_uniPoll (pc : Nat) : all.any (·.uniPoll pc) = pollAgreeSites.contains pc := by
  simp [all, idealArith, clusterMbar, approx, swExp2, peerBit, tcLd, commitOrder, pollAgree,
    Assumption.idealReal, Assumption.clusterScopeMbarAt, Assumption.approxExact,
    Assumption.segmentExact, Assumption.pairEvenAt, Assumption.tcLdDataflowAt,
    Assumption.commitOrderAt, Assumption.pollAgreeAt]

end PTX.Kernels.FlashAttn4Fwd.Assumptions
