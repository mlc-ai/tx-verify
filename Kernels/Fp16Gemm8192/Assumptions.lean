-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Spec
public import Core.Assumption.IdealReal
public import Core.Assumption.ClusterScopeMbar
public import Core.Assumption.PollAgree

@[expose] public section

/-!
# The assumptions of the production FP16 GEMM

The theorems of `Theorem.lean` assume exactly `idealArith`, `clusterMbar` and `pollAgree`, and
nothing else.
-/

namespace PTX.Kernels.Fp16Gemm8192.Assumptions
open PTX

/-- The kernel's floating computation — its `tcgen05.mma.cta_group::2.kind::f16` with f16
inputs and f32 accumulator (§9.7.18) and the epilogue's `cvt.rn.f16x2.f32` (§9.7.10.25) — is
read as exact real arithmetic, so that the output is the exact real GEMM. -/
noncomputable def idealArith : Assumption :=
  Assumption.idealReal "fp16-gemm-ideal-arith"
    { float := [.cvtRnF16x2F32], mma := [.f16 .f16 .f32] }
    "The GEMM accumulates with kind::f16 MMAs and packs results with cvt.rn.f16x2.f32; PTX \
    rounds the conversion (\".rn mantissa LSB rounds to nearest even\") and the MMA \
    accumulation, while the theorem states the exact real product."

/-- The mbarrier sites of `clusterMbar`: every `mbarrier.arrive` and `mbarrier.try_wait` of the
kernel, all `.cta`-scoped release arrivals and acquire waits. -/
def clusterMbarSites : List Nat :=
    [119, 144, 149, 173, 178, 202, 207, 231, 236, 259, 264, 287, 292, 315, 320, 343, 350, 368, 389,
     393, 397, 401, 419, 429, 431, 450, 494, 512, 513, 520, 541, 563, 585, 707, 728, 746, 913]

/-- `clusterMbarSites` are exactly the kernel's mbarrier arrivals and waits. -/
theorem clusterMbarSites_eq : clusterMbarSites = (List.range kernel.code.length).filter
    (fun pc => match (kernel.code[pc]?).map Instr.op with
      | some (.mbarWait ..) | some (.mbarArrive ..) => true
      | _ => false) := by
  decide +kernel

/-- The `.cta`-scoped mbarrier arrivals and waits of the kernel (§9.7.15.16.16) synchronize at
cluster scope. The CTA pair's handoffs (the odd CTA's input loads and the consumers' releases of
the leader's barriers) arrive on the peer CTA's mbarriers with the default scope. The proof
treats every poll and arrival of the kernel uniformly as cluster-scoped, so the assumption
names all of them; at a site whose barrier is in the issuing CTA it adds no edge. -/
def clusterMbar : Assumption :=
  Assumption.clusterScopeMbarAt "fp16-gemm-cluster-mbar" clusterMbarSites
    "The GEMM's CTA pairs hand off data through mbarrier arrivals on the peer CTA's barrier \
    and acquire waits, all with the default scope (\"If the .scope qualifier is not specified \
    then it defaults to .cta\"), which does not include the peer CTA's threads; the proof treats \
    every arrival and wait of the kernel as cluster-scoped, so all of them are listed."

/-- The poll branches of the consumer warps (0-7): after their waits on the accumulator-full
barrier (pc 746, branch 747) and on the CLC response barrier (pc 707, branch 708). The kernel's
other 21 poll branches belong to the loader, MMA and scheduler roles, which poll only on the lane
their warp elected, so no two lanes of a warp execute them. -/
def pollAgreeSites : List Nat := [708, 747]

/-- The listed sites are guarded `bra.uni` instructions on the predicate that the unguarded
`mbarrier.try_wait` right before each writes. -/
theorem pollAgreeSites_ops :
    pollAgreeSites.all (fun pc => match kernel.code[pc]?, kernel.code[pc - 1]? with
      | some ⟨some (p, false), .bra _ true⟩, some ⟨none, .mbarWait d ..⟩ => p == d
      | _, _ => false) = true := by
  decide +kernel

/-- At the consumers' poll branches, two lanes' executions after polls of one mbarrier are not
compared, whatever the polls' parities. -/
def pollAgree : Assumption :=
  Assumption.pollAgreeAt "fp16-gemm-poll-agree" pollAgreeSites
    "The GEMM's consumer warps spin on all 32 lanes at their accumulator-full and CLC-response \
    waits with mbarrier.try_wait P; @P bra.uni (CUTLASS's wait loop); lanes polling one phase in \
    one round are not ordered, so their poll results may differ."

end PTX.Kernels.Fp16Gemm8192.Assumptions
