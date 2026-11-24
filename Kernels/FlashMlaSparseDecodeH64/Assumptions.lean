-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Data.Sites
public import Kernels.FlashMlaSparseDecodeH64.Data.Params
public import Kernels.FlashMlaSparseDecodeH64.Assumptions.Numerics
public import Kernels.FlashMlaSparseDecodeH64.Assumptions.SharedBits
public import Core.Assumption.IdealReal
public import Core.Assumption.ApproxExact
public import Core.Assumption.CommitOrder
public import Core.Assumption.NcReadOnly
public import Core.Assembly.SharedLifetime

@[expose] public section

/-!
# The assumptions of the FlashMLA sparse decode head64 kernel

Each assumption is built from a constructor in `Core/Assumption/` where one fits, and otherwise
from a kernel-local `Assumption` whose hook is narrowed to the instruction forms or the pcs the
kernel needs. `Data/Sites.lean` proves the pc lists against the decoded program.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
open PTX

noncomputable section

/-- The kernel's floating computation that has an exact `.rn` (or rounding-free) meaning is read
as exact real arithmetic: the `.f32` and `.f32x2` `add`, `sub`, `mul`, `fma`, `max` and `setp`
forms the kernel contains, scalar f32 negation, and the `kind::f16` MMAs with bf16 inputs and an
f32 accumulator. -/
def idealArith : Assumption :=
  Assumption.idealReal "flashmla-h64-ideal-arith"
    { float := [.add .f32, .mul .f32, .subRn .f32, .fma .f32, .max .f32, .setp .f32,
        .setpInf .f32, .neg .f32, .addRnF32x2, .fmaRnF32x2, .mulF32x2],
      mma := [.f16 .bf16 .f32] }
    "The kernel computes S = Q K^T and O = P V with kind::f16 MMAs over bf16 operands, the \
    softmax row maxima, exponent reference, online rescaling with f32 and f32x2 arithmetic, \
    and the LSE comparison with setp.f32; PTX rounds these (nearest even for .rn) \
    while the theorem states the exact real attention."

/-- `ex2.approx.ftz.f32` (the softmax exponentials, the rescale factor and the sink term) is read
as the exact `2 ^ x`; `div.approx.ftz.f32` (the output normalization) as the exact `1 / x`. -/
def approx : Assumption :=
  Assumption.approxExact "flashmla-h64-approx-ex2-div" [.ex2 .f32, .div .f32]
    "The kernel computes every softmax exponential with ex2.approx.ftz.f32 and the output scale \
    with div.approx.ftz.f32; the theorem states the exact attention, so these are read as the \
    exact 2^x and 1/x, ignoring their ulp error and the flush of subnormal results to zero."

/-- The 17 `ld.global.nc` loads of the top-k lengths, the sink and the index arrays read launch
content that the kernel does not write. -/
def ncReadOnly : Assumption :=
  Assumption.ncReadOnly "flashmla-h64-nc-readonly" ncLoads
    "The kernel reads the per-batch top-k lengths, the per-head sink and the sparse index rows \
    with ld.global.nc; the launch passes these buffers as read-only inputs and no operation of \
    the kernel writes them."

/-- The offset of a parameter-pointer addition: an integer constant or a register holding one
(the `selp` between 768 and 896). -/
def offsetOf (t : TState) : Opnd → Option Int
  | .imm v => some v
  | .reg r => match readReg t r with
    | .ok (.bits 64 x) => some (Int.ofNat x.toNat)
    | _ => none
  | _ => none

/-- At the six descriptor-offset additions of `param_1`, a parameter-space pointer plus an
offset becomes the numeric address of one of the four published descriptors. At the three
`prefetch.tensormap` sites the prefetch checks that the numeric address is a published map and
otherwise has no effect. -/
def paramPointers : Assumption where
  name := "flashmla-h64-param-pointers"
  statement := "At the six add.s64 sites that add {128, 512, 768, 896} to the address of the \
    param_1 tensor-map object, the arithmetic on the parameter-space pointer is read as the \
    numeric address param_1 + offset, where param_1's base is the launch's binding of the \
    by-value object; at the three prefetch.tensormap sites the prefetched numeric address is \
    read as one of the published tensor maps. The addresses are these sites: \
    [22, 23, 24, 25, 26, 27, 1197, 1902, 2256]."
  localRule L g t op :=
    if paramAdds.contains t.pc then
      match op with
      | .int ⟨.add, .int .s 64, _, [some d], [.reg a, k]⟩ =>
        match readReg t a with
        | .ok (.ptr 64 true (.param name) 0) =>
          match L.paramObjects name, offsetOf t k with
          | some (_, base), some off =>
            if 0 ≤ off then
              some (pure (next (setReg t d (.bits 64 (BitVec.ofNat 64 (base + off.toNat))))))
            else none
          | _, _ => none
        | _ => none
      | _ => none
    else if prefetchTensorMapSites.contains t.pc then
      match op with
      | .prefetchTensorMap true 64 src =>
        match readValue L g t 64 src with
        | .ok (.bits 64 x) => if (L.tensorMaps x.toNat).isSome then some (pure (next t)) else none
        | _ => none
      | _ => none
    else none

/-- At the four static output-store sites, every issued tensor store completes reading its
shared source before its issuing thread exits. This supplies a lifetime edge and requires the
read-completion stage to be present at each matching exit. -/
def storeDrain : Assumption where
  name := "flashmla-h64-store-drain"
  statement := "At each output store site [1358, 1516, 1673, 1831], the shared source reads \
    complete before the issuer exits. The PTX commits at site 1832 but has no subsequent \
    group wait. A cp.async.bulk.wait_group.read 0 after that commit (before the barrier.sync \
    at PTX line 3615) would supply the lifetime order through EXT-READ-WAIT-ORDER."
  storeReadsBeforeExit := tensorStores.contains
  wf _ _ X := TensorStore.ReadsDrainedBeforeExit tensorStores.contains X

/-- The PV commit is the only selected Tensor Core commit site. -/
def pvCommitOrderSites : List Nat := [2148]

/-- Site 2148 is the third of the frozen program's audited Tensor Core commits. -/
theorem pvCommitOrderSites_eq : pvCommitOrderSites = tcCommit.drop 2 := by
  rw [tcCommit_eq]
  decide +kernel

/-- The PV arrive-on is ordered before the next commit's arrive-on on the same MMA lane.

ERR-SHARED-LIFETIME cites PTX ISA 9.5 §2.2.2, "The executing CTA has to make sure that
the shared memory of the peer CTA exists before communicating with it via shared memory
and the peer CTA hasn’t exited before completing the shared memory operation." It also cites
§5.1.7, "The shared ( .shared ) state space is a memory that is owned by an executing CTA".

The list in PTX ISA 9.5 §9.7.18.6.2.1.1 is:

1. `tcgen05.mma`
2. `tcgen05.cp`
3. `tcgen05.shift`

§9.7.18.12.1 says, "Makes the mbarrier object track the completion of all prior async-tcgen05
operations initiated by the executing thread." The tracked list excludes commit itself, so
this description does not supply an order between arrive-ons.

All PV buffer generations that will be reused are accounted for by their observers. On a CTA
with at least two KV blocks, the penultimate PV at site 2148 (PTX line 4196) lacks a reuse
wait: the WG0 epilogue at site 1184 waits for the final PV slot. The elected MMA lane also
issues the last block's QK commit at site 2105, whose completion WG0 observes before exit.
For one block the only PV is the one observed by the epilogue. The padded main length gives
at least one block even when the effective main and extra lengths are zero.
-/
def commitOrder : Assumption :=
  Assumption.commitOrderAt "flashmla-h64-pv-commit-order" pvCommitOrderSites
    "The penultimate PV slot has no reuse wait. Its notification must precede the same MMA \
    lane's next commit notification, which is observed by a softmax lane before CTA exit."

/-- All assumptions of the kernel's theorems. -/
def all : List Assumption :=
  [idealArith, approx, mulBf16x2, cvtBf16x2, cvtUe8m0,
    lg2Exact, ncReadOnly, paramPointers, storeDrain, sharedBits, commitOrder]

/-- Exactly the audited tensor stores are selected for the source-read drain. -/
theorem all_storeReadsBeforeExit (pc : Nat) :
    all.any (·.storeReadsBeforeExit pc) = tensorStores.contains pc := by
  simp [all, idealArith, approx, mulBf16x2, cvtBf16x2, cvtUe8m0,
    lg2Exact, ncReadOnly, paramPointers, storeDrain, sharedBits, commitOrder,
    Assumption.commitOrderAt, Assumption.idealReal,
    Assumption.approxExact, Assumption.ncReadOnly]

/-- Only the audited PV commit selects the commit order. -/
theorem all_commitInOrder (pc : Nat) :
    all.any (·.commitInOrder pc) = pvCommitOrderSites.contains pc := by
  simp [all, idealArith, approx, mulBf16x2, cvtBf16x2, cvtUe8m0,
    lg2Exact, ncReadOnly, paramPointers, storeDrain, sharedBits, commitOrder,
    Assumption.commitOrderAt, Assumption.idealReal,
    Assumption.approxExact, Assumption.ncReadOnly]

/-- No assumption selects a poll branch. -/
theorem all_uniPoll (pc : Nat) : all.any (·.uniPoll pc) = false := by
  simp [all, idealArith, approx, mulBf16x2, cvtBf16x2, cvtUe8m0,
    lg2Exact, ncReadOnly, paramPointers, storeDrain, sharedBits, commitOrder,
    Assumption.commitOrderAt, Assumption.idealReal,
    Assumption.approxExact, Assumption.ncReadOnly]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
