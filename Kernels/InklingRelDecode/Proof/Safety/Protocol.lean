-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Barriers

@[expose] public section

/-!
# The facts `safe_goal` takes from the layers below

`Protocol Q L X` is the one structure of what the safety layer has not proved for an execution `X`
of the kernel. Each field is a statement of the thread layer (a classification of the events of
every thread) or of a protocol, and each is read as the statement its docstring gives; the field
names are the rows of the design note in `All.lean`.

Where a branch of `Unsafe` could be factored, the fields are the factors (the memory branches take
placement, region orders and store uniqueness; the mbarrier branch takes record faults and
publication; the tensor branches take the map operand and the boxes). A few branches enter whole
(`¬ Branch`), as the design note says, because the protocol that proves them is not written.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

/-- **What `safe_goal` takes for one execution.** -/
structure Protocol (Q : Params) (L : Launch) (X : Execution) : Prop where
  -- Thread layer: the machines never stop on a value, and every event is classified
  /-- The machines continue at every event that has a later event of its thread (the exit events
  are last and `next` is `none` there): no such event is one the machine's `next` rejects with
  `none` (the facts of "thread-layer gaps": loaded words, shuffles, role bytes, `lg2`/`rcp`
  domains). -/
  faultFree : ∀ {g k : Nat} {s : TSt} {e : Event}, g < L.threads → (X.tr g)[k]? = some e →
    (X.tr g)[k + 1]? ≠ none → Frame.stateAt (code L Q) X g k = some (some s) →
    (threadCode L g Q).next s e ≠ none
  /-- Every shared byte an access touches is in a region of a launched CTA (`Regions.lean`). -/
  sharedPlaced : SharedPlaced L X
  /-- Every global byte an access touches is an input byte or an output byte. -/
  globalPlaced : GlobalPlaced Q X
  /-- Every global byte an access reads is an input byte (`Params.reads`). -/
  globalReads : GlobalReads Q X
  /-- The softmax region's `o_done` poll names `o_done` of its CTA (the one poll without an event
  shape). -/
  odoneWait : OdoneWait Q L X
  /-- Every tensor copy's box is inside the map. -/
  boxInBounds : BoxInBounds X
  -- Protocols: memory orders
  /-- The shared regions' orders (`Memory.SharedOrder`). -/
  order : SharedOrder L X
  -- Protocols: mbarriers
  /-- No mbarrier record faults (counts, phases, transaction balance). -/
  recordsOk : ¬ ∃ m r, r ∈ X.objects m ∧ r.fault.isSome
  /-- Every mbarrier record lies in an initialized lifetime published to its issue. -/
  objectsPublished : ∀ m r, r ∈ X.objects m → ObjectPublished L X m r
  /-- Every mbarrier operand has an initialization published to it (the initialization before
  use: `bar.sync 0` and the named barrier). Open as a whole. -/
  mbarInit : ¬ MbarUninit L X
  -- Protocols: named barriers, warps, lifetimes, registers
  /-- Lanes of a warp agree on the barrier and the thread count at each barrier ordinal (the
  kernel has no `bar.arrive`, so this is all of `BarMismatch`). -/
  barLanes : ¬ BarLaneMismatch L X
  /-- Named barrier 0 (counts 256, 128, 256) and barrier 1 (256) accept every arrival
  (`EXT-BAR-PARTICIPANTS`). Open as a whole. -/
  ctaBar : ¬ CtaBarFault L X
  /-- The lanes of a warp run the `tcgen05` collectives in lockstep (same position and operands at
  the `k`-th one), and no lane exits before its warp's. -/
  tcAligned : ¬ AlignedClass.tc.Divergent L kernel X ∧ ¬ AlignedClass.tc.Exited L kernel X
  /-- The same for `barrier{.cta}`: lanes agree on the source position, and no participant of an
  aligned barrier without a thread count exits before it (`bar.sync 0` of 256 threads). -/
  barAligned : ¬ AlignedClass.bar.Divergent L kernel X ∧ ¬ AlignedClass.bar.Exited L kernel X
  /-- The same for `setmaxnreg`: lanes agree on the position, and no thread of the warpgroup
  exits before its warps' request. -/
  regAligned : ¬ AlignedClass.setMaxReg.Divergent L kernel X ∧
    ¬ AlignedClass.setMaxReg.Exited L kernel X
  /-- No guarded `bra.uni` is evaluated differently by two lanes of a warp. The kernel's six poll
  branches are executed by all 32 lanes with no ordering between their polls, and
  `Assumptions.all` has no poll-agreement assumption, so this field is not provable from the
  protocols alone: it needs `Assumption.pollAgreeAt` at the six branches (the development notes,
  `D-ASM-POLLAGREE`). -/
  warpUniform : ¬ WarpDivergent L kernel asms X
  /-- Every use of a CTA's shared memory completes before an exit of the CTA's threads. Open as a
  whole. -/
  lifetime : ¬ SharedLifetimeUnsafe L kernel asms X
  /-- The four warps of a warpgroup request the same direction and count at each ordinal
  (`EXT-BAR-PARTICIPANTS`; the workers' requests depend on their roles). -/
  regAgree : RegAgree L X
  /-- A request follows the previous requests of the whole warpgroup in base causality order
  (`barrier.sync 1` between them). -/
  regSync : RegSync L X
  -- Protocols: Tensor Memory and the MMAs
  /-- Every Tensor Core read has a supported source. Open as a whole. -/
  tcSource : ¬ TcMma.SourceUnsafe L asms X
  /-- Every Tensor Memory access is inside a completed allocation and completes before its
  release. Open as a whole. -/
  tmemAccess : ¬ Tmem.Pair.AccessUnsafe L X
  /-- Every two writers of a Tensor Memory cell are ordered. Open as a whole. -/
  tcWrites : ¬ TcMma.WritesUnsafe L X
  /-- Every MMA is a valid instance with a derived value. Open as a whole. -/
  tcInstr : ¬ TcMma.InstructionUnsafe L asms X
  /-- Every MMA read is ordered with every writer of its cell. Open as a whole. -/
  tcReads : ¬ TcMma.ReadsUnsafe L X

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
