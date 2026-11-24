-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.SafeFacts
public import Kernels.FlashAttn4Fwd.Proof.ResultFacts
public import Kernels.FlashAttn4Fwd.Proof.ValuesGlue
public import Kernels.FlashAttn4Fwd.Proof.FactsAll2
public import Kernels.FlashAttn4Fwd.Proof.Protocol.SmemElementsMma
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesInputs
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesScore
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesStats
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesPv
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaUses
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCover

@[expose] public section

/-! # The protocol premises of the safety and value goals

For every consistent execution, from the thread layer's exports (`FactsAll.threadInputs`): the
shared operands of the MMAs are FP16 values (`SmemElements.smemElements_of_descs`, with the
inputs unwritten by `Result.frame`), and, for a complete execution, the value links between the
roles (`ValuesScore.scoreLoads`, `Floats.stats_reads`, `ValuesPv.pvChain`), from the context of
the values (`ValuesOps.Ctx`) assembled from the handoffs as in `safe_goal`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace FactsAll

/-- No write covers a global byte outside O (`Result.frame`). -/
theorem inputsUnwritten (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) :
    SmemElements.InputsUnwritten P X :=
  fun _ hs hout => Result.frame
    (Result.writes_within_output hpre (itemCoords hpre) hX (store hpre hX) (writes hX)) hs hout

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- The rings' barriers are initialized first (`InitFirst.ringInit`). -/
theorem ringInit : Rings.RingInit L X :=
  have hi := threadInputs hpre hX
  InitFirst.ringInit hpre hX hi.cluster hi.tmem hi.init hi.rings

/-- **An MMA's operands read from shared memory are FP16 values.** -/
theorem smemElements : TcMmaSources.SmemElements X :=
  have hi := threadInputs hpre hX
  SmemElements.smemElements_of_descs hpre hX hi.rings hi.tmem (ringInit hpre hX)
    hi.ringCopies hi.async (inputsUnwritten hpre hX) hi.score hi.tc hi.tcmma
    (mmaSmemFacts hpre hX (tracked hpre hX))

/-- The softmax warps' arrivals on the statistics barriers (`Stats.softArrives`). -/
theorem softArrives : Stats.SoftArrives L X :=
  have hi := threadInputs hpre hX
  Stats.softArrives hpre hX hi.stats hi.older

/-- The context of the routes (`routeCtx`). -/
theorem routeCtx' : Score.RouteCtx P L mem0 kernel asms X :=
  have hi := threadInputs hpre hX
  routeCtx hpre hX hi.route hi.pready hi.p2 hi.sfull hi.ofull hi.stats hi.tmem hi.init hi.cluster
    (softArrives hpre hX) hi.spin

/-- Every handoff (`handoffs`). -/
theorem handoffs' : Handoffs L X :=
  handoffs (routeCtx' hpre hX) (threadInputs hpre hX).score

/-- **The context of the values** (`ValuesOps.Ctx`). -/
theorem valuesCtx : ValuesOps.Ctx P L mem0 X :=
  have hi := threadInputs hpre hX
  have hh := handoffs' hpre hX
  { base := valueCtx_of hpre hX hi ⟨smemElements hpre hX⟩
    steps := mmaStepFacts hpre hX (tracked hpre hX)
    inputs := ValuesInputs.smemInputs hpre hX hi.rings hi.tmem (ringInit hpre hX)
      hi.ringCopies hi.async (inputsUnwritten hpre hX) hi.score hi.tc hi.tcmma
      (mmaStepFacts hpre hX (tracked hpre hX)) (mmaUseFacts hpre hX (tracked hpre hX))
    softCover := Cover.softCoverLast hpre hi.score hi.tc hi.tcmma hi.cover hh.sFull
    corrCover := Cover.corrCoverLast (routeCtx' hpre hX) hi.score hi.oacc hi.tc hi.tcmma
      hi.cover hh.sFull hh.oFull }

/-- **The correction warps' loads of the statistics return the softmax rows' values.** -/
theorem statsReads : StatsReads L X :=
  have hi := threadInputs hpre hX
  have hin := InitFirst.statsInit hpre hX hi.cluster hi.tmem hi.init hi.stats
  have hsoft : Stats.SoftArrives L X := softArrives hpre hX
  Floats.stats_reads hpre hX hi.stats hi.floats hi.tmem
    (Stats.statsCredit hpre hX hi.stats hi.tmem hin hsoft hi.spin) hsoft
    (statsAsync hX hi.rings hi.output hi.tmem hi.mmaReads)
    fun hg hw hld => TcMmaSources.softLoads_f32 (valueCtx_of hpre hX hi ⟨smemElements hpre hX⟩)
      hg hw hld

/-- **The premises of the output values** (`ValueInputs`). -/
theorem valueInputs : ValueInputs P L X where
  facts := values hpre hX
  scores := ValuesScore.scoreLoads (valuesCtx hpre hX)
  stats := statsReads hpre hX
  pv := ValuesPv.pvChain (valuesCtx hpre hX)
  loads := loadFloats_of hpre hX (threadInputs hpre hX) ⟨smemElements hpre hX⟩
  statsReads := statsFloats_of hpre hX (threadInputs hpre hX) ⟨smemElements hpre hX⟩

end

end FactsAll

end
end PTX.Kernels.FlashAttn4Fwd.Proof
