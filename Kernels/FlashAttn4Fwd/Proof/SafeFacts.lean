-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.Memory
public import Kernels.FlashAttn4Fwd.Proof.Safety.Resource
public import Kernels.FlashAttn4Fwd.Proof.Safety.SyncBar
public import Kernels.FlashAttn4Fwd.Proof.Safety.TensorStore
public import Kernels.FlashAttn4Fwd.Proof.Safety.TcLoads
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ClusterStart
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemAlloc
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsGen
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsBaseCausality
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsCreditGate
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputBytes
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputHandoff
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputRegion
public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst
public import Kernels.FlashAttn4Fwd.Proof.SafeGlue
public import Kernels.FlashAttn4Fwd.Proof.TcFacts
public import Kernels.FlashAttn4Fwd.Proof.SafeGlue2
public import Kernels.FlashAttn4Fwd.Proof.SafeGlue3
public import Kernels.FlashAttn4Fwd.Proof.Protocol.Cover
public import Lemmas.Kernel.Goals
public import Lemmas.Flow.NotMatrix
public import Kernels.FlashAttn4Fwd.Proof.Progress.Async
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic

@[expose] public section

/-! # `SafeGoal`

The root of the safety layer: every branch of `Unsafe` is dispatched to its theorem, from the
thread facts and the protocols' exports. `SafeRemaining` holds, per consistent execution, the
facts not yet proved (`SafeInputs`): the thread layer's exports (`ThreadInputs`: its `Interface`
structures and the few facts the safety files state for it) and the protocol premises not yet
discharged (`ProtocolPremises`), each to be replaced by the proof of its protocol.

Discharged from the protocols, given those inputs: the cluster barrier (`ClusterStart`), the
named barriers (`Safety.no_barMismatch`, `Stats.not_ctaBarFault`),
  the assumptions' undefined case (`Safety.no_assumption_ub`: none declares one), the
register requests (`Safety.no_reg_unsafe`), the CLC branch, the
tensor stores, the Tensor Memory allocator (`TmemAlloc.resource_ok`), the loaded registers'
sources (`Safety.tc_supported`, with the cover of the loads' cells: `Cover.softCover`,
`Cover.corrCover`) and the memory branches (`Safety.no_unalloc`, `no_race`,
`no_mixed`; the statistics words by `Stats.stats_ordered`, the staging buffers by
`Output.staging_ordered`, the output by `outputOrdered`; the bytes outside O without exemption,
for the progress layer, by `outside_ordered`), the TMA, tensor, tensor-allocation and
shared-lifetime branches (`SafeGlue`, with the barriers' first initializations `InitFirst.*`),
and the Tensor Core, undefined-behaviour and warp-divergence branches (`TcFacts`, `Safety.no_ub`,
`Safety.no_warpDivergent`). The aligned-instruction branch is checked class by class
(`Safety.no_tcMismatch`, `Safety.no_barDivergent`, `Safety.no_barExited`,
`ClusterStart.no_cluster_mismatch`, `no_setMaxReg_divergent`, `no_setMaxReg_exited`, and
`no_matrix`: the kernel has no warp matrix instruction). Decided on the code: every poll is a
canonical spin (`poll_spins`). Every named mbarrier has an initialization published to its user
(`no_mbarUninit`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof

noncomputable section

/-- **The thread layer's exports**: the interface structures of the roles, and the facts the
safety files state of the threads' events. Each is proved by the thread layer. -/
structure ThreadInputs (P : Params) (L : Launch) (X : Execution) : Prop where
  cluster : ClusterFacts L X
  tmem : TmemFacts L X
  stats : StatsFacts L X
  output : OutputFacts L X
  rings : RingFacts L X
  score : ScoreFacts L X
  reg : Safety.RegFacts L X
  async : AsyncFacts P L X
  ringCopies : RingCopies P L X
  init : InitFacts L X
  oacc : OAccFacts L X
  tc : TcFacts L X
  thread : ThreadFacts L X
  route : RouteFacts L X
  pready : PReadyFacts L X
  p2 : P2Facts L X
  sfull : SFullFacts L X
  ofull : OFullFacts L X
  floats : FloatFacts L X
  tmemLife : TmemLifeFacts L X
  tcmma : TcMmaThreadFacts L X
  warp : WarpSyncFacts L X
  exit : ExitFacts P L X
  older : OlderFacts P L X
  store : StoreFacts P L X
  cover : CoverFacts L X
  /-- No operation names a spare barrier. -/
  spare : Faults.SpareUnused L X
  /-- No thread's write releases. -/
  noRelease : ∀ {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte},
    X.get e = some ⟨pc, .wr a bs⟩ → a.release = false
  /-- A successful wait is in a canonical spin (DEP-CANONICAL-SPIN). -/
  spin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, kernel.CanonicalSpin pc exit
  /-- Barrier 2's `bar.arrive` is its thread's last event on barrier 2. -/
  bar2ArriveLast : Stats.Bar2ArriveLast X
  /-- The tensor stores' boxes start aligned. -/
  storeBoxes : Safety.StoreBoxes X
  /-- Every touched shared byte is in a region of a launched CTA. -/
  sharedPlaced : Safety.SharedPlaced L X
  /-- Every touched global byte is in a tensor. -/
  globalPlaced : Safety.GlobalPlaced P X
  /-- Every global write is of O. -/
  globalWrites : Safety.GlobalWrites P X
  /-- Every MMA operand read is in a ring region. -/
  mmaReads : MmaReadsRings L X

/-- **The protocol premises not yet proved**: each is a statement of one protocol's layer, to
be replaced by that protocol's theorem. -/
structure ProtocolPremises (L : Launch) (X : Execution) : Prop where
  /-- An MMA's operands read from shared memory are FP16 values. -/
  smemElements : TcMmaSources.SmemElements X

/-- The safety facts of one execution not yet proved. -/
structure SafeInputs (P : Params) (L : Launch) (X : Execution) : Prop where
  thread : ThreadInputs P L X
  protocol : ProtocolPremises L X

/-- The safety facts not yet proved, for every consistent execution. -/
def SafeRemaining (P : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X, Consistent L kernel asms mem0 X → SafeInputs P L X

/-! ### Branches decided on the code and the register facts -/

section Static

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every poll of the kernel is the poll of a canonical spin**, whether or not it succeeds: it
fires from a listed poll of the code, which heads a wait loop (as `kernel_spins`). -/
theorem poll_spins (hX : Consistent L kernel asms mem0 X) {e : EvId} {pc : Nat} {m : Loc}
    {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m p ok acq sc⟩) : ∃ exit, kernel.CanonicalSpin pc exit := by
  rcases Flow.get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
    · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
      exact Kernel.canonicalSpin_of_waitLoopPcs kernel_poll_pcs kernel_wait_loops hc hop
    · push Not at hw
      exact absurd rfl (Flow.fires_notWait (Flow.eventTmpl_notWait hw) hf m p ok acq sc)

/-- **The lanes of a warp make their register request at one position**: the request's
position is its warp's (`RegFacts.request`). -/
theorem no_setMaxReg_divergent (hX : Consistent L kernel asms mem0 X)
    (hr : Safety.RegFacts L X) : ¬ AlignedClass.setMaxReg.Divergent L kernel X := by
  intro hd
  obtain ⟨⟨g, i⟩, ⟨h, j⟩, pc, pc', inc, inc', n, n', inst, inst', hw, he, hf, -, hne⟩ :=
    (AlignedClass.divergent_setMaxReg_iff L).mp hd
  obtain ⟨-, hpc, -⟩ := hr.request (Frame.lt_of_get hX he) he
  obtain ⟨-, hpc', -⟩ := hr.request (Frame.lt_of_get hX hf) hf
  have hwarp : warpOf L g = warpOf L h := hw.2
  rw [hpc, hpc', hwarp] at hne
  exact hne rfl

/-- **No thread exits short of its warpgroup's register request**: every request is its
thread's first, and a thread exits after its own. -/
theorem no_setMaxReg_exited (hX : Consistent L kernel asms mem0 X) (hr : Safety.RegFacts L X) :
    ¬ AlignedClass.setMaxReg.Exited L kernel X := by
  intro hx
  obtain ⟨⟨g, i⟩, pc, inc, n, inst, hreq, h, j, pc', hh, -, hex, hle⟩ :=
    AlignedClass.exited_setMaxReg_old L hx
  obtain ⟨h0, -⟩ := hr.request (Frame.lt_of_get hX hreq) hreq
  have h1 := hr.exit hh hex
  omega

/-- **A named mbarrier is initialized, and the initialization is published to its user**: the
mbarrier is a table barrier of the user's pair (`AsyncFacts.mbar_pair`), initialized by the
prologue (`InitFirst.init_exists`) and published through the cluster start
(`ClusterStart.init_published`). -/
theorem mbar_published (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (ha : AsyncFacts P L X) (hi : InitFacts L X) {g j : Nat}
    {ev : Event} {m : Loc} (he : X.get (g, j) = some ev) (hk : ¬ PreKind ev.kind)
    (hub : ∀ f, ev.kind ≠ .ub f) (hu : X.UsesMbar (g, j) m) :
    ∃ i count, X.MbInit i m count ∧ InitPublished L X i (g, j) m := by
  obtain ⟨b, c, rfl, hcl⟩ := ha.mbar_pair hu
  obtain ⟨⟨g0, a0⟩, pci, n, hinit⟩ := InitFirst.init_exists hpre hX hc hi b he hk hub hcl.symm
  refine ⟨_, _, ⟨pci, hinit⟩, ?_⟩
  have hc0 : ctaOf L g0 = c := by
    obtain ⟨b', hm', -⟩ := hc.init_site (Frame.lt_of_get hX hinit) hinit
    exact (FBar.loc_inj hm').2.symm
  exact ClusterStart.init_published hpre hX hc hinit he hk hub (by
    rw [clusterOf_eq hpre, clusterOf_eq hpre, hc0]
    exact hcl)

/-- **Every named mbarrier has an initialization published to its user**: arrivals and polls by
`mbar_published`, commits by `Safety.commit_target_published`, tensor loads by
`tensorLoadInit`; the kernel has no linear copy, `cp.async.mbarrier.arrive`, invalidation or
cancellation request. -/
theorem no_mbarUninit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hr : RingFacts L X) (htm : TmemFacts L X) (ha : AsyncFacts P L X)
    (hcp : RingCopies P L X) (hi : InitFacts L X) (ht : TcFacts L X) : ¬ MbarUninit L X := by
  rintro ⟨⟨g, j⟩, m, hu, hni, hn⟩
  apply hn
  rcases hu with ⟨tx, count, rel, sc, pc, he⟩ | ⟨s, ⟨pc, he⟩, -⟩ | ⟨noinc, pc, he⟩ |
    ⟨s, rank, hcm, htg⟩ | ⟨pc, q, ok, acq, sc, he⟩ | ⟨pc, he⟩ | ⟨address, s, ⟨pc, he⟩, rfl⟩ |
    ⟨s, targets, c, ⟨pc, he⟩, -⟩ | ⟨count, pc, he⟩
  · exact mbar_published hpre hX hc ha hi he (by simp [PreKind]) (by simp)
      (.inl ⟨_, _, _, _, pc, he⟩)
  · exact (htm.no_bulk he).elim
  · exact (TmemFacts_no_arriveOn hX he).elim
  · exact Safety.commit_target_published hX ht (pairInit hpre hX ht hc) hcm htg
  · exact mbar_published hpre hX hc ha hi he (by simp [PreKind]) (by simp)
      (.inr (.inr (.inr (.inr (.inl ⟨pc, q, ok, acq, sc, he⟩)))))
  · exact (htm.no_inval he).elim
  · exact tensorLoadInit hpre hX hc hr ha hcp hi he
  · exact (htm.no_clc he).elim
  · exact (hni count ⟨pc, he⟩).elim

export PTX.Flow (NotMatrix matrixOp widen_notMatrix ofExec_notMatrix eventTmpl_notMatrix
  fires_matrix_op)

theorem kernel_noMatrix : kernel.code.all (fun ins => !matrixOp ins.op) = true := by
  decide +kernel

/-- **The kernel performs no warp matrix instruction.** -/
theorem no_matrix_ev (hX : Consistent L kernel asms mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : isMatrix ev = false := by
  exact Flow.no_matrix_of_code hX kernel_noMatrix he

/-- No event of the kernel is a warp matrix event. -/
theorem no_matrix (hX : Consistent L kernel asms mem0 X) {e : EvId} {pc : Nat} {op : MatrixOp}
    {own : List (Option Byte)} {recv : List (Option Byte)}
    (he : X.get e = some ⟨pc, .matrix op own recv⟩) : False := by
  simpa [isMatrix] using no_matrix_ev hX he

end Static

/-- **The context of the MMA values** of a consistent execution, from the thread layer's exports
and the protocol premises: the routes and handoffs, the Tensor Memory lifetimes, the covers of
the loads' cells, guarded synchronization (every mbarrier record is fault-free) and the
statistics reads' floats. -/
theorem valueCtx_of {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (hi : ThreadInputs P L X)
    (hp : ProtocolPremises L X) : TcMmaSources.ValueCtx P L mem0 X :=
  have hsoft : Stats.SoftArrives L X := Stats.softArrives hpre hX hi.stats hi.older
  have hin := InitFirst.statsInit hpre hX hi.cluster hi.tmem hi.init hi.stats
  have hU := Stats.statsCredit hpre hX hi.stats hi.tmem hin hsoft hi.spin
  have hrc := routeCtx hpre hX hi.route hi.pready hi.p2 hi.sfull hi.ofull hi.stats hi.tmem
    hi.init hi.cluster hsoft hi.spin
  have hh := handoffs hrc hi.score
  have hother := otherFaultFree hrc hi.cluster hi.async hi.output hi.spare
  have hlt := tmemLifetime hpre hX hi.stats hi.score hi.oacc hi.tc hi.tmem hi.init hi.cluster
    hi.tmemLife hh.oFull
  have hsg : SyncGuarded L kernel X :=
    Progress.syncGuarded_of hX hi.rings (fun _ _ _ _ he => hi.noRelease he) hi.tmem
      fun _ _ hrm => Safety.record_fault_free hpre hX hi.cluster hi.rings hi.tmem hi.async
        (tableInit hpre hX hi.cluster hi.tmem hi.init hi.rings hi.async)
        (Rings.ring_fault_free hpre hX hi.rings hi.tmem
          (InitFirst.ringInit hpre hX hi.cluster hi.tmem hi.init hi.rings))
        (fun cta _ hrec => TmemAlloc.fault_free hpre hX hi.tmem
          (HsInitProof.hsInit hpre hX hi.cluster hi.tmem hi.init cta) hrec)
        hother hrm
  valueCtx hpre hX hi.score hi.oacc hi.tc hi.tcmma hi.p2 hh
    (mmaLive hpre hX hi.score hi.oacc hi.tc hi.tmem hlt.2.2.1) hp.smemElements hi.floats
    (Cover.corrCover hrc hi.score hi.oacc hi.tc hi.tcmma hi.cover hh.sFull hh.oFull)
    (tmemLive hpre hX hi.score hi.oacc hi.tc hi.tmem hlt.2.2.1 hlt.2.2.2) hsg
    (Cover.softCover hpre hi.score hi.tc hi.tcmma hi.cover hh.sFull)
    fun hh h8 h12 he hsl => Floats.stats_floats hpre hX hi.stats hi.floats hi.tmem hU hsoft
      (statsAsync hX hi.rings hi.output hi.tmem hi.mmaReads) hh h8 h12 he hsl

/-- **Every Tensor Memory load returns single-precision floats**, from the context of the MMA
values. -/
theorem loadFloats_of {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (hi : ThreadInputs P L X)
    (hp : ProtocolPremises L X) : Safety.LoadFloats L X :=
  have hV := valueCtx_of hpre hX hi hp
  have hv : ∀ {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → TcMma.CompletedValues L asms X i := TcMmaSources.mmaValues hV
  Safety.loadFloats hX hi.score hi.floats (Floats.loadSources hpre hX hi.score hi.oacc hV.pReady
    hV.p2Gate hV.sFull hV.oReady hV.softCover hV.corrCover hv hV.tmemLive)

/-- **Every correction `ld.shared` returns the bytes of a single-precision float.** -/
theorem statsFloats_of {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (hi : ThreadInputs P L X)
    (hp : ProtocolPremises L X) : Safety.StatsFloats L X :=
  have hsoft : Stats.SoftArrives L X := Stats.softArrives hpre hX hi.stats hi.older
  have hin := InitFirst.statsInit hpre hX hi.cluster hi.tmem hi.init hi.stats
  Safety.statsFloats hpre hX hi.stats hi.floats hi.tmem
    (Stats.statsCredit hpre hX hi.stats hi.tmem hin hsoft hi.spin) hsoft
    (statsAsync hX hi.rings hi.output hi.tmem hi.mmaReads)
    fun hg hw hld => TcMmaSources.softLoads_f32 (valueCtx_of hpre hX hi hp) hg hw hld

/-- **No consistent execution is unsafe**, given the facts not yet proved. -/
theorem safe_goal {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hR : SafeRemaining P L mem0) : SafeGoal kernel asms L mem0 := by
  refine ⟨Safety.tc_group_uniform, fun X hX hu => ?_⟩
  obtain ⟨hi, hp⟩ := hR X hX
  have hsoft : Stats.SoftArrives L X := Stats.softArrives hpre hX hi.stats hi.older
  have hbo := baseOrdered' hpre hX hi.rings hi.output hi.tmem hi.mmaReads hi.stats hi.tmemLife
    hi.async hi.older
  have hbr : TmemAlloc.BaseRead L X := BaseWord.baseRead hpre hX hi.stats hi.tmem hi.tmemLife
    hi.async hi.older hi.rings hi.output hi.mmaReads hbo
  have hring := Rings.ring_ordered hpre hX hi.rings hi.tmem
    (InitFirst.ringInit hpre hX hi.cluster hi.tmem hi.init hi.rings) hi.ringCopies hi.output
    hi.older
  have hin := InitFirst.statsInit hpre hX hi.cluster hi.tmem hi.init hi.stats
  have hout := InitFirst.outputInit hpre hX hi.cluster hi.tmem hi.init hi.output
  have hU := Stats.statsCredit hpre hX hi.stats hi.tmem hin hsoft hi.spin
  have hH := Output.outputHandoff hpre hX hi.output hi.tmem hout hi.spin
  have hsa := stagingAsync hX hi.rings hi.output hi.tmem hi.mmaReads
  have hoo := outputOrdered hpre hX hi.rings hi.tmem hi.async hi.ringCopies hi.output hi.store
    hi.older hH hsa
  have hstats := Stats.stats_ordered hpre hX hi.stats hU
    (statsAsync hX hi.rings hi.output hi.tmem hi.mmaReads)
  have hstage := Output.staging_ordered hpre hX hi.output hH hsa
  have hres := TmemAlloc.resource_ok hpre hX hi.tmem hbr
  have hrc := routeCtx hpre hX hi.route hi.pready hi.p2 hi.sfull hi.ofull hi.stats hi.tmem
    hi.init hi.cluster hsoft hi.spin
  have hh := handoffs hrc hi.score
  have hother := otherFaultFree hrc hi.cluster hi.async hi.output hi.spare
  obtain ⟨hab, hpc, hmd, hwd⟩ := tmemLifetime hpre hX hi.stats hi.score hi.oacc hi.tc hi.tmem
    hi.init hi.cluster hi.tmemLife hh.oFull
  have hlive : TcMmaSources.MmaLive L X := mmaLive hpre hX hi.score hi.oacc hi.tc hi.tmem hmd
  have hcc : Floats.CorrCover L X :=
    Cover.corrCover hrc hi.score hi.oacc hi.tc hi.tcmma hi.cover hh.sFull hh.oFull
  have htl : Floats.TmemLive L X := tmemLive hpre hX hi.score hi.oacc hi.tc hi.tmem hmd hwd
  have hV := valueCtx_of hpre hX hi hp
  have hstf : Safety.StatsFloats L X :=
    Safety.statsFloats hpre hX hi.stats hi.floats hi.tmem hU hsoft
      (statsAsync hX hi.rings hi.output hi.tmem hi.mmaReads)
      fun hg hw hld => TcMmaSources.softLoads_f32 hV hg hw hld
  have hT := tcOrders hi.score hi.oacc hh.sFull hh.pReady hh.p2Gate hh.oReady
  have hv : ∀ {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → TcMma.CompletedValues L asms X i := TcMmaSources.mmaValues hV
  have hload : Floats.LoadSources L X := Floats.loadSources hpre hX hi.score hi.oacc hh.pReady
    hh.p2Gate hh.sFull
    hh.oReady (Cover.softCover hpre hi.score hi.tc hi.tcmma hi.cover hh.sFull)
    hcc hv htl
  rcases hu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h
  · exact Safety.no_ub hX hi.tc (baseZero hpre hX hi.tmem hbr)
      (Safety.loadFloats hX hi.score hi.floats hload)
      hstf
      (Safety.shflUniform hX hi.floats) h
  · exact Safety.no_unalloc hpre hi.sharedPlaced hi.globalPlaced
      (Safety.mbar_allocated hpre hX hi.async) h
  · exact Safety.no_race hi.sharedPlaced hbo hstats hstage (hring.mono fun _ => q_rings)
      (hring.mono fun _ => kv_rings) hi.globalWrites hoo h
  · exact Safety.no_mixed hi.sharedPlaced hbo hstats hstage (hring.mono fun _ => q_rings)
      (hring.mono fun _ => kv_rings) hi.globalWrites hoo h
  · exact Safety.no_barMismatch hi.stats h
  · exact tmaSafe hpre hX hi.cluster hi.rings hi.tmem hi.async hi.init hi.sharedPlaced
      hother h
  · refine h (TcMma.sourceSafe_iff.mpr
      ⟨Safety.tc_supported hi.score (softLoads hload) (corrLoads hload), ?_⟩)
    exact Safety.sources_acc_a (TcMmaSources.accSources hV)
      (aSources hpre hi.score hi.oacc hi.tc hh.pReady hh.p2Gate hh.sFull
        (TcMmaSources.pvAStoresAt hpre hX hi.score hi.tc hi.tcmma hi.p2 hh.pReady hh.p2Handoff
          hlive))
  · exact Safety.no_assumption_ub h
  · obtain ⟨htcd, htcx⟩ := Safety.no_tcMismatch hi.thread hX hi.warp
    obtain ⟨hcld, hclx⟩ := ClusterStart.no_cluster_mismatch hX hi.cluster
    rcases (alignedMismatch_iff L).mp h with (h | h) | (h | h) | (h | h) | (h | h) | (h | h)
    · exact htcd h
    · exact htcx h
    · exact Safety.no_barDivergent hi.stats h
    · exact Safety.no_barExited hX hi.stats h
    · exact hcld h
    · exact hclx h
    · exact no_setMaxReg_divergent hX hi.reg h
    · exact no_setMaxReg_exited hX hi.reg h
    · obtain ⟨g, i, pc, op, own, recv, n, hget, -⟩ := AlignedClass.divergent_matrix_old L h
      exact no_matrix hX hget
    · obtain ⟨g, i, pc, op, own, recv, n, hget, -⟩ := AlignedClass.exited_matrix_old L h
      exact no_matrix hX hget
  · exact lifetimeSafe' hpre hX hi.rings hi.ringCopies hi.tmem hi.score hi.stats hi.output
      hi.cluster hi.async hi.init hi.exit hi.ofull hi.sfull hh
      (Lifetime.selectedPerformed hX) hi.spin h
  · exact Safety.no_clcUnsafe hi.tmem h
  · exact tensorSafe hpre hX hi.rings hi.async hi.ringCopies h
  · exact Safety.no_tensorStoreUnsafe hX hi.output hi.tmem h
  · exact tensorAllocSafe hpre hX hi.rings hi.ringCopies hi.async h
  · exact hres.1 h
  · exact hres.2 h
  · obtain ⟨e, pc, m, q, ok, acq, sc, he, hns, -⟩ := h
    exact hns (poll_spins hX he)
  · exact Safety.no_access_unsafe hpre hX hi.score hi.oacc hi.tc hi.tmem hab hpc hmd hwd h
  · exact Safety.no_commit_unsafe hpre hX hi.tc h
  · exact Safety.no_writes_unsafe hpre hi.score hi.oacc hT h
  · exact Safety.no_instruction_unsafe hi.score hi.tc hi.tcmma hv h
  · exact Safety.no_reads_unsafe hi.score hi.oacc hi.tc hT
      (fun hw hx hthr hlt => TcMmaSources.scoreDonePv hpre hi.score hi.tc hi.route hh.sFull
        hh.pReady hw hx hthr hlt) h
  · exact Safety.no_reg_unsafe hpre hX hi.reg h.unsafe
  · exact Stats.not_ctaBarFault hpre hX hi.stats hU hi.bar2ArriveLast h
  · exact ClusterStart.no_cluster_fault hX hi.cluster h
  · exact Safety.no_warpDivergent (Safety.poll_synced hi.thread hX hi.warp) h
  · exact not_matrixUnsafe_of_none L (fun e ev he => no_matrix_ev hX he) h
  · exact no_mbarUninit hpre hX hi.cluster hi.rings hi.tmem hi.async hi.ringCopies hi.init
      hi.tc h

/-- **The conflicts outside O are ordered**, for every consistent execution, given the facts not
yet proved: each shared region by its protocol, and a global byte outside O has no writer. -/
theorem outside_ordered {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hR : SafeRemaining P L mem0) :
    ∀ X, Consistent L kernel asms mem0 X →
      ConflictsOrdered L X fun l => ¬ Safety.InTensor P P.oBase P.sq l := by
  intro X hX
  obtain ⟨hi, -⟩ := hR X hX
  have hsoft : Stats.SoftArrives L X := Stats.softArrives hpre hX hi.stats hi.older
  have hbo := baseOrdered' hpre hX hi.rings hi.output hi.tmem hi.mmaReads hi.stats hi.tmemLife
    hi.async hi.older
  have hring := Rings.ring_ordered hpre hX hi.rings hi.tmem
    (InitFirst.ringInit hpre hX hi.cluster hi.tmem hi.init hi.rings) hi.ringCopies hi.output
    hi.older
  have hin := InitFirst.statsInit hpre hX hi.cluster hi.tmem hi.init hi.stats
  have hout := InitFirst.outputInit hpre hX hi.cluster hi.tmem hi.init hi.output
  have hU := Stats.statsCredit hpre hX hi.stats hi.tmem hin hsoft hi.spin
  have hH := Output.outputHandoff hpre hX hi.output hi.tmem hout hi.spin
  have hsa := stagingAsync hX hi.rings hi.output hi.tmem hi.mmaReads
  exact Safety.outside_ordered hi.sharedPlaced hbo
    (Stats.stats_ordered hpre hX hi.stats hU (statsAsync hX hi.rings hi.output hi.tmem hi.mmaReads))
    (Output.staging_ordered hpre hX hi.output hH hsa) (hring.mono fun _ => q_rings)
    (hring.mono fun _ => kv_rings) hi.globalWrites

end
end PTX.Kernels.FlashAttn4Fwd.Proof
