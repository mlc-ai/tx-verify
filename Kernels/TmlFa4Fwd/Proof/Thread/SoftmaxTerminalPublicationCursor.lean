-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalDrainStart
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalIssueProgress
import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalPublish
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Correction Thread

def terminalSchedulerFrame (p : Params) (l : Launch) (g : Nat)
    (warp : Fin 8) (parity : Nat) : List (Nat × Value) :=
  (7258,b32 parity)::idleCarry l warp ++ RowDrainRole.softmax.frame p l g

/-- The terminal value, credit parity, and scheduler operands coexist at the end of the row. -/
def terminalRowFrame (p : Params) (l : Launch) (g : Nat)
    (warp : Fin 8) (parity : Nat) (sum maximum : Value) : List (Nat × Value) :=
  [(7257,sum),(7256,maximum),(5127,b32 (3+warp.val))] ++
    terminalSchedulerFrame p l g warp parity

private theorem terminalReload {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {warp : Fin 8} {parity : Nat} {sum maximum : Value}
    (ht : At t 7605 (terminalRowFrame p l g warp parity sum maximum)) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u 7607 ((652,.pred (decide (p.batch < laneOf l g))) ::
        (7151,b32 p.batch) :: terminalRowFrame p l g warp parity sum maximum) := by
  let F := terminalRowFrame p l g warp parity sum maximum
  let v := next (setReg t 7151 (b32 p.batch))
  obtain ⟨hWord,hParam⟩ := hp.values (19,p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [Loader.loaderParam19Name] at hParam
  have hv : run kernel Assumptions.all l g 1 t = some v := by
    apply run_local Flow.code_7605 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil (by
      rw [ht.1]
      decide) rfl,execLocalA_nil,execLocal_mem rfl]
    simp only [execMove,MemAccess.regs,List.filterMap_cons,List.filterMap_nil,id_eq,
      hParam,DType.width,MemExt.extendBits_same,pure,Except.pure]
    rw [truncBits_ofNat hWord (by decide)]
    rfl
  have hvAt : At v 7606 ((7151,b32 p.batch)::F) := ht.set (by
    simp [terminalRowFrame,terminalSchedulerFrame,idleCarry,RowDrainRole.frame,
      RowDrainRole.laneReg,RowDrainRole.ctaReg])
  have hs : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hb := hp.shape.2.1
  have hs31 : laneOf l g < 2^31 := by omega
  have hCompare : Seg kernel Assumptions.all l g 1 7606 ((7151,b32 p.batch)::F)
      7607 ((652,.pred (decide (p.batch < laneOf l g))) :: (7151,b32 p.batch) :: F) := by
    intro s hAt
    dsimp only [F,terminalRowFrame,terminalSchedulerFrame,idleCarry,RowDrainRole.frame,
      RowDrainRole.laneReg,RowDrainRole.ctaReg,List.cons_append,List.nil_append] at hAt ⊢
    seg_fp hAt using simp only [truncBits_ofNat (show laneOf l g < 2^32 by omega) (by decide),
      truncBits_ofNat (show p.batch < 2^32 by omega) (by decide),compare,Option.getD_some,
      RowDrainRole.signedWord hs31,RowDrainRole.signedWord hb,gt_iff_lt,Int.ofNat_lt]
  obtain ⟨w,hw,hW⟩ := hCompare.apply hvAt
  exact ⟨w,run_comp hv hw,hW⟩

private theorem firstTerminalStoreStops {l : Launch} {g : Nat} {s : TState} (hPc : s.pc = 7614) :
    Stops kernel Assumptions.all l g s := by
  have hCore := RowDrainRole.softmax.drainCore (l := l) (g := g) (s := s)
    (by rw [hPc]; decide) (by rw [hPc]; decide)
  rw [Stops,hCore]
  cases hf : s.fault with
  | none =>
    rw [out_event hf (hPc.symm ▸ Flow.code_7614) rfl rfl]
    exact ⟨_,rfl⟩
  | some f => exact ⟨.ub f,by simp [out,hf]⟩

private theorem terminalAddressKeepsScheduler {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g parity : Nat} {warp : Fin 8} {s t : TState}
    (hS : At s 7607 ((652,.pred (decide (p.batch < laneOf l g))) ::
      (7151,b32 p.batch) :: terminalSchedulerFrame p l g warp parity))
    (hRun : run kernel Assumptions.all l g 7 s = some t) (hPc : t.pc = 7614) :
    Holds t.regs ((652,.pred (decide (p.batch < laneOf l g))) ::
      (7151,b32 p.batch) :: terminalSchedulerFrame p l g warp parity) := by
  let span : RowDrainSpan := ⟨7607,7614,7733⟩
  let F := (652,.pred (decide (p.batch < laneOf l g))) ::
    (7151,b32 p.batch) :: terminalSchedulerFrame p l g warp parity
  have hAudit : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected (F.map Prod.fst) i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSegments : span.segmentKeeps (F.map Prod.fst) := by
    apply span.segmentKeeps_of_audit
    rfl
  have hAbove {a b : TState} {es : List Event}
      (h : TraceReach kernel Assumptions.all l g a es b) (hA : span.bypass ≤ a.pc) :
      span.bypass ≤ b.pc :=
    span.traceAboveExit h (by set_option maxRecDepth 100000 in decide +kernel) (by decide) hA
  obtain ⟨u,pre,tail,hCount,hu,_,hKeep,hReach⟩ := span.cut hp hAudit hSegments hAbove
    (TraceReach.of_local (run_rtg hRun)) (by rw [hS.1]; decide)
    (by rw [hS.2.1]; decide) (scratchStateOfClear ⟨hS.2.1,hS.2.2.1⟩) hS.2.2.2.2
    (by rw [hPc]; decide)
  have hPre : pre = [] := (List.append_eq_nil_iff.mp hCount.symm).1
  subst pre
  obtain ⟨v,hPrefix,hLocal⟩ := hReach.returnedPrefix
  have hv : v = s := by cases hPrefix; rfl
  subst v
  have hu' : u.pc = 7614 := hu
  obtain rfl := stop_unique hLocal (run_rtg hRun)
    (firstTerminalStoreStops hu') (firstTerminalStoreStops hPc)
  exact hKeep

/-- The reached terminal row produces the ready final publication with the guard,
the metadata pointer and the visit parity preserved for the scheduler drain. -/
theorem terminalPublicationCursorOfRow {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g parity : Nat} (hg : g < l.threads) (warp : Fin 8) (hWarp : warp.val = warpIndex l g)
    {sum maximum : Value} (hSum : sum.bytes = 4) (hMaxWord : maximum.bytes = 4)
    (c : OpeningTripCursor l X g 7605 (terminalRowFrame p l g warp parity sum maximum)) :
    X.Writes (g,c.pos) (statsAcc l g warp 2) sum.toBytes ∧
      X.Writes (g,c.pos+1) (statsAcc l g warp 3) maximum.toBytes ∧
      ∃ next : OpeningTripCursor l X g 7616 ((5127,b32 (3+warp.val)) ::
        RowDrainRole.softmax.guarded p l g ++ ((7258,b32 parity)::idleCarry l warp)),
        next.pos = c.pos+2 := by
  let F := [(5814,b32 (statsBase l g warp)),(7257,sum),(7256,maximum),(5127,b32 (3+warp.val))] ++
    (RowDrainRole.softmax.guarded p l g ++ ((7258,b32 parity)::idleCarry l warp))
  have hw : warpIndex l g < 8 := hWarp ▸ warp.isLt
  obtain ⟨s,hStart,hs⟩ := terminalReload hp c.checkpoint
  have hs' : At s 7607 [(1062,b32 warp.val),(2535,b32 l.sharedBase),(7257,sum),
      (7256,maximum),(5127,b32 (3+warp.val))] := by
    apply hs.mono
    have hGet (x : Nat × Value) (hx : x ∈ (652,.pred (decide (p.batch < laneOf l g))) ::
        (7151,b32 p.batch) :: terminalRowFrame p l g warp parity sum maximum) :=
      holds_mem hs.2.2.2.2 hx
    refine ⟨hGet (1062,b32 warp.val) ?_,hGet (2535,b32 l.sharedBase) ?_,hGet (7257,sum) ?_,
      hGet (7256,maximum) ?_,hGet (5127,b32 (3+warp.val)) ?_,trivial⟩ <;>
      simp [terminalRowFrame,terminalSchedulerFrame,idleCarry]
  obtain ⟨u,hRun,hu⟩ := terminalStatsReady hp warp hWarp hs'
  have hStable : At s 7607 ((652,.pred (decide (p.batch < laneOf l g))) ::
      (7151,b32 p.batch) :: terminalSchedulerFrame p l g warp parity) :=
    hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2⟩
  have hKeep := terminalAddressKeepsScheduler hp hStable hRun hu.1
  have hFrame : At u 7614 F := by
    apply hu.mono
    apply (holds_append ..).mpr
    refine ⟨hu.2.2.2.2,(holds_append ..).mpr ⟨?_,?_⟩⟩
    · exact ⟨hKeep.1,hKeep.2.1,hKeep.2.2.2.2.2⟩
    · exact ⟨hKeep.2.2.1,hKeep.2.2.2.1,hKeep.2.2.2.2.1,trivial⟩
  let ready : OpeningTripCursor l X g 7614 F :=
    ⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hFrame,c.recorded,c.remaining,
      c.localSteps.trans (run_rtg (run_comp hStart hRun))⟩
  obtain ⟨hWrite,second,hSecond⟩ := statsStoreOfMaximal hp hMax hg hw warp 2 hSum
    (by simp [F,statsStore]) (by simp [F,statsStore]) ready
  obtain ⟨hWrite',bar,hBar⟩ := statsStoreOfMaximal hp hMax hg hw warp 3 hMaxWord
    (by simp [F,statsStore]) (by simp [F,statsStore]) second
  have hAt : At bar.ready 7616 ((5127,b32 (3+warp.val)) ::
      RowDrainRole.softmax.guarded p l g ++ ((7258,b32 parity)::idleCarry l warp)) :=
    bar.checkpoint.mono bar.checkpoint.2.2.2.2.2.2.2
  rw [hSecond] at hWrite'
  refine ⟨hWrite,hWrite',⟨⟨bar.pos,bar.before,bar.ready,bar.ending,bar.positive,bar.bounded,
    bar.released,hAt,bar.recorded,bar.remaining,bar.localSteps⟩,?_⟩⟩
  rw [hBar,hSecond]

end PTX.Kernels.TmlFa4Fwd.Softmax
