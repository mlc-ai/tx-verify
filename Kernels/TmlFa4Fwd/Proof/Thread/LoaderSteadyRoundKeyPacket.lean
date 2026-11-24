-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundKeyPairs
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerReloadProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyOperandReload
import all Kernels.TmlFa4Fwd.Proof.LoaderSteadyOperandReload
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringSwizzle
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part023

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The frame before the second K pair: the lower pointer words, the stage offset, the even
destination base, the packed carry and the size of the first pair. -/
def steadyRoundKeySecondFrame (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  let tid := warpLane l g lane%l.block
  let stage := steadyKeyStage round
  steadyWords false 0 (steadyRoundKeyPointer p l g batch round lane 0) ++
    ([(2160,b32 (32768*stage)),(2161,b32 (kvCopyAddress l.sharedBase stage tid 0 false))] ++
      (steadyRoundKeyPacked p l g batch round lane ++ steadyKeySizes 1))

set_option maxRecDepth 4096 in
/-- The K prelude computes both swizzled destination bases and the residual row count, and
compares the first row. -/
private theorem steadyRoundKeyPreludeOfSaved {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g batch round shuffles votes : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1451
      (fun lane => [(9539,b64 1),(779,.pred false)] ++ steadyRoundKeyCarry p l g batch round lane)
      shuffles votes ends) :
    ∃ ready : SchedulerWarpReached l X g 1469
        (fun lane => [(212,Value.pred true)] ++ steadyRoundKeyPacked p l g batch round lane)
        shuffles votes ends, ready.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let P := [(9539,b64 1),(779,.pred false)] ++ steadyRoundKeyCarry p l g batch round lane
  let tile := steadyRoundTile p l g batch round
  let res := steadyRoundKeyResidual p l g batch round lane
  have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hLive := steadyRoundKeyLive hp (lane := lane) hb hLo hHi hTrips 0
  have hLen := (hp.lengths batch hb).2.2
  have hs := cur.checkpoint lane hl
  have hP : Holds (cur.state lane).regs P := hs.2.2.2.2
  have hIn : At (cur.state lane) 1451 (recurringSwizzleInputs l tid 2 ++ P) :=
    hs.mono ((holds_append ..).mpr ⟨⟨holds_lookup hP rfl,holds_lookup hP rfl,
      holds_lookup hP rfl,trivial⟩,hP⟩)
  obtain ⟨a,ha,hA⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (show Seg kernel [] l t 13 1451 (recurringSwizzleInputs l tid 2) 1464
      (recurringSwizzleFacts l tid 2) from recurringSwizzleCore hTid hp.shared.2.1 2) hIn
  let Q := recurringSwizzleFacts l tid 2 ++ P
  have hQ : Holds a.regs Q := hA.2.2.2.2
  have hA' : At a 1464 ([(1144,b32 tile),(1145,b32 (128*tile)),(1146,b32 (tid/8%8)),
      (1086,b32 (p.kLength batch))] ++ Q) :=
    hA.mono ⟨holds_lookup hQ rfl,holds_lookup hQ rfl,holds_lookup hQ rfl,holds_lookup hQ rfl,hQ⟩
  have hRowLive : 128*tile+tid/8%8 < p.kLength batch := by
    have h := hLive.1
    simp only [steadyRoundKeyResidual] at h
    simp only [tile,tid,t]
    omega
  obtain ⟨b,hbRun,hB⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (steadyKeyCopyResidualCore (l := l) (g := t) hRowLive (by omega)) hA'
  have hB' : At b 1468 ([(2155,b32 res)] ++ steadyRoundKeyPacked p l g batch round lane) := by
    have h := hB.2.2.2.2
    exact hB.mono ⟨h.1,h.1,h.2.1,h.2.2.1,h.2.2.2.2.2⟩
  obtain ⟨c,hcRun,hC⟩ := roundStraightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl
    (liveKeyCompareCore (l := l) (g := t) (steadyKeyCompareCode 0) hLive.1 hLive.2) hB'
  exact ⟨c,run_rtg (run_comp ha (run_comp hbRun hcRun)),hC⟩

theorem steadyKeyReloadAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (slot : Fin 2) :
    l.localBase+32+(steadyPointerReload false slot).offset < 2^64 ∧
      (l.localBase+32+(steadyPointerReload false slot).offset)%8 = 0 := by
  have h := hp.localMemory
  have hs := slot.isLt
  change l.localBase+32+8*slot.val < 2^64 ∧ (l.localBase+32+8*slot.val)%8 = 0
  omega

set_option maxRecDepth 4096 in
/-- The first two steady K pairs establish both destination bases and issue their four
vectors. The lane's private cells are preserved. -/
theorem steadyRoundKeyFirstPairsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round shuffles votes : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1451
      (fun lane => [(9539,b64 1),(779,.pred false)] ++ steadyRoundKeyCarry p l g batch round lane)
      shuffles votes ends)
    (hSaved : ∀ lane < 32, PrimingCellValue X (warpLane l g lane) (cur.pos lane) 1447
      (pointerSaveAccess l (warpLane l g lane) 2 0)
      (b64 (steadyRoundKeyPointer p l g batch round lane 0)).toBytes) :
    ∃ done : SchedulerWarpReached l X g (steadyKeyNextPc 2)
        (fun lane => steadyRoundKeyGroupFrame p l g batch round lane 0 2) (shuffles+4) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => steadyRoundKeyPointer p l g batch round lane 0
  let stage := steadyKeyStage round
  let Pk := steadyRoundKeyPacked p l g batch round
  have hPtr (lane : Nat) := steadyRoundKeyPointerBounds hp (round := round) (lane := lane)
    hb hLo hHi 0
  have hStage := steadyKeyStage_lt round
  obtain ⟨pre,hPre⟩ := steadyRoundKeyPreludeOfSaved hp hb hLo hHi hTrips cur
  -- the lower pointer reload
  obtain ⟨rel,_,hRel⟩ := (steadyPointerReload false 0).warpReadPreservingOfMaximal hp hMax hg
    (by decide) (steadyPointerReloadCode false 0) (steadyKeyReloadAddress hp 0).1
    (steadyKeyReloadAddress hp 0).2 (by decide) ptr (fun lane _ => (hPtr lane).1) pre
    (fun lane _ => by
      simp [steadyPointerReload,pointerReloadBase,steadySpillSite,steadyRoundKeyPacked,
        steadyRoundKeyCarry,steadyRoundTileFrame,steadyRoundFrame,steadyCacheHeadFrame,
        steadyRoundCarry,warmRoundCarry,openingWarmFrame,warmStartFrame,warmPageRoots,
        warmLaneRoots])
    (fun lane _ pair hm => by
      have h : (([(212,Value.pred true)] ++ Pk lane).map Prod.fst).all
          (fun r => decide (r ≠ 2156 ∧ r ≠ 2157)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm)))
    (fun lane hl => by rw [hPre]; exact hSaved lane hl)
  obtain ⟨w0,hW0⟩ := rel.advanceLocalWithPosition (pc' := steadyPairShufflePc false 0)
    (G := fun lane => steadyWords false 0 (ptr lane) ++ ((212,Value.pred true) :: Pk lane))
    (fun lane hl => ⟨rel.state lane,.refl,rel.checkpoint lane hl⟩)
  -- pair zero
  obtain ⟨ex0,hEx0⟩ := steadyExchangeOfMaximal hp hMax hg false 0 ptr
    (fun lane _ fact hm => by
      have h : ((steadyWords false 0 (ptr lane) ++ (212,Value.pred true) :: Pk lane).map
          Prod.fst).all (fun r => decide (r ≠ 2158 ∧ r ≠ 2159)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))) w0
  let src0 := fun lane =>
    recurringSourceAddress (ptr (steadyPairSender lane 0)) (warpLane l g lane%l.block)
  obtain ⟨ready0,hReady0⟩ := ex0.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 2) 0)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 2) stage (warpLane l g lane%l.block)
      (src0 lane) 16 0 ++ steadyRoundKeySecondFrame p l g batch round lane) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      let E := steadyExchangeWords false 0 (ptr (steadyPairSender lane 0)) ++
        steadyWords false 0 (ptr lane) ++ (212,Value.pred true) :: Pk lane
      have hs := ex0.checkpoint lane hl
      have hE : Holds (ex0.state lane).regs E := hs.2.2.2.2
      have hPkE : Holds (ex0.state lane).regs (Pk lane) := ((holds_append ..).mp hE).2.2
      have hIn : At (ex0.state lane) 1472
          (steadyPairInputs false 0 (ptr (steadyPairSender lane 0)) tid ++ E) :=
        hs.mono ((holds_append ..).mpr ⟨⟨hE.1,hE.2.1,holds_lookup hPkE rfl,trivial⟩,hE⟩)
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl
        (show Seg kernel [] l t 2 1472
          (steadyPairInputs false 0 (ptr (steadyPairSender lane 0)) tid)
          1474 [(7782,b64 (src0 lane))] from
          steadyPairSourceCore (hPtr (steadyPairSender lane 0)).1 false 0) hIn
      have hEven : At u 1474 ([(7179,b32 stage),
          (1153,b32 (kvCopyAddress l.sharedBase 0 tid 0 false))] ++
          ([(7782,b64 (src0 lane))] ++ E)) :=
        have hEu : Holds u.regs E := hU.2.2.2.2.2
        have hPku : Holds u.regs (Pk lane) := ((holds_append ..).mp hEu).2.2
        hU.mono ⟨holds_lookup hPku rfl,holds_lookup hPku rfl,hU.2.2.2.2⟩
      obtain ⟨v,hv,hV⟩ := roundStraightFrameAll (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (recurringEvenSeedRun hp (g := t) (lane := tid) 2 hStage) hEven
      have hSel : At v 1476 ([(212,Value.pred true)] ++
          (recurringEvenFacts l 2 stage tid ++ ([(7782,b64 (src0 lane))] ++ E))) :=
        hV.mono ⟨hV.2.2.2.2.2.2.2.2.2.2.2.1,hV.2.2.2.2⟩
      obtain ⟨w,hw,hW⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl
        (liveKeySelectCore (l := l) (g := t) (steadyKeySelectCode 0)) hSel
      refine ⟨w,run_rtg (run_comp hu (run_comp hv hw)),?_⟩
      have hR := hW.2.2.2.2
      have hRest : Holds w.regs E := hR.2.2.2.2
      have hWords := ((holds_append ..).mp ((holds_append ..).mp hRest).1).2
      have hPk : Holds w.regs (Pk lane) := ((holds_append ..).mp hRest).2.2
      refine hW.mono ⟨hR.2.1,hR.2.2.2.1,hR.1,?_⟩
      exact (holds_append _ (steadyWords false 0 (ptr lane)) _).mpr ⟨hWords,hR.2.2.1,hR.2.1,
        (holds_append _ (Pk lane) _).mpr ⟨hPk,hR.1,trivial⟩⟩)
  obtain ⟨copied0,_,hCopied0⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 2) 0
    (by change stage+0 < 3; omega) src0 (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => steadySourceAligned (hPtr (steadyPairSender lane 0)).2)
    (fun _ _ => le_rfl) ready0
  -- pair one
  let N1 := fun lane =>
    [(2160,b32 (32768*stage)),
      (2161,b32 (kvCopyAddress l.sharedBase stage (warpLane l g lane%l.block) 0 false))] ++
      (Pk lane ++ steadyKeySizes 1)
  obtain ⟨m1,hM1⟩ := copied0.advanceLocalWithPosition (pc' := steadyPairShufflePc false 1)
    (G := fun lane => steadyWords false 1 (ptr lane) ++ ((213,Value.pred true) :: N1 lane)) (by
      intro lane hl
      have hs := copied0.checkpoint lane hl
      have hF : Holds (copied0.state lane).regs
          (steadyRoundKeySecondFrame p l g batch round lane) :=
        hs.2.2.2.2
      have hRes := steadyRoundKeyLive hp (lane := lane) hb hLo hHi hTrips 1
      have hN : Holds (copied0.state lane).regs (N1 lane) := ((holds_append ..).mp hF).2
      have hPk : Holds (copied0.state lane).regs (Pk lane) :=
        ((holds_append ..).mp ((holds_append ..).mp hN).2).1
      have hIn : At (copied0.state lane) 1479
          ([(2155,b32 (steadyRoundKeyResidual p l g batch round lane))] ++
            steadyRoundKeySecondFrame p l g batch round lane) :=
        hs.mono ⟨hPk.1,hF⟩
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl
        (liveKeyCompareCore (l := l) (g := warpLane l g lane) (steadyKeyCompareCode 1)
          hRes.1 hRes.2) hIn
      have hU' := hU.2.2.2.2.2
      exact ⟨u,run_rtg hu,hU.mono ⟨hU'.1,hU'.2.1,hU.2.2.2.2.1,hU'.2.2⟩⟩)
  obtain ⟨ex1,hEx1⟩ := steadyExchangeOfMaximal hp hMax hg false 1 ptr
    (fun lane _ fact hm => by
      have h : ((steadyWords false 1 (ptr lane) ++ (213,Value.pred true) :: N1 lane).map
          Prod.fst).all (fun r => decide (r ≠ 2162 ∧ r ≠ 2163)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))) m1
  let src1 := fun lane =>
    recurringSourceAddress (ptr (steadyPairSender lane 1)) (warpLane l g lane%l.block)
  obtain ⟨ready1,hReady1⟩ := ex1.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 2) 1)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 2) stage (warpLane l g lane%l.block)
      (src1 lane) 16 1 ++ steadyRoundKeyGroupFrame p l g batch round lane 0 2) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      let E := steadyExchangeWords false 1 (ptr (steadyPairSender lane 1)) ++
        steadyWords false 1 (ptr lane) ++ (213,Value.pred true) :: N1 lane
      have hs := ex1.checkpoint lane hl
      have hE : Holds (ex1.state lane).regs E := hs.2.2.2.2
      have hN : Holds (ex1.state lane).regs (N1 lane) := ((holds_append ..).mp hE).2.2
      have hPk : Holds (ex1.state lane).regs (Pk lane) :=
        ((holds_append ..).mp ((holds_append ..).mp hN).2).1
      have hIn : At (ex1.state lane) 1482
          (steadyPairInputs false 1 (ptr (steadyPairSender lane 1)) tid ++ E) :=
        hs.mono ((holds_append ..).mpr ⟨⟨hE.1,hE.2.1,holds_lookup hPk rfl,trivial⟩,hE⟩)
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl
        (show Seg kernel [] l t 2 1482
          (steadyPairInputs false 1 (ptr (steadyPairSender lane 1)) tid)
          1484 [(7784,b64 (src1 lane))] from
          steadyPairSourceCore (hPtr (steadyPairSender lane 1)).1 false 1) hIn
      have hOdd : At u 1484 ([(1152,b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),
          (2160,b32 (32768*stage))] ++ ([(7784,b64 (src1 lane))] ++ E)) :=
        have hEu : Holds u.regs E := hU.2.2.2.2.2
        have hNu : Holds u.regs (N1 lane) := ((holds_append ..).mp hEu).2.2
        have hPku : Holds u.regs (Pk lane) :=
          ((holds_append ..).mp ((holds_append ..).mp hNu).2).1
        hU.mono ⟨holds_lookup hPku rfl,hNu.1,hU.2.2.2.2⟩
      obtain ⟨v,hv,hV⟩ := roundStraightFrameAll (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl
        (recurringOddSeedRun hp (g := t) (lane := tid) 2 hStage) hOdd
      have hSel : At v 1485 ([(213,Value.pred true)] ++
          ([(2164,b32 (kvCopyAddress l.sharedBase stage tid 1 false))] ++
            ([(7784,b64 (src1 lane))] ++ E))) :=
        hV.mono ⟨hV.2.2.2.2.2.2.2.2.2.2.1,hV.2.2.2.2⟩
      obtain ⟨w,hw,hW⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl
        (liveKeySelectCore (l := l) (g := t) (steadyKeySelectCode 1)) hSel
      refine ⟨w,run_rtg (run_comp hu (run_comp hv hw)),?_⟩
      have hR := hW.2.2.2.2
      have hRest : Holds w.regs E := hR.2.2.2
      have hWords := ((holds_append ..).mp ((holds_append ..).mp hRest).1).2
      have hN' : Holds w.regs (N1 lane) := ((holds_append ..).mp hRest).2.2
      have hPk' : Holds w.regs (Pk lane ++ steadyKeySizes 1) := ((holds_append ..).mp hN').2
      refine hW.mono ⟨hR.2.1,hR.2.2.1,hR.1,?_⟩
      refine (holds_append _ (steadyWords false 0 (ptr lane)) _).mpr
        ⟨hWords,hN'.1,hN'.2.1,hR.2.1,?_⟩
      rw [show steadyKeySizes 2 = steadyKeySizes 1 ++ [(1155,b32 16)] from
        steadyKeySizes_succ 1,← List.append_assoc]
      exact (holds_append _ (Pk lane ++ steadyKeySizes 1) _).mpr ⟨hPk',hR.1,trivial⟩)
  obtain ⟨copied1,_,hCopied1⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 2) 1
    (by change stage+0 < 3; omega) src1 (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => steadySourceAligned (hPtr (steadyPairSender lane 1)).2)
    (fun _ _ => le_rfl) ready1
  refine ⟨copied1,fun lane hl pc cell data hCell => ?_⟩
  apply (hCopied1 lane hl).2
  rw [hReady1]
  apply (hEx1 lane hl).2
  rw [hM1]
  apply (hCopied0 lane hl).2
  rw [hReady0]
  apply (hEx0 lane hl).2
  rw [hW0]
  apply (hRel lane hl).2
  rw [hPre]
  exact hCell

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
