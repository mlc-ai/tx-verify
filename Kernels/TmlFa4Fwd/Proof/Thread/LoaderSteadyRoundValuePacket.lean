-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundValuePairs
import all Kernels.TmlFa4Fwd.Proof.LoaderSteadyOperandReload
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part026
import Kernels.TmlFa4Fwd.Flow.Code.Part027

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

private theorem steadyValueColumnCore {l : Launch} {g base tid : Nat} :
    Seg kernel [] l g 3 1635 (steadyPairInputs true 0 base tid) 1638
      [(7825,b64 (16*(tid%8)))] := by
  have hFit : 8*(tid%8) < 2^32 := by omega
  have hFit64 : 16*(tid%8) < 2^64 := by omega
  intro s hs
  change At s 1635 [(2200,b32 (base%2^32)),(2201,b32 (base/2^32)),(1147,b32 (8*(tid%8)))] at hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hFit,Nat.mod_eq_of_lt hFit64,
      show 8*(tid%8)*2 = 16*(tid%8) by omega]

private theorem steadyValueSourceAndColumn {l : Launch} {g base tid : Nat}
    (hBase : base < 2^64) :
    Seg kernel [] l g 3 1635 (steadyPairInputs true 0 base tid) 1638
      [(7826,b64 (recurringSourceAddress base tid)),(7825,b64 (16*(tid%8)))] := by
  intro s hs
  have hSrc := steadyPairSourceCore (l := l) (g := g) (tid := tid) hBase true 0
  change Seg kernel [] l g 3 1635 (steadyPairInputs true 0 base tid) 1638
    [(7826,b64 (recurringSourceAddress base tid))] at hSrc
  obtain ⟨u,hu,hU⟩ := hSrc s hs
  obtain ⟨v,hv,hV⟩ := steadyValueColumnCore (l := l) (g := g) (base := base) (tid := tid) s hs
  have he : v = u := Option.some.inj (hv.symm.trans hu)
  exact ⟨u,hu,hU.mono ⟨hU.2.2.2.2.1,he ▸ hV.2.2.2.2⟩⟩

theorem steadyValueReloadAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (slot : Fin 2) :
    l.localBase+(steadyPointerReload true slot).offset < 2^64 ∧
      (l.localBase+(steadyPointerReload true slot).offset)%8 = 0 := by
  have h := hp.localMemory
  have hs := slot.isLt
  change l.localBase+8*slot.val < 2^64 ∧ (l.localBase+8*slot.val)%8 = 0
  omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

set_option maxRecDepth 4096 in
/-- The first two steady V pairs establish the lane column and both destination bases and
issue their four vectors. The lane's private cells are preserved. -/
theorem steadyRoundValueFirstPairsOfMaximal {g batch round shuffles votes : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1632 (steadyRoundValueRest p l g batch round)
      shuffles votes ends)
    (hSaved : ∀ lane < 32, PrimingCellValue X (warpLane l g lane) (cur.pos lane) 1628
      (pointerSaveAccess l (warpLane l g lane) 3 0)
      (b64 (steadyRoundValuePointer p l g batch round lane 0)).toBytes) :
    ∃ done : SchedulerWarpReached l X g (steadyValueNextPc 2)
        (steadyRoundValueGroupFrame p l g batch round · 0) (shuffles+4) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => steadyRoundValuePointer p l g batch round lane 0
  let stage := steadyValueStage round
  let VR := steadyRoundValueRest p l g batch round
  have hPtr (lane : Nat) := steadyRoundValuePointerBounds hp (round := round) (lane := lane)
    hb hLo hHi 0
  have hStage := steadyValueStage_lt round
  obtain ⟨rel,_,hRel⟩ := (steadyPointerReload true 0).warpReadPreservingOfMaximal hp hMax hg
    (by decide) (steadyPointerReloadCode true 0) (steadyValueReloadAddress hp 0).1
    (steadyValueReloadAddress hp 0).2 (by decide) ptr (fun lane _ => (hPtr lane).1) cur
    (fun lane _ => by
      simp [steadyPointerReload,pointerReloadBase,steadySpillSite,steadyRoundValueRest,
        steadyRoundValueAcquired,steadyRoundValueCarry,steadyRoundKeyDone,steadyRoundKeyPacked,
        steadyRoundKeyCarry,steadyRoundTileFrame,steadyRoundFrame,steadyCacheHeadFrame,
        steadyRoundCarry,warmRoundCarry,openingWarmFrame,warmStartFrame,primingVScratchAbi])
    (fun lane _ pair hm => by
      have h : ((VR lane).map Prod.fst).all (fun r => decide (r ≠ 2198 ∧ r ≠ 2199)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm)))
    hSaved
  obtain ⟨w0,hW0⟩ := rel.advanceLocalWithPosition (pc' := steadyPairShufflePc true 0)
    (G := fun lane => steadyWords true 0 (ptr lane) ++ VR lane)
    (fun lane hl => ⟨rel.state lane,.refl,rel.checkpoint lane hl⟩)
  obtain ⟨ex0,hEx0⟩ := steadyExchangeOfMaximal hp hMax hg true 0 ptr
    (fun lane _ fact hm => by
      have h : ((steadyWords true 0 (ptr lane) ++ VR lane).map Prod.fst).all
          (fun r => decide (r ≠ 2200 ∧ r ≠ 2201)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))) w0
  let src0 := fun lane =>
    recurringSourceAddress (ptr (steadyPairSender lane 0)) (warpLane l g lane%l.block)
  let M1 := fun lane =>
    let tid := warpLane l g lane%l.block
    steadyWords true 0 (ptr lane) ++
      ([(7825,b64 (16*(tid%8))),(2202,b32 (32768*stage)),
        (2203,b32 (kvCopyAddress l.sharedBase stage tid 0 false))] ++ VR lane)
  obtain ⟨ready0,hReady0⟩ := ex0.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 3) 0)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 3) stage (warpLane l g lane%l.block)
      (src0 lane) 16 0 ++ M1 lane) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      let E := steadyExchangeWords true 0 (ptr (steadyPairSender lane 0)) ++
        steadyWords true 0 (ptr lane) ++ VR lane
      have hs := ex0.checkpoint lane hl
      have hE : Holds (ex0.state lane).regs E := hs.2.2.2.2
      have hVR : Holds (ex0.state lane).regs (VR lane) := ((holds_append ..).mp hE).2
      have hIn : At (ex0.state lane) 1635
          (steadyPairInputs true 0 (ptr (steadyPairSender lane 0)) tid ++ E) :=
        hs.mono ((holds_append ..).mpr ⟨⟨hE.1,hE.2.1,holds_lookup hVR rfl,trivial⟩,hE⟩)
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (steadyValueSourceAndColumn (l := l) (g := t) (tid := tid)
          (hPtr (steadyPairSender lane 0)).1) hIn
      have hEu : Holds u.regs E := hU.2.2.2.2.2.2
      have hVRu : Holds u.regs (VR lane) := ((holds_append ..).mp hEu).2
      have hEven : At u 1638 ([(1170,b32 stage),
          (1153,b32 (kvCopyAddress l.sharedBase 0 tid 0 false))] ++
          ([(7826,b64 (src0 lane)),(7825,b64 (16*(tid%8)))] ++ E)) :=
        hU.mono ⟨holds_lookup hVRu rfl,holds_lookup hVRu rfl,hU.2.2.2.2⟩
      obtain ⟨v,hv,hV⟩ := roundStraightFrameAll (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (recurringEvenSeedRun hp (g := t) (lane := tid) 3 hStage) hEven
      refine ⟨v,run_rtg (run_comp hu hv),?_⟩
      have hR := hV.2.2.2.2
      have hRest : Holds v.regs E := hR.2.2.2.2
      have hWords := ((holds_append ..).mp ((holds_append ..).mp hRest).1).2
      have hVRv : Holds v.regs (VR lane) := ((holds_append ..).mp hRest).2
      refine hV.mono ⟨hR.1,hR.2.2.1,holds_lookup hVRv rfl,?_⟩
      exact (holds_append _ (steadyWords true 0 (ptr lane)) _).mpr
        ⟨hWords,hR.2.2.2.1,hR.2.1,hR.1,hVRv⟩)
  obtain ⟨copied0,_,hCopied0⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 3) 0
    (by change stage+0 < 3; omega) src0 (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => steadySourceAligned (hPtr (steadyPairSender lane 0)).2)
    (fun _ _ => le_rfl) ready0
  -- pair one
  let N1 := fun lane =>
    let tid := warpLane l g lane%l.block
    [(7825,b64 (16*(tid%8))),(2202,b32 (32768*stage)),
      (2203,b32 (kvCopyAddress l.sharedBase stage tid 0 false))] ++ VR lane
  obtain ⟨m1,hM1⟩ := copied0.advanceLocalWithPosition (pc' := steadyPairShufflePc true 1)
    (G := fun lane => steadyWords true 1 (ptr lane) ++ N1 lane)
    (fun lane hl => ⟨copied0.state lane,.refl,copied0.checkpoint lane hl⟩)
  obtain ⟨ex1,hEx1⟩ := steadyExchangeOfMaximal hp hMax hg true 1 ptr
    (fun lane _ fact hm => by
      have h : ((steadyWords true 1 (ptr lane) ++ N1 lane).map Prod.fst).all
          (fun r => decide (r ≠ 2204 ∧ r ≠ 2205)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))) m1
  let src1 := fun lane =>
    recurringSourceAddress (ptr (steadyPairSender lane 1)) (warpLane l g lane%l.block)
  obtain ⟨ready1,hReady1⟩ := ex1.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 3) 1)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 3) stage (warpLane l g lane%l.block)
      (src1 lane) 16 1 ++ steadyRoundValueGroupFrame p l g batch round lane 0) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      let E := steadyExchangeWords true 1 (ptr (steadyPairSender lane 1)) ++
        steadyWords true 1 (ptr lane) ++ N1 lane
      have hs := ex1.checkpoint lane hl
      have hE : Holds (ex1.state lane).regs E := hs.2.2.2.2
      have hN : Holds (ex1.state lane).regs (N1 lane) := ((holds_append ..).mp hE).2
      have hIn : At (ex1.state lane) 1644
          (steadyPairInputs true 1 (ptr (steadyPairSender lane 1)) tid ++ E) :=
        hs.mono ((holds_append ..).mpr ⟨⟨hE.1,hE.2.1,hN.1,trivial⟩,hE⟩)
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl
        (show Seg kernel [] l t 2 1644
          (steadyPairInputs true 1 (ptr (steadyPairSender lane 1)) tid)
          1646 [(7828,b64 (src1 lane))] from
          steadyPairSourceCore (hPtr (steadyPairSender lane 1)).1 true 1) hIn
      have hEu : Holds u.regs E := hU.2.2.2.2.2
      have hNu : Holds u.regs (N1 lane) := ((holds_append ..).mp hEu).2
      have hVRu : Holds u.regs (VR lane) := ((holds_append ..).mp hNu).2
      have hOdd : At u 1646 ([(1152,b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),
          (2202,b32 (32768*stage))] ++ ([(7828,b64 (src1 lane))] ++ E)) :=
        hU.mono ⟨holds_lookup hVRu rfl,hNu.2.1,hU.2.2.2.2⟩
      obtain ⟨v,hv,hV⟩ := roundStraightFrameAll (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl
        (recurringOddSeedRun hp (g := t) (lane := tid) 3 hStage) hOdd
      refine ⟨v,run_rtg (run_comp hu hv),?_⟩
      have hR := hV.2.2.2.2
      have hRest : Holds v.regs E := hR.2.2
      have hWords := ((holds_append ..).mp ((holds_append ..).mp hRest).1).2
      have hNv : Holds v.regs (N1 lane) := ((holds_append ..).mp hRest).2
      have hVRv : Holds v.regs (VR lane) := ((holds_append ..).mp hNv).2
      refine hV.mono ⟨hR.1,hR.2.1,holds_mem hVRv (steadyKeySize_mem_valueRest 1 (by decide)),?_⟩
      exact (holds_append _ (steadyWords true 0 (ptr lane)) _).mpr
        ⟨hWords,hNv.1,hNv.2.1,hNv.2.2.1,hR.1,hVRv⟩)
  obtain ⟨copied1,_,hCopied1⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 3) 1
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
  exact (hRel lane hl).2 hCell

private theorem steadyRoundValueHalfOfMaximal {g batch round ordinal votes first : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2)
    (hFirst : 2 ≤ first ∧ 8*slot.val < first) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (steadyValueNextPc first)
      (steadyRoundValueGroupFrame p l g batch round · slot) ordinal votes ends) (count : Nat)
    (hLast : first+count ≤ 8*(slot.val+1)) :
    ∃ done : SchedulerWarpReached l X g (steadyValueNextPc (first+count))
        (steadyRoundValueGroupFrame p l g batch round · slot) (ordinal+2*count) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  induction count with
  | zero => exact ⟨cur,fun _ _ _ _ _ h => h⟩
  | succ k ih =>
    obtain ⟨mid,hMid⟩ := ih (by omega)
    have hSlot := slot.isLt
    let pair : Fin 16 := ⟨first+k,by omega⟩
    have hNo : pair.val ≠ 8 := by
      fin_cases slot
      · change first+k+1 ≤ 8 at hLast
        change first+k ≠ 8
        omega
      · have h := hFirst.2
        change 8 < first at h
        change first+k ≠ 8
        omega
    have hEntry : steadyValueNextPc (first+k) = steadyPairShufflePc true pair := by
      simp [steadyValueNextPc,hNo,pair,show first+k < 16 by omega]
    have hExit : packetPairPc (recurringPacketSite 3) pair+2 =
        steadyValueNextPc (first+(k+1)) := by
      have hp16 : pair.val < 16 := pair.isLt
      change packetPairPc (recurringPacketSite 3) pair+2 = steadyValueNextPc (pair.val+1)
      generalize pair = q at hNo hp16 ⊢
      fin_cases q <;> first | contradiction | decide
    obtain ⟨mid',hMid'⟩ := mid.advanceLocalWithPosition (pc' := steadyPairShufflePc true pair)
      (G := (steadyRoundValueGroupFrame p l g batch round · slot))
      (fun lane hl => ⟨mid.state lane,.refl,hEntry ▸ mid.checkpoint lane hl⟩)
    obtain ⟨done,hDone⟩ := steadyRoundValueLaterPairOfMaximal hp hMax hg hb hLo hHi slot pair
      (by dsimp [pair]; omega) ⟨by dsimp [pair]; omega,by dsimp [pair]; omega⟩ mid'
    have hN : ordinal+2*k+2 = ordinal+2*(k+1) := by omega
    rw [← hN,← hExit]
    refine ⟨done,fun lane hl _ _ _ h => hDone lane hl ?_⟩
    rw [hMid']
    exact hMid lane hl h

set_option maxRecDepth 4096 in
/-- All sixteen V pairs of steady round `round` issue their vectors; the warp reaches the V
commit. -/
theorem steadyRoundValueVectorsOfMaximal {g batch round shuffles votes : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1632 (steadyRoundValueRest p l g batch round)
      shuffles votes ends)
    (hSaved : ∀ lane < 32, ∀ slot : Fin 2,
      PrimingCellValue X (warpLane l g lane) (cur.pos lane) 1628
        (pointerSaveAccess l (warpLane l g lane) 3 slot)
        (b64 (steadyRoundValuePointer p l g batch round lane slot)).toBytes) :
    Nonempty (SchedulerWarpReached l X g 1734
      (steadyRoundValueGroupFrame p l g batch round · 1) (shuffles+32) votes ends) := by
  obtain ⟨first,hFirst⟩ := steadyRoundValueFirstPairsOfMaximal hp hMax hg hb hLo hHi cur
    (fun lane hl => hSaved lane hl 0)
  obtain ⟨low,hLow⟩ := steadyRoundValueHalfOfMaximal hp hMax hg hb hLo hHi (first := 2) 0
    (by decide) first 6 (by decide)
  let ptr := fun lane => steadyRoundValuePointer p l g batch round lane 1
  obtain ⟨reload,_,_⟩ := (steadyPointerReload true 1).warpReadPreservingOfMaximal hp hMax hg
    (by decide) (steadyPointerReloadCode true 1) (steadyValueReloadAddress hp 1).1
    (steadyValueReloadAddress hp 1).2 (by decide) ptr
    (fun lane _ => (steadyRoundValuePointerBounds hp (round := round) (lane := lane)
      hb hLo hHi 1).1) low
    (fun lane _ => by
      simp [steadyPointerReload,pointerReloadBase,steadySpillSite,steadyRoundValueGroupFrame,
        steadyRoundValueRest,steadyRoundValueAcquired,steadyRoundValueCarry,steadyRoundKeyDone,
        steadyRoundKeyPacked,steadyRoundKeyCarry,steadyRoundTileFrame,steadyRoundFrame,
        steadyCacheHeadFrame,steadyRoundCarry,warmRoundCarry,openingWarmFrame,warmStartFrame,
        primingVScratchAbi])
    (fun lane _ fact hm => by
      have h : ((steadyRoundValueGroupFrame p l g batch round lane 0).map Prod.fst).all
          (fun r => decide (r ≠ 2219 ∧ r ≠ 2220)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm)))
    (fun lane hl => hLow lane hl (hFirst lane hl (hSaved lane hl 1)))
  obtain ⟨high,_⟩ := reload.advanceLocalWithPosition (pc' := steadyPairShufflePc true 8)
    (G := (steadyRoundValueGroupFrame p l g batch round · 1)) (by
      intro lane hl
      have hs := reload.checkpoint lane hl
      have k := hs.2.2.2.2
      have hGF : Holds (reload.state lane).regs
          (steadyRoundValueGroupFrame p l g batch round lane 0) := k.2.2
      exact ⟨reload.state lane,.refl,hs.mono ⟨k.1,k.2.1,
        ((holds_append _ (steadyWords true (steadyKeySlotPair 0) _) _).mp hGF).2⟩⟩)
  obtain ⟨eight,_⟩ := steadyRoundValueLaterPairOfMaximal hp hMax hg hb hLo hHi 1 8 (by decide)
    ⟨by decide,by decide⟩ high
  obtain ⟨upper,_⟩ := eight.advanceLocalWithPosition (pc' := steadyValueNextPc 9)
    (G := (steadyRoundValueGroupFrame p l g batch round · 1))
    (fun lane hl => ⟨eight.state lane,.refl,eight.checkpoint lane hl⟩)
  obtain ⟨done,_⟩ := steadyRoundValueHalfOfMaximal hp hMax hg hb hLo hHi (first := 9) 1
    (by decide) upper 7 (by decide)
  exact ⟨done⟩
end

/-- The registers that the steady tail reads come from the V carry. -/
theorem steadyPublishedFrameOfValueCarry {R : Nat → Option Value} {p : Params} {l : Launch}
    {g batch round lane : Nat}
    (h : Holds R (steadyRoundValueCarry p l g batch round lane)) :
    Holds R (steadyCachePublishedFrame round
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
      (steadyRoundCarry p l g batch lane)) := by
  have hK : Holds R (steadyRoundKeyDone p l g batch round lane) := h.2.2
  have hF : Holds R (steadyRoundFrame p l g batch round lane) :=
    steadyHoldsOfSubset hK (fun _ hx => steadyRoundFrame_mem_keyDone hx)
  exact ⟨h.1,h.2.1,hF.1,hF.2.1,((holds_append ..).mp hF).2⟩

/-- Both packets of steady round `round` are published and the lane is at the steady tail. -/
structure SteadyRoundValuePublished (p : Params) (l : Launch) (X : Execution)
    (g batch round : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SteadyCachePublished l X g round
    (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
    (steadyRoundCarry p l g batch) shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+128+64*round
  published : ∀ lane < 32, ∃ i, i+1 = reached.pos lane ∧
    X.get (warpLane l g lane,i) = some ⟨reuseArrival 3,
      .asyncArrive (readyObject l (warpLane l g lane) (kvUseStage (cacheUseOfRound round+1)))
        true⟩

set_option maxRecDepth 4096 in
/-- After its K publication, a loader warp of steady round `round` passes the V gate, saves
both V pointers, issues the V packet, commits it and publishes its ready arrival. -/
theorem SteadyRoundKeyPublished.valuePublishedOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReleased : (cacheUseOfRound round+1)/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round+1)))
    (c : SteadyRoundKeyPublished p l X g batch round) :
    Nonempty (SteadyRoundValuePublished p l X g batch round) := by
  classical
  obtain ⟨acq,hAcq⟩ := c.valueAcquireOfMaximal hp hMax hFrame hg hw hb hLo hHi hReleased
  obtain ⟨saved,hSaved⟩ := steadyRoundValuePointersOfMaximal hp hMax hg hw hb hLo hHi acq hAcq
  obtain ⟨vec⟩ := steadyRoundValueVectorsOfMaximal hp hMax hg hb hLo hHi saved hSaved
  let use := cacheUseOfRound round+1
  let threads := warpLane l g
  let addr := l.sharedBase+8*(kvUseStage use).val
  let stop := fun lane => vec.pos lane+2
  let ev : Nat → Event := fun lane =>
    ⟨reuseArrival 3,.asyncArrive (readyObject l (threads lane) (kvUseStage use)) true⟩
  let es : Nat → List Event := fun lane => [⟨1734,.asyncCommit⟩,ev lane]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hStage := (kvUseStage use).isLt
  have hWidth : addr+(copyArrivalAddress (recurringPacketSite 3)).2 < 2^32 := by
    have h := hp.shared.2.1
    change l.sharedBase+8*(kvUseStage use).val+32 < 2^32
    omega
  have hAlign : addr%8 = 0 := by
    have h := hp.shared.1
    dsimp [addr]
    omega
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (threads lane)).drop (vec.pos lane) =
        es lane ++ (X.tr (threads lane)).drop (stop lane) ∧
      At u 1736 (steadyCachePublishedFrame round
        (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
        (steadyRoundCarry p l g batch lane)) ∧
      Run kernel Assumptions.all l (threads lane) {} ((X.tr (threads lane)).take (stop lane))
        (some u) ∧
      Run kernel Assumptions.all l (threads lane) u ((X.tr (threads lane)).drop (stop lane))
        (c.ends lane) ∧
      stop lane ≤ (X.tr (threads lane)).length ∧
      (stop lane = (X.tr (threads lane)).length → Step.Released l X (threads lane)) ∧
      X.get (threads lane,vec.pos lane+1) = some (ev lane) := by
    have hActor := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    have hs := vec.checkpoint lane hl
    have hG := hs.2.2.2.2
    have hVR : Holds (vec.state lane).regs (steadyRoundValueRest p l g batch round lane) :=
      ((holds_append ..).mp ((holds_append ..).mp hG).2).2
    have hVA : Holds (vec.state lane).regs (steadyRoundValueAcquired p l g batch round lane) :=
      hVR.2.2
    have hAt : At (vec.state lane) (copyCommitPc (recurringPacketSite 3))
        [((copyArrivalAddress (recurringPacketSite 3)).1,b32 addr)] :=
      hs.mono ⟨holds_lookup hVA rfl,trivial⟩
    obtain ⟨hc,ha,hPast,hTail⟩ := copyCommitAndArriveOfMaximal hMax
      (g := threads lane) hActor (recurringPacketSite 3) hAt hWidth hAlign
      (vec.localSteps lane hl) (vec.recorded lane hl) (vec.continuation lane hl)
      (vec.positive lane hl) (vec.bounded lane hl) (vec.released lane hl)
    have hLoc : (⟨.shared,threads lane/l.block,addr+32⟩ : Loc) =
        readyObject l (threads lane) (kvUseStage use) := by
      change _ = initObject l (threads lane/l.block) (readySlot (kvUseStage use))
      rw [readySlot_address]
    change X.get (threads lane,vec.pos lane+1) =
      some ⟨1735,.asyncArrive ⟨.shared,threads lane/l.block,addr+32⟩ true⟩ at ha
    rw [hLoc] at ha
    have hStop : stop lane = vec.pos lane+1+1 := rfl
    have hVC : Holds (vec.state lane).regs (steadyRoundValueCarry p l g batch round lane) :=
      ((holds_append ..).mp hVA).2
    have hFrameAt : At (next (next (vec.state lane))) 1736
        (steadyCachePublishedFrame round
          (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
          (steadyRoundCarry p l g batch lane)) :=
      hs.next.next.mono (steadyPublishedFrameOfValueCarry hVC)
    refine ⟨_,?_,hFrameAt,hPast,hTail,?_,?_,ha⟩
    · change (X.tr (threads lane))[vec.pos lane]? = some ⟨1734,.asyncCommit⟩ at hc
      change (X.tr (threads lane))[vec.pos lane+1]? = some (ev lane) at ha
      have hlo := List.getElem?_eq_some_iff.mp hc
      have hhi := List.getElem?_eq_some_iff.mp ha
      rw [List.drop_eq_getElem_cons hlo.1,hlo.2,List.drop_eq_getElem_cons hhi.1,hhi.2,hStop]
      rfl
    · rw [hStop]
      exact len_of_get ha
    · rw [hStop]
      exact releasedIfLast ha (by intro h; cases h)
  let _ : Inhabited TState := ⟨{}⟩
  choose! u hTrace hAt hPast hTail hBound hRelease hArrive using hLane
  have hOrd := vec.ordinals.advance es (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨c.shuffles+32,c.votes,c.ends,⟨⟨stop,u,u,hOrd,hTail,fun _ _ => .refl,hAt⟩,
    fun lane hl => (vec.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,by rw [c.rank]; omega,
    fun lane hl => ⟨vec.pos lane+1,rfl,hArrive lane hl⟩⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
