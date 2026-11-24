-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyEvenProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part015

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

private theorem warmKeyFirstLive {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch lane : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (group : Fin 16) :
    8*group.val < warmFirstKeyResidual p l g batch lane ∧
      warmFirstKeyResidual p l g batch lane < 2^31 := by
  have hBound := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  refine ⟨?_,?_⟩
  · exact recurringKeyResidualLive (round := 0) group hTrips hBound (Nat.mod_lt _ (by decide))
  · unfold warmFirstKeyResidual
    omega

set_option maxRecDepth 4096 in
private theorem warmKeyOddPrepared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch shuffles votes : Nat}
    (hPtr : ∀ lane < 32, warmFirstKeyLanePointer p l g batch lane < 2^64)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1017 (fun lane =>
      let tid := warpLane l g lane%l.block
      let ptr := warmFirstKeyLanePointer p l g batch
      warmKeyExchangeWords 1 (ptr (warmKShuffleSender lane 1)) ++
        warmKeyWords 1 (ptr lane) ++ (170,.pred true) ::
          warmKeyEvenCarry l 2 tid (warmFirstKeyPacked p l g batch lane))
      shuffles votes ends) :
    ∃ ready : SchedulerWarpReached l X g 1021 (fun lane =>
      let tid := warpLane l g lane%l.block
      let ptr := warmFirstKeyLanePointer p l g batch
      packetCopyFacts l (recurringPacketSite 0) 2 tid
          (recurringSourceAddress (ptr (warmKShuffleSender lane 1)) tid) 16 1 ++
        warmKeyPairOperands l 2 tid 1 (ptr lane) (warmFirstKeyPacked p l g batch lane))
      shuffles votes ends, ready.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let ptr := warmFirstKeyLanePointer p l g batch
  let sender := warmKShuffleSender lane 1
  let src := recurringSourceAddress (ptr sender) tid
  let F := warmKeyWords 1 (ptr lane) ++
    warmKeyEvenCarry l 2 tid (warmFirstKeyPacked p l g batch lane)
  let G := (170,.pred true)::F
  have hSender : sender < 32 := by unfold sender warmKShuffleSender pointerBroadcastLane; omega
  have hs := cur.checkpoint lane hl
  have hStart : At (cur.state lane) 1017 (warmKPairInputs 1 (ptr sender) tid ++ G) := by
    refine hs.mono ((holds_append ..).mpr ⟨?_,?_⟩)
    · exact ⟨holds_lookup hs.2.2.2.2 rfl,holds_lookup hs.2.2.2.2 rfl,
        holds_lookup hs.2.2.2.2 rfl,trivial⟩
    · exact ⟨holds_lookup hs.2.2.2.2 rfl,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.2.2.2⟩
  have hSource : Seg kernel [] l t 2 1017 (warmKPairInputs 1 (ptr sender) tid)
      1019 [(7669,b64 src)] := warmKPairSourceCore (g := t) (hPtr sender hSender) 1
  obtain ⟨u,hu,hU⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSource hStart
  let H := (7669,b64 src)::G
  have hAt : At u 1019
      ([(1988,b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),(2002,b32 (32768*2))]++H) :=
    hU.mono ⟨holds_lookup hU.2.2.2.2 rfl,holds_lookup hU.2.2.2.2 rfl,hU.2.2.2.2⟩
  have hOdd : Seg kernel Assumptions.all l t 1 1019
      [(1988,b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),(2002,b32 (32768*2))] 1020
      [(2006,b32 (kvCopyAddress l.sharedBase 2 tid 1 false))] :=
    recurringOddSeedRun hp (g := t) 0 (by decide)
  obtain ⟨v,hv,hV⟩ := hOdd u (hAt.mono ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.1,trivial⟩)
  have hRun : run kernel [] l t 1 u = some v := by
    have hDecode := loaderOutCore (l := l) (g := t) (t := u)
      (by rw [hAt.1]; decide) (by rw [hAt.1]; decide)
    simpa only [run,tauStep,hDecode] using hv
  have hKeep := (loaderLinear (regs := H.map Prod.fst) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hRun).2
  have hHF := holdsSchedulerFrame hAt.2.2.2.2.2.2 hKeep (fun _ hm => List.mem_map_of_mem hm)
  let J := (2006,b32 (kvCopyAddress l.sharedBase 2 tid 1 false))::(7669,b64 src)::F
  have hJA : At v 1020 ([(170,.pred true)]++J) :=
    hV.mono ⟨hHF.2.1,hV.2.2.2.2.1,hHF.1,hHF.2.2⟩
  have hSelect : Seg kernel [] l t 1 1020 [(170,.pred true)] 1021 [(1124,b32 16)] :=
    liveKeySelectCore Flow.code_1020
  obtain ⟨w,hw,hW⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hSelect hJA
  refine ⟨w,run_rtg (run_comp hu (run_comp hv hw)),hW.mono ?_⟩
  have hHW := hW.2.2.2.2
  exact ⟨holds_lookup hHW rfl,holds_lookup hHW rfl,holds_lookup hHW rfl,
    holds_lookup hHW rfl,holds_lookup hHW rfl,holds_lookup hHW rfl,holds_lookup hHW rfl,
    holds_lookup hHW rfl,holds_lookup hHW rfl,hHW.2.2.2.2.2.2.2.2⟩

set_option maxRecDepth 4096 in
/-- The first odd pair installs the second destination base while preserving the upper pointer. -/
theorem WarmFirstPages.firstTwoKeyPairsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : WarmFirstPages p l X g batch) :
    ∃ done : SchedulerWarpReached l X g 1023
        (fun lane => warmKeyPairOperands l 2 (warpLane l g lane%l.block) 1
          (warmFirstKeyLanePointer p l g batch lane) (warmFirstKeyPacked p l g batch lane))
        (c.shuffles+4) c.votes c.ends,
      ∀ lane < 32, warmKeySavedUpper p l X g batch lane (done.pos lane) := by
  let ptr := warmFirstKeyLanePointer p l g batch
  let res := warmFirstKeyResidual p l g batch
  let P := warmFirstKeyPacked p l g batch
  let F := fun lane => warmKeyEvenCarry l 2 (warpLane l g lane%l.block)
    (warmFirstKeyFirstWords p l g batch lane)
  let G := fun lane => (170,.pred true)::warmKeyEvenCarry l 2 (warpLane l g lane%l.block) (P lane)
  have hPtr (lane : Nat) : ptr lane < 2^64 ∧ ptr lane%16 = 0 :=
    warmKeyLanePointerBounds hp (lane := lane) hb hLo hHi 0
  obtain ⟨afterEven,hUpper⟩ := c.firstKeyPairCursorOfMaximal hp hMax hg hw hb hLo hHi hTrips
  obtain ⟨maskStart,hMaskStart⟩ := afterEven.advanceLocalWithPosition (pc' := warmKeyMaskPc 1)
    (G := fun lane => (1997,b32 (res lane))::F lane) (by
      intro lane hl
      let hs := afterEven.checkpoint lane hl
      exact ⟨afterEven.state lane,.refl,hs.mono ⟨holds_lookup hs.2.2.2.2 rfl,hs.2.2.2.2⟩⟩)
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ F lane) :
      pair.1 ≠ 169+(1 : Fin 16).val := by
    have h : ((F lane).map Prod.fst).all (fun r => decide (r ≠ 170)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨masked,hMasked⟩ := warmKeyMaskOfReached 1 res
    (fun lane _ => (warmKeyFirstLive hp (lane := lane) hb hLo hHi hTrips 1).1)
    (fun lane _ => (warmKeyFirstLive hp (lane := lane) hb hLo hHi hTrips 1).2)
    hFresh maskStart
  obtain ⟨shuffle,hShuffle⟩ := masked.advanceLocalWithPosition (pc' := warmKShufflePc 1)
    (G := fun lane => warmKeyWords 1 (ptr lane) ++ G lane) (by
      intro lane hl
      let hs := masked.checkpoint lane hl
      refine ⟨masked.state lane,.refl,hs.mono ?_⟩
      exact ⟨holds_lookup hs.2.2.2.2 rfl,holds_lookup hs.2.2.2.2 rfl,hs.2.2.2.2.1,
        hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.2.2.2.2.2⟩)
  have hFresh' (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
      (hm : pair ∈ warmKeyWords 1 (ptr lane) ++ G lane) :
      pair.1 ≠ warmKShuffleOutput 1 ∧ pair.1 ≠ warmKShuffleOutput 1+1 := by
    have h : ((warmKeyWords 1 (ptr lane) ++ G lane).map Prod.fst).all
        (fun r => decide (r ≠ 2004 ∧ r ≠ 2005)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨exchanged,hEx⟩ := warmKeyExchangeOfMaximal hp hMax hg 1 ptr hFresh' shuffle
  obtain ⟨ready,hReady⟩ := warmKeyOddPrepared hp (fun lane _ => (hPtr lane).1) exchanged
  let src := fun lane => recurringSourceAddress (ptr (warmKShuffleSender lane 1))
    (warpLane l g lane%l.block)
  have hAlign (lane : Nat) : src lane%16 = 0 := by
    unfold src recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    simp [Nat.add_mod,(hPtr (warmKShuffleSender lane 1)).2]
  obtain ⟨done,_,hDone⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 0) 1
    (by decide) src (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => hAlign lane) (fun _ _ => le_rfl) ready
  refine ⟨done,fun lane hl => (hDone lane hl).2 ?_⟩
  rw [hReady]
  apply (hEx lane hl).2
  rw [hShuffle,hMasked,hMaskStart]
  exact hUpper lane hl

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
