-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyFirstWordsKeep
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondReload
import Kernels.TmlFa4Fwd.Flow.Code.Part015

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

def warmKeyEvenCarry (l : Launch) (stage tid : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(7666,b64 (16*(tid%8))),(2002,b32 (32768*stage)),
    (2003,b32 (kvCopyAddress l.sharedBase stage tid 0 false))] ++ F

def warmFirstKeyFirstWords (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  warmKeyWords 0 (warmFirstKeyLanePointer p l g batch lane) ++ warmFirstKeyPacked p l g batch lane

private theorem firstWarmKeySourceAndColumn {l : Launch} {g base tid : Nat}
    (hBase : base < 2^64) :
    Seg kernel [] l g 3 1006 (warmKPairInputs 0 base tid)
      1009 [(7667,b64 (recurringSourceAddress base tid)),(7666,b64 (16*(tid%8)))] := by
  have hFit : 8 * (tid%8) < 2^32 := by omega
  intro s hs
  change At s 1006 [(2000,b32 (base%2^32)),(2001,b32 (base/2^32)),(1119,b32 (8*(tid%8)))] at hs
  have hWord := warmKPairSourceCore (l := l) (g := g) (tid := tid) hBase 0
  obtain ⟨u,hu,hU⟩ := hWord s hs
  have hColumn : Seg kernel [] l g 3 1006
      [(2000,b32 (base%2^32)),(2001,b32 (base/2^32)),(1119,b32 (8*(tid%8)))]
      1009 [(7666,b64 (16*(tid%8)))] := by
    intro a ha
    seg_fp ha using
      norm_bits [Nat.mod_eq_of_lt hFit,show 8*(tid%8)*2 = 16*(tid%8) by omega]
  obtain ⟨v,hv,hV⟩ := hColumn s hs
  have he : v = u := Option.some.inj (hv.symm.trans hu)
  exact ⟨u,hu,hU.mono ⟨hU.2.2.2.2.1,he ▸ hV.2.2.2.2⟩⟩

set_option maxRecDepth 4096 in
private theorem warmKeyEvenPrepared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch shuffles votes : Nat}
    (hPtr : ∀ lane < 32, warmFirstKeyLanePointer p l g batch lane < 2^64)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1006 (fun lane =>
      warmKeyExchangeWords 0 (warmFirstKeyLanePointer p l g batch (pointerBroadcastLane lane)) ++
        warmFirstKeyFirstWords p l g batch lane) shuffles votes ends) :
    ∃ ready : SchedulerWarpReached l X g 1012 (fun lane =>
      let tid := warpLane l g lane%l.block
      packetCopyFacts l (recurringPacketSite 0) 2 tid (warmFirstKeySource p l g batch lane) 16 0 ++
        warmKeyEvenCarry l 2 tid (warmFirstKeyFirstWords p l g batch lane))
      shuffles votes ends, ready.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let sender := pointerBroadcastLane lane
  let ptr := warmFirstKeyLanePointer p l g batch sender
  let src := warmFirstKeySource p l g batch lane
  let F := warmFirstKeyFirstWords p l g batch lane
  let S := [(7667,b64 src),(7666,b64 (16*(tid%8)))]
  have hSender : sender < 32 := by unfold sender pointerBroadcastLane; omega
  have hs := cur.checkpoint lane hl
  have hStart : At (cur.state lane) 1006 (warmKPairInputs 0 ptr tid ++ F) := by
    have hSplit := (holds_append ..).mp hs.2.2.2.2
    refine hs.mono ((holds_append ..).mpr ⟨?_,hSplit.2⟩)
    exact ⟨hSplit.1.1,hSplit.1.2.1,holds_lookup hSplit.2 rfl,trivial⟩
  have hSource : Seg kernel [] l t 3 1006 (warmKPairInputs 0 ptr tid) 1009 S :=
    firstWarmKeySourceAndColumn (hPtr sender hSender)
  obtain ⟨u,hu,hU⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSource hStart
  have hAt : At u 1009
      ([(7179,b32 2),(1992,b32 (kvCopyAddress l.sharedBase 0 tid 0 false))]++(S++F)) :=
    hU.mono ⟨holds_lookup hU.2.2.2.2 rfl,holds_lookup hU.2.2.2.2 rfl,hU.2.2.2.2⟩
  have hEven : Seg kernel [] l t 2 1009
      [(7179,b32 2),(1992,b32 (kvCopyAddress l.sharedBase 0 tid 0 false))] 1011
      (recurringEvenFacts l 0 2 tid) :=
    recurringEvenCore hp (g := t) 0 (by decide)
  obtain ⟨v,hv,hV⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hEven hAt
  let I := recurringEvenFacts l 0 2 tid ++ S ++ F
  have hSelect : Seg kernel [] l t 1 1011 [(169,.pred true)] 1012 [(1123,b32 16)] :=
    liveKeySelectCore Flow.code_1011
  obtain ⟨w,hw,hW⟩ := straightFrame (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hSelect
    (show At v 1011 ([(169,.pred true)]++I) from hV.mono
      ⟨holds_lookup hV.2.2.2.2 rfl,hV.2.2.2.2⟩)
  refine ⟨w,run_rtg (run_comp hu (run_comp hv hw)),hW.mono ?_⟩
  exact ⟨hW.2.2.2.2.2.1,hW.2.2.2.2.2.2.2.1,hW.2.2.2.2.1,
    hW.2.2.2.2.2.2.2.2.1,hW.2.2.2.2.2.2.1,hW.2.2.2.2.2.1,
    hW.2.2.2.2.2.2.2.2.2⟩

def warmKeySavedUpper (p : Params) (l : Launch) (X : Execution)
    (g batch lane index : Nat) : Prop :=
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let t := warpLane l g lane
  PrimingCellValue X t index 977 (pointerSaveAccess l t 0 1)
    (b64 (primingKRowPointer p batch head (warmFirstSlotRow p l g batch lane 1))).toBytes

theorem warmKeyLanePointerBounds {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch lane : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    let ptr := primingKRowPointer p batch head (warmFirstSlotRow p l g batch lane slot)
    ptr < 2^64 ∧ ptr%16 = 0 := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let row := warmFirstSlotRow p l g batch lane slot
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have h := sourceScratchPayload_live hp 0 (primingScratchPageBound hp (row := row) hb)
    (Nat.mod_lt row (by decide)) hh
  have hEq : sourceScratchPayload (primingScratchPage p batch row) (row%16)
      p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base+2*(head*p.kLayout.headStride)) = primingKRowPointer p batch head row :=
    h.1
  exact hEq ▸ h.2

set_option maxRecDepth 4096 in
/-- The first actual pair leaves the even stage base and the second private pointer live. -/
theorem WarmFirstPages.firstKeyPairCursorOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : WarmFirstPages p l X g batch) :
    ∃ done : SchedulerWarpReached l X g 1014
        (fun lane => warmKeyEvenCarry l 2 (warpLane l g lane%l.block)
          (warmFirstKeyFirstWords p l g batch lane)) (c.shuffles+2) c.votes c.ends,
      ∀ lane < 32, warmKeySavedUpper p l X g batch lane (done.pos lane) := by
  let ptr := warmFirstKeyLanePointer p l g batch
  let src := warmFirstKeySource p l g batch
  let F := warmFirstKeyPacked p l g batch
  have hPtr (lane : Nat) : ptr lane < 2^64 ∧ ptr lane%16 = 0 :=
    warmKeyLanePointerBounds hp (lane := lane) hb hLo hHi 0
  obtain ⟨words,hUpper⟩ := c.reloadKeyPointerPreservingOfMaximal hp hMax hg hw hb hLo hHi hTrips
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
      (hm : pair ∈ warmKeyWords 0 (ptr lane) ++ F lane) :
      pair.1 ≠ warmKShuffleOutput 0 ∧ pair.1 ≠ warmKShuffleOutput 0+1 := by
    have h : (((warmKeyWords 0 (ptr lane)) ++ F lane).map Prod.fst).all
        (fun r => decide (r ≠ 2000 ∧ r ≠ 2001)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨exchanged,hEx⟩ := warmKeyExchangeOfMaximal hp hMax hg 0 ptr hFresh words
  obtain ⟨ready,hReady⟩ := warmKeyEvenPrepared hp (fun lane _ => (hPtr lane).1) exchanged
  have hAlign (lane : Nat) : src lane%16 = 0 := by
    unfold src warmFirstKeySource recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    have hLocal : warmFirstKeyLanePointer p l g batch (pointerBroadcastLane lane)%16 = 0 :=
      (hPtr (pointerBroadcastLane lane)).2
    simp [Nat.add_mod,hLocal]
  obtain ⟨done,_,hDone⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 0) 0
    (by decide) src (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => hAlign lane) (fun _ _ => le_rfl) ready
  refine ⟨done,fun lane hl => (hDone lane hl).2 ?_⟩
  rw [hReady]
  exact (hEx lane hl).2 (hUpper lane hl)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
