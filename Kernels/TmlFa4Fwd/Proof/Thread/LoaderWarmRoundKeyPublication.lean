-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundKeyPacket
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyHalfProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyPublicationProgress
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondReload
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Flow.CountTake
import Lemmas.Flow.NthEv
import Kernels.TmlFa4Fwd.Flow.Code.Part016
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader


def warmRoundGroupPointer (p : Params) (l : Launch) (g batch round lane : Nat) (slot : Fin 2) : Nat
    :=
  primingKRowPointer p batch ((assignedCoordinates p batch (g/l.block)).2/6)
    (warmRoundSlotRow p l g batch round lane slot)

/-- The K carry before group `k` of the given pointer slot, with the copy sizes of the
earlier groups. -/
def warmRoundKeyGroupFrame (p : Params) (l : Launch) (g batch round lane : Nat) (slot : Fin 2)
    (k : Nat) : List (Nat × Value) :=
  warmKeyPairOperands l (warmKeyStage round) (warpLane l g lane%l.block) (warmKeySlotGroup slot)
    (warmRoundGroupPointer p l g batch round lane slot)
    (warmRoundKeySized p l g batch round k lane)

/-- A later K pair issues both vectors and keeps the pair's size operand for the V packet. -/
theorem warmKeyLaterPairSizedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g stage shuffles votes : Nat} (hg : g < l.threads) (hStage : stage < 3)
    (group : Fin 16) (hLater : 2 ≤ group.val) (ptr : Nat → Nat)
    (hPtr : ∀ lane < 32, ptr lane < 2^64 ∧ ptr lane%16 = 0)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane,
      pair.1 ≠ warmKShuffleOutput group ∧ pair.1 ≠ warmKShuffleOutput group+1)
    (hFrame : ∀ lane < 32,
      ((kernel.code.drop (warmKShufflePc group+2)).take
        (packetPairPc (recurringPacketSite 0) group-(warmKShufflePc group+2))).all
        (fun i => ((F lane).map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (cur : SchedulerWarpReached l X g (warmKShufflePc group) (fun lane =>
      let t := warpLane l g lane
      warmKeyWords group (ptr lane) ++ warmKeyPairMask group ::
        warmKeyPairCarry l stage (t%l.block) (F lane))
      shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (packetPairPc (recurringPacketSite 0) group+2) (fun lane =>
      warmKeyPairOperands l stage (warpLane l g lane%l.block) group (ptr lane) (F lane) ++
        [(packetSizeReg (recurringPacketSite 0) group,b32 16)])
      (shuffles+2) votes ends,
      ∀ lane < 32,
        ∀ {pc : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
          PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let G := fun lane =>
    warmKeyPairMask group :: warmKeyPairCarry l stage (warpLane l g lane%l.block) (F lane)
  have hFresh' : ∀ lane < 32, ∀ pair ∈ warmKeyWords group (ptr lane) ++ G lane,
      pair.1 ≠ warmKShuffleOutput group ∧ pair.1 ≠ warmKShuffleOutput group+1 := by
    intro lane hl pair hMem
    let Lit := warmKeyWords group (ptr lane) ++
      warmKeyPairMask group :: warmKeyPairCarry l stage (warpLane l g lane%l.block) []
    have hSplit : warmKeyWords group (ptr lane) ++ G lane = Lit ++ F lane := by
      simp [G,Lit,warmKeyPairCarry,List.append_assoc]
    rw [hSplit] at hMem
    rcases List.mem_append.mp hMem with hm | hm
    · have h : (Lit.map Prod.fst).all
          (fun r => decide (r ≠ warmKShuffleOutput group ∧ r ≠ warmKShuffleOutput group+1)) =
          true := by fin_cases group <;> exact of_decide_eq_true rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
    · exact hFresh lane hl pair hm
  obtain ⟨exchanged,hEx⟩ := warmKeyExchangeOfMaximal hp hMax hg group ptr hFresh' cur
  obtain ⟨ready,hReady⟩ := warmKeyPairReadyAfterExchange group hLater ptr
    (fun lane hl => (hPtr lane hl).1) hFrame exchanged
  obtain ⟨ready',hReady'⟩ := retainPacketSize ready
  let src := fun lane =>
    recurringSourceAddress (ptr (warmKShuffleSender lane group)) (warpLane l g lane%l.block)
  have hAlign (lane : Nat) (hl : lane < 32) : src lane%16 = 0 := by
    have hSender : warmKShuffleSender lane group < 32 := by
      have hSlot := Nat.mod_lt group.val (by decide : 0 < 8)
      unfold warmKShuffleSender pointerBroadcastLane
      omega
    unfold src recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    simp [Nat.add_mod,(hPtr _ hSender).2]
  obtain ⟨done,_,hResult⟩ := packetPairWarpOfMaximal hp hMax hg
    (recurringPacketSite 0) group hStage src (fun _ => 16)
    (fun _ _ => Nat.mod_lt _ (by decide)) hAlign (fun _ _ => le_rfl) ready'
  refine ⟨done,fun lane hl => ?_⟩
  intro pc cell data hCell
  apply (hResult lane hl).2
  rw [hReady',hReady]
  exact (hEx lane hl).2 hCell

private theorem warmRoundKeyWordsForSlot (group : Fin 16) (slot : Fin 2) (base : Nat)
    (hRange : 8*slot.val ≤ group.val ∧ group.val < 8*(slot.val+1)) :
    warmKeyWords (warmKeySlotGroup slot) base = warmKeyWords group base := by
  fin_cases slot
  · change 0 ≤ group.val ∧ group.val < 8 at hRange
    have h : group.val < 8 := hRange.2
    simp [warmKeyWords,warmKShuffleInput,warmKeySlotGroup,h]
  · change 8 ≤ group.val ∧ group.val < 16 at hRange
    have h : ¬ group.val < 8 := Nat.not_lt_of_ge hRange.1
    simp [warmKeyWords,warmKShuffleInput,warmKeySlotGroup,h]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch round ordinal votes : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
include hp hMax hg hb hLo hHi hTrips

set_option maxRecDepth 100000 in
/-- Any reached noninitial group in either half executes its mask, both exchanges, and both
copies. All lane-local cells are preserved across the exact group slice. -/
theorem warmRoundKeyNextGroupOfMaximal (slot : Fin 2) (group : Fin 16) (hLater : 2 ≤ group.val)
    (hRange : 8*slot.val ≤ group.val ∧ group.val < 8*(slot.val+1)) (hNoReload : group.val ≠ 8)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmKeyNextGroupPc group.val)
      (fun lane => warmRoundKeyGroupFrame p l g batch round lane slot group.val)
        ordinal votes ends) :
    ∃ done : SchedulerWarpReached l X g (warmKeyNextGroupPc (group.val+1))
        (fun lane => warmRoundKeyGroupFrame p l g batch round lane slot (group.val+1))
        (ordinal+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => warmRoundGroupPointer p l g batch round lane slot
  let res := warmRoundKeyResidual p l g batch round
  let P := fun lane => warmRoundKeySized p l g batch round group.val lane
  let F := fun lane => warmRoundKeyGroupFrame p l g batch round lane slot group.val
  let G := fun lane => warmKeyPairMask group ::
    warmKeyPairCarry l (warmKeyStage round) (warpLane l g lane%l.block) (P lane)
  have hEntry : warmKeyNextGroupPc group.val = warmKeyMaskPc group := by
    simp [warmKeyNextGroupPc,group.isLt]
  have hMask : warmKeyMaskPc group+1 = warmKShufflePc group := by
    fin_cases group <;> first | decide | contradiction
  obtain ⟨start,hStart⟩ := cur.advanceLocalWithPosition (pc' := warmKeyMaskPc group)
    (G := fun lane => (1997,b32 (res lane))::F lane) (by
      intro lane hl
      have hs := cur.checkpoint lane hl
      refine ⟨cur.state lane,.refl,hEntry ▸ hs.mono ?_⟩
      exact ⟨holds_lookup hs.2.2.2.2 (by fin_cases slot <;> rfl),hs.2.2.2.2⟩)
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ F lane) :
      pair.1 ≠ 169+group.val := by
    have h : ((F lane).map Prod.fst).all (fun r => decide (r ≠ 169+group.val)) = true := by
      fin_cases group <;> first | contradiction | (fin_cases slot <;> exact of_decide_eq_true rfl)
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨masked,hMasked⟩ := warmKeyMaskOfReached group res
    (fun lane _ => (warmRoundKeyLive hp (lane := lane) hb hLo hHi hTrips group).1)
    (fun lane _ => (warmRoundKeyLive hp (lane := lane) hb hLo hHi hTrips group).2)
    hFresh start
  obtain ⟨shuffle,hShuffle⟩ := masked.advanceLocalWithPosition (pc' := warmKShufflePc group)
    (G := fun lane => warmKeyWords group (ptr lane) ++ G lane) (by
      intro lane hl
      let hs := masked.checkpoint lane hl
      have ht := hs.2.2.2.2
      have h' : Holds (masked.state lane).regs (warmKeyPairOperands l (warmKeyStage round)
          (warpLane l g lane%l.block) group (ptr lane) (P lane)) := by
        rw [warmKeyPairOperands,← warmRoundKeyWordsForSlot group slot (ptr lane) hRange]
        exact ht.2.2
      have hSplit := (holds_append ..).mp h'
      refine ⟨masked.state lane,.refl,hMask ▸ hs.mono ((holds_append ..).mpr ⟨hSplit.1,?_⟩)⟩
      exact ⟨ht.1,hSplit.2⟩)
  have hFresh' (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ P lane) :
      pair.1 ≠ warmKShuffleOutput group ∧ pair.1 ≠ warmKShuffleOutput group+1 := by
    have h : ((P lane).map Prod.fst).all (fun r =>
        decide (r ≠ warmKShuffleOutput group ∧ r ≠ warmKShuffleOutput group+1)) = true := by
      fin_cases group <;> exact of_decide_eq_true rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  have hFrame : ∀ lane < 32,
      ((kernel.code.drop (warmKShufflePc group+2)).take
        (packetPairPc (recurringPacketSite 0) group-(warmKShufflePc group+2))).all
        (fun i => ((P lane).map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    intro lane _
    fin_cases group <;> kernel_rfl
  obtain ⟨paired,hPaired⟩ := warmKeyLaterPairSizedOfMaximal hp hMax hg (warmKeyStage_lt round)
    group hLater ptr (fun lane _ => warmRoundKeyLanePointerBounds hp (lane := lane) hb hLo hHi slot)
    hFresh' hFrame shuffle
  have hNext : packetPairPc (recurringPacketSite 0) group+2 =
      warmKeyNextGroupPc (group.val+1) := by fin_cases group <;> decide
  obtain ⟨done,hDone⟩ := paired.advanceLocalWithPosition
    (pc' := warmKeyNextGroupPc (group.val+1))
    (G := fun lane => warmRoundKeyGroupFrame p l g batch round lane slot (group.val+1)) (by
      intro lane hl
      have hs := paired.checkpoint lane hl
      have hAt : At (paired.state lane)
          (packetPairPc (recurringPacketSite 0) group+2)
          (warmRoundKeyGroupFrame p l g batch round lane slot (group.val+1)) := by
        have hEq : warmRoundKeyGroupFrame p l g batch round lane slot (group.val+1) =
            warmKeyPairOperands l (warmKeyStage round) (warpLane l g lane%l.block) group
              (ptr lane) (P lane) ++ [(packetSizeReg (recurringPacketSite 0) group,b32 16)] := by
          simp only [warmRoundKeyGroupFrame,warmKeyPairOperands,
            warmRoundKeyWordsForSlot group slot _ hRange,P,warmRoundKeySized,keySizes_succ,
            keySizeReg,warmKeyPairCarry,List.append_assoc,ptr]
        rw [hEq]
        exact hs
      exact ⟨paired.state lane,.refl,hNext ▸ hAt⟩)
  refine ⟨done,fun lane hl pc cell data hCell => ?_⟩
  rw [hDone]
  apply hPaired lane hl
  rw [hShuffle,hMasked,hStart]
  exact hCell


set_option maxRecDepth 4096 in
/-- The upper half reloads the second saved private pointer before its first exchange. -/
theorem warmRoundKeyUpperOfMaximal {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmKeyNextGroupPc 8)
      (fun lane => warmRoundKeyGroupFrame p l g batch round lane 0 8) ordinal votes ends)
    (hSaved : ∀ lane < 32, warmRoundKeySavedUpper p l X g batch round lane (cur.pos lane)) :
    ∃ done : SchedulerWarpReached l X g (warmKeyNextGroupPc 9)
        (fun lane => warmRoundKeyGroupFrame p l g batch round lane 1 9) (ordinal+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => warmRoundGroupPointer p l g batch round lane 1
  let pF := fun lane => warmRoundKeySized p l g batch round 8 lane
  let F := fun lane => warmRoundKeyGroupFrame p l g batch round lane 0 8
  let G := fun lane => warmKeyPairMask 8 ::
    warmKeyPairCarry l (warmKeyStage round) (warpLane l g lane%l.block) (pF lane)
  let res := warmRoundKeyResidual p l g batch round
  obtain ⟨start,hStart⟩ := cur.advanceLocalWithPosition (pc' := warmKeyMaskPc 8)
    (G := fun lane => (1997,b32 (res lane))::F lane) (by
      intro lane hl
      have hs := cur.checkpoint lane hl
      exact ⟨cur.state lane,.refl,hs.mono ⟨holds_lookup hs.2.2.2.2 rfl,hs.2.2.2.2⟩⟩)
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ F lane) :
      pair.1 ≠ 169+(8 : Fin 16).val := by
    have h : ((F lane).map Prod.fst).all (fun r => decide (r ≠ 177)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨masked,hMasked⟩ := warmKeyMaskOfReached 8 res
    (fun lane _ => (warmRoundKeyLive hp (lane := lane) hb hLo hHi hTrips 8).1)
    (fun lane _ => (warmRoundKeyLive hp (lane := lane) hb hLo hHi hTrips 8).2) hFresh start
  obtain ⟨read,hRead⟩ := masked.advanceLocalWithPosition (pc' := warmKSecondReload.pc) (G := G) (by
    intro lane hl
    have hs := masked.checkpoint lane hl
    exact ⟨masked.state lane,.refl,hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.2.2.2⟩⟩)
  let base := l.localBase+32
  have hRange : base+warmKSecondReload.offset < 2^64 := by
    have hStack := hp.localMemory.2.1
    change l.localBase+32+8 < 2^64
    omega
  have hAlign : (base+warmKSecondReload.offset)%8 = 0 := by
    have hStack := hp.localMemory.1
    change (l.localBase+32+8)%8 = 0
    omega
  have hStackReg : ∀ lane < 32, (warmKSecondReload.baseReg,b64 base) ∈ G lane := by
    intro lane _
    simp [G,pF,base,warmKSecondReload,warmKeyPairCarry,warmRoundKeySized,warmRoundKeyPacked,
      warmRoundKeyCarry,
      warmRoundPagesFrame,warmRoundFrame,openingWarmFrame,warmStartFrame,
      warmPageRoots,warmLaneRoots]
  have hReloadFresh : ∀ lane < 32, ∀ pair ∈ G lane,
      pair.1 ≠ warmKSecondReload.lowReg ∧ pair.1 ≠ warmKSecondReload.highReg := by
    intro lane _ pair hm
    have h : ((G lane).map Prod.fst).all (fun r => decide (r ≠ 2019 ∧ r ≠ 2020)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  have hCell (lane : Nat) (hl : lane < 32) :
      PrimingCellValue X (warpLane l g lane) (read.pos lane) 977
        (warmKSecondReload.cell (warpLane l g lane) base) (b64 (ptr lane)).toBytes := by
    rw [hRead,hMasked,hStart]
    exact hSaved lane hl
  obtain ⟨ready,hReadyPos,hReadKeep⟩ := warmKSecondReload.warpReadPreservingOfMaximal hp hMax hg
    (by decide)
    Flow.code_1072 hRange hAlign (by decide) ptr
    (fun lane _ => (warmRoundKeyLanePointerBounds hp (lane := lane) hb hLo hHi 1).1)
    read hStackReg hReloadFresh hCell
  have hExF (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ pF lane) :
      pair.1 ≠ warmKShuffleOutput 8 ∧ pair.1 ≠ warmKShuffleOutput 8+1 := by
    have h : ((pF lane).map Prod.fst).all (fun r => decide (r ≠ 2021 ∧ r ≠ 2022)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨after,hAfterKeep⟩ := warmKeyLaterPairSizedOfMaximal hp hMax hg (warmKeyStage_lt round) 8
    (by decide) ptr
    (fun lane _ => warmRoundKeyLanePointerBounds hp (lane := lane) hb hLo hHi 1) hExF
    (by intro lane _; set_option maxRecDepth 100000 in kernel_rfl) ready
  obtain ⟨after',hAfterPos⟩ := after.advanceLocalWithPosition (pc' := warmKeyNextGroupPc 9)
    (G := fun lane => warmRoundKeyGroupFrame p l g batch round lane 1 9) (by
      intro lane hl
      have hs := after.checkpoint lane hl
      refine ⟨after.state lane,.refl,?_⟩
      have hPc : packetPairPc (recurringPacketSite 0) 8+2 = warmKeyNextGroupPc 9 := by decide
      have hEq : warmRoundKeyGroupFrame p l g batch round lane 1 9 =
          warmKeyPairOperands l (warmKeyStage round) (warpLane l g lane%l.block) 8
            (ptr lane) (pF lane) ++ [(packetSizeReg (recurringPacketSite 0) 8,b32 16)] := by
        simp only [warmRoundKeyGroupFrame,warmKeyPairOperands,pF,warmRoundKeySized,
          keySizes_succ,keySizeReg,warmKeyPairCarry,List.append_assoc,ptr]
        rfl
      rw [hEq]
      exact hPc ▸ hs)
  refine ⟨after',fun lane hl pc cell data hCell => ?_⟩
  rw [hAfterPos]
  apply hAfterKeep lane hl
  apply (hReadKeep lane hl).2
  rw [hRead,hMasked,hStart]
  exact hCell
end


private theorem warmRoundKeyHalfOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round ordinal votes first : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (slot : Fin 2) (hFirst : 2 ≤ first ∧ 8*slot.val < first)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmKeyNextGroupPc first)
      (fun lane => warmRoundKeyGroupFrame p l g batch round lane slot first) ordinal votes ends)
    (count : Nat) (hLast : first+count ≤ 8*(slot.val+1)) :
    ∃ done : SchedulerWarpReached l X g (warmKeyNextGroupPc (first+count))
        (fun lane => warmRoundKeyGroupFrame p l g batch round lane slot (first+count))
        (ordinal+2*count) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  induction count with
  | zero => exact ⟨cur,fun _ _ _ _ _ h => h⟩
  | succ k ih =>
    obtain ⟨mid,hMid⟩ := ih (by omega)
    have hSlot := slot.isLt
    let group : Fin 16 := ⟨first+k,by omega⟩
    have hNo : group.val ≠ 8 := by
      fin_cases slot
      · change first+k+1 ≤ 8 at hLast
        change first+k ≠ 8
        omega
      · have h := hFirst.2
        change 8 < first at h
        change first+k ≠ 8
        omega
    obtain ⟨done,hDone⟩ := warmRoundKeyNextGroupOfMaximal hp hMax hg hb hLo hHi hTrips slot group
      (by dsimp [group]; omega) ⟨by dsimp [group]; omega,by dsimp [group]; omega⟩ hNo mid
    have hN : ordinal+2*k+2 = ordinal+2*(k+1) := by omega
    rw [← hN]
    exact ⟨done,fun lane hl _ _ _ h => hDone lane hl (hMid lane hl h)⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch round : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)))
include hp hMax hFrame hg hw hb hLo hHi hTrips hReleased

private theorem warmRoundKeyPacketsOfMaximal (c : WarmRoundPages p l X g batch round) :
    ∃ done : SchedulerWarpReached l X g 1136
        (fun lane => warmRoundKeyGroupFrame p l g batch round lane 1 16) (c.shuffles+32) c.votes
        c.ends,
      ∀ lane < 32, ∀ slot isRow,
        warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  obtain ⟨first,hFirst⟩ := c.firstTwoKeyPairsOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips
      hReleased
  obtain ⟨mid,hMid⟩ := warmRoundKeyHalfOfMaximal hp hMax hg hb hLo hHi hTrips
    (first := 2) 0 (by decide) first 6 (by decide)
  obtain ⟨upper,hUpper⟩ := warmRoundKeyUpperOfMaximal hp hMax hg hb hLo hHi hTrips mid
    (fun lane hl => hMid lane hl (hFirst lane hl).1)
  obtain ⟨done,hDone⟩ := warmRoundKeyHalfOfMaximal hp hMax hg hb hLo hHi hTrips
    (first := 9) 1 (by decide) upper 7 (by decide)
  exact ⟨done,fun lane hl slot isRow =>
    hDone lane hl (hUpper lane hl (hMid lane hl ((hFirst lane hl).2 slot isRow)))⟩

/-- A warm K publication returns the full original register carry at the entrance to V. -/
theorem WarmRoundPages.publishKeyOfMaximal (c : WarmRoundPages p l X g batch round) :
    ∃ done : SchedulerWarpReached l X g 1138
        (fun lane => warmRoundKeyCarry p l g batch round lane ++ keySizes 16)
        (c.shuffles+32) c.votes c.ends,
      ∀ lane < 32, (∃ i,
        i+1 = done.pos lane ∧ X.get (warpLane l g lane,i) = some ⟨reuseArrival 0,
          .asyncArrive (readyObject l (warpLane l g lane) (kvUseStage (cacheUseOfRound round)))
            true⟩) ∧
        ∀ slot isRow, warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  classical
  obtain ⟨cur,hCurCells⟩ :=
    warmRoundKeyPacketsOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips hReleased c
  let threads := warpLane l g
  let addr := l.sharedBase+8*warmKeyStage round
  have hStage := warmKeyStage_lt round
  let stop := fun lane => cur.pos lane+2
  let ev : Nat → Event := fun lane => ⟨1137,.asyncArrive (readyObject l (threads lane) (kvUseStage
      (cacheUseOfRound round))) true⟩
  let es : Nat → List Event := fun lane => [⟨1136,.asyncCommit⟩,ev lane]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hWidth : addr+(copyArrivalAddress (recurringPacketSite 0)).2 < 2^32 := by
    have h := hp.shared.2.1
    change l.sharedBase+8*warmKeyStage round+32 < 2^32
    omega
  have hAlign : addr%8 = 0 := by
    have h := hp.shared.1
    dsimp [addr]
    omega
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (threads lane)).drop (cur.pos lane) =
        es lane ++ (X.tr (threads lane)).drop (stop lane) ∧
      At u 1138 (warmRoundKeyCarry p l g batch round lane ++ keySizes 16) ∧
      Run kernel Assumptions.all l (threads lane) {} ((X.tr (threads lane)).take (stop lane))
        (some u) ∧
      Run kernel Assumptions.all l (threads lane) u ((X.tr (threads lane)).drop (stop lane))
        (c.ends lane) ∧
      stop lane ≤ (X.tr (threads lane)).length ∧
      (stop lane = (X.tr (threads lane)).length → Step.Released l X (threads lane)) ∧
      X.get (threads lane,cur.pos lane+1) = some (ev lane) ∧
      ∀ slot isRow, warmRoundMetadata p l X g batch round lane (stop lane) slot isRow := by
    have hActor := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    have hs := cur.checkpoint lane hl
    have hAt : At (cur.state lane) (copyCommitPc (recurringPacketSite 0))
        [((copyArrivalAddress (recurringPacketSite 0)).1,b32 addr)] :=
      hs.mono ⟨holds_lookup hs.2.2.2.2 rfl,trivial⟩
    obtain ⟨hc,ha,hPast,hTail⟩ := copyCommitAndArriveOfMaximal hMax
      (g := threads lane) hActor (recurringPacketSite 0) hAt hWidth hAlign
      (cur.localSteps lane hl) (cur.recorded lane hl) (cur.continuation lane hl)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
    have hLoc : (⟨.shared,threads lane/l.block,addr+32⟩ : Loc) =
        readyObject l (threads lane) (kvUseStage (cacheUseOfRound round)) := by
      change _ = initObject l (threads lane/l.block) (readySlot (kvUseStage (cacheUseOfRound
          round)))
      rw [readySlot_address]
      congr 1
    change X.get (threads lane,cur.pos lane+1) =
      some ⟨1137,.asyncArrive ⟨.shared,threads lane/l.block,addr+32⟩ true⟩ at ha
    rw [hLoc] at ha
    have hStop : stop lane = cur.pos lane+1+1 := rfl
    have hFrame : At (next (next (cur.state lane))) 1138
        (warmRoundKeyCarry p l g batch round lane ++ keySizes 16) := by
      exact hs.next.next.mono hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨_,?_,hFrame,hPast,hTail,?_,?_,ha,fun slot isRow => ?_⟩
    · change (X.tr (threads lane))[cur.pos lane]? = some ⟨1136,.asyncCommit⟩ at hc
      change (X.tr (threads lane))[cur.pos lane+1]? = some (ev lane) at ha
      have hlo := List.getElem?_eq_some_iff.mp hc
      have hhi := List.getElem?_eq_some_iff.mp ha
      rw [List.drop_eq_getElem_cons hlo.1,hlo.2,List.drop_eq_getElem_cons hhi.1,hhi.2,hStop]
      rfl
    · rw [hStop]
      exact len_of_get ha
    · rw [hStop]
      exact releasedIfLast ha (by intro h; cases h)
    · rw [hStop]
      exact ((hCurCells lane hl slot isRow).step hMax.1 hc (by intro _ _ h; cases h)).step
        hMax.1 ha (by intro _ _ h; cases h)
  let _ : Inhabited TState := ⟨{}⟩
  choose! u hTrace hAt hPast hTail hBound hRelease hArrive hCells using hLane
  have hOrd := cur.ordinals.advance es (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨⟨stop,u,u,hOrd,hTail,fun _ _ => .refl,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,fun lane hl => ⟨⟨cur.pos lane+1,rfl,hArrive lane hl⟩,hCells lane hl⟩⟩
end


/-- The first warm key packet has returned its ready arrivals for all physical lanes. -/
structure WarmRoundKeyPublished (p : Params) (l : Launch) (X : Execution)
    (g batch round : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 1138
    (fun lane => warmRoundKeyCarry p l g batch round lane ++ keySizes 16) shuffles votes
      ends
  rank : shuffles = primingSearchShuffleCount batch+96+64*round
  published : ∀ lane < 32, ∃ i, i+1 = reached.pos lane ∧
    X.get (warpLane l g lane,i) = some ⟨reuseArrival 0,
      .asyncArrive (readyObject l (warpLane l g lane) (kvUseStage (cacheUseOfRound round))) true⟩
  metadata : ∀ lane < 32, ∀ slot isRow,
    warmRoundMetadata p l X g batch round lane (reached.pos lane) slot isRow

/-- The refreshed pages of warm round `round` progress through all K vectors, the commit and
the ready arrival. -/
theorem WarmRoundPages.keyPublishedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)))
    (c : WarmRoundPages p l X g batch round) :
    Nonempty (WarmRoundKeyPublished p l X g batch round) := by
  obtain ⟨done,hPublished⟩ :=
    c.publishKeyOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips hReleased
  exact ⟨⟨c.shuffles+32,c.votes,c.ends,done,by rw [c.rank]; omega,
    fun lane hl => (hPublished lane hl).1,fun lane hl => (hPublished lane hl).2⟩⟩

def warmRoundValueCarry (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  recurringVTransitionFacts 0 (kvUseStage (cacheUseOfRound round))
    (kvEmptyPhase (cacheUseOfRound round)) ++
      (warmRoundKeyCarry p l g batch round lane ++ keySizes 16)

/-- Both warps return from the K publication of warm round `round` with V using the next
ring stage and parity. -/
theorem WarmRoundKeyPublished.valueEntry {p : Params} {l : Launch} {X : Execution}
    {g batch round : Nat} (c : WarmRoundKeyPublished p l X g batch round) :
    ∃ next : SchedulerWarpReached l X g 1143 (warmRoundValueCarry p l g batch round)
        c.shuffles c.votes c.ends,
      next.pos = c.reached.pos := by
  apply c.reached.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let use := cacheUseOfRound round
  let F := warmRoundKeyCarry p l g batch round lane ++ keySizes 16
  have hs := c.reached.checkpoint lane hl
  have hF : Holds (c.reached.state lane).regs F := hs.2.2.2.2
  have hAt : At (c.reached.state lane) 1138
      ([(7179,b32 (kvUseStage use).val),(7180,loaderPhaseWord (kvEmptyPhase use))]++F) := by
    refine hs.mono ⟨holds_mem hF ?_,holds_mem hF ?_,hF⟩ <;>
      simp [F,use,warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame]
  obtain ⟨u,hu,hU⟩ := roundStraightFrameAll (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringVTransitionRun (l := l) (g := t) 0 (kvUseStage use) (kvEmptyPhase use)) hAt
  exact ⟨u,run_rtg hu,hU⟩

/-- After the K publication of warm round `round`, each lane of the warp has made all
recurring publications up to and including that K use. -/
theorem WarmRoundKeyPublished.publicationCount {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (c : WarmRoundKeyPublished p l X g batch round) :
    ∀ lane < 32, cacheUseOfRound round-1 ≤
      ((X.tr (warpLane l g lane)).take (c.reached.pos lane)).countP
        recurringPublicationMark := by
  intro lane hl
  obtain ⟨i,hi,he⟩ := c.published lane hl
  have hMark : recurringPublicationMark ⟨reuseArrival 0,
      .asyncArrive (readyObject l (warpLane l g lane) (kvUseStage (cacheUseOfRound round)))
        true⟩ = true := by
    apply (recurringPublicationMark_iff _).mpr
    exact ⟨0,_,rfl⟩
  have hRank := recurringPublicationShuffleRank hp hX hFrame hg hw hl hb hLo hHi he hMark
  have hShfl := countP_take_succ_false (p := Execution.isShfl) he rfl
  rw [hi,c.reached.ordinals.shfl lane hl,c.rank] at hShfl
  have hSucc := countP_take_succ he hMark
  rw [hi] at hSucc
  change _ = _ + 32 + 32*(2+((X.tr (warpLane l g lane)).take i).countP recurringPublicationMark)
    at hRank
  unfold cacheUseOfRound
  omega

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
