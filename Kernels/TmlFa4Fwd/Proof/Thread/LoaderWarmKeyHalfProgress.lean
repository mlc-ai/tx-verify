-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyOddProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyOddProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

def warmKeyNextGroupPc (group : Nat) : Nat :=
  if h : group < 16 then warmKeyMaskPc ⟨group,h⟩ else 1136

def warmKeySlotGroup : Fin 2 → Fin 16
  | 0 => 0
  | 1 => 8

def warmKeyLanePointer (p : Params) (l : Launch) (g batch lane : Nat) (slot : Fin 2) : Nat :=
  primingKRowPointer p batch ((assignedCoordinates p batch (g/l.block)).2/6)
    (warmFirstSlotRow p l g batch lane slot)

def warmKeyGroupFrame (p : Params) (l : Launch) (g batch lane : Nat) (slot : Fin 2) :
    List (Nat × Value) :=
  warmKeyPairOperands l 2 (warpLane l g lane%l.block) (warmKeySlotGroup slot)
    (warmKeyLanePointer p l g batch lane slot) (warmFirstKeyPacked p l g batch lane)

private theorem warmKeyWordsForSlot (group : Fin 16) (slot : Fin 2) (base : Nat)
    (hRange : 8*slot.val ≤ group.val ∧ group.val < 8*(slot.val+1)) :
    warmKeyWords (warmKeySlotGroup slot) base = warmKeyWords group base := by
  fin_cases slot
  · change 0 ≤ group.val ∧ group.val < 8 at hRange
    have h : group.val < 8 := hRange.2
    simp [warmKeyWords,warmKShuffleInput,warmKeySlotGroup,h]
  · change 8 ≤ group.val ∧ group.val < 16 at hRange
    have h : ¬ group.val < 8 := Nat.not_lt_of_ge hRange.1
    simp [warmKeyWords,warmKShuffleInput,warmKeySlotGroup,h]

set_option maxRecDepth 100000 in
/-- Any reached noninitial group in either half executes its mask, both exchanges, and both
copies. All lane-local cells are preserved across the exact group slice. -/
theorem warmKeyNextGroupOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch ordinal votes : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (slot : Fin 2) (group : Fin 16) (hLater : 2 ≤ group.val)
    (hRange : 8*slot.val ≤ group.val ∧ group.val < 8*(slot.val+1))
    (hNoReload : group.val ≠ 8) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmKeyNextGroupPc group.val)
      (fun lane => warmKeyGroupFrame p l g batch lane slot) ordinal votes ends) :
    ∃ done : SchedulerWarpReached l X g (warmKeyNextGroupPc (group.val+1))
        (fun lane => warmKeyGroupFrame p l g batch lane slot) (ordinal+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => warmKeyLanePointer p l g batch lane slot
  let res := warmFirstKeyResidual p l g batch
  let P := warmFirstKeyPacked p l g batch
  let F := fun lane => warmKeyGroupFrame p l g batch lane slot
  let G := fun lane => warmKeyPairMask group ::
    warmKeyPairCarry l 2 (warpLane l g lane%l.block) (P lane)
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
    (fun lane _ => (warmKeyFirstLive hp (lane := lane) hb hLo hHi hTrips group).1)
    (fun lane _ => (warmKeyFirstLive hp (lane := lane) hb hLo hHi hTrips group).2)
    hFresh start
  obtain ⟨shuffle,hShuffle⟩ := masked.advanceLocalWithPosition (pc' := warmKShufflePc group)
    (G := fun lane => warmKeyWords group (ptr lane) ++ G lane) (by
      intro lane hl
      let hs := masked.checkpoint lane hl
      have ht := hs.2.2.2.2
      have h' : Holds (masked.state lane).regs (warmKeyPairOperands l 2
          (warpLane l g lane%l.block) group (ptr lane) (P lane)) := by
        rw [warmKeyPairOperands,← warmKeyWordsForSlot group slot (ptr lane) hRange]
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
  obtain ⟨paired,hPaired⟩ := warmKeyLaterPairOfMaximal hp hMax hg (by decide)
    group hLater ptr (fun lane _ => warmKeyLanePointerBounds hp (lane := lane) hb hLo hHi slot)
    hFresh' hFrame shuffle
  have hNext : packetPairPc (recurringPacketSite 0) group+2 =
      warmKeyNextGroupPc (group.val+1) := by fin_cases group <;> decide
  obtain ⟨done,hDone⟩ := paired.advanceLocalWithPosition
    (pc' := warmKeyNextGroupPc (group.val+1)) (G := F) (by
      intro lane hl
      have hs := paired.checkpoint lane hl
      have hAt : At (paired.state lane)
          (packetPairPc (recurringPacketSite 0) group+2) (F lane) := by
        unfold F warmKeyGroupFrame warmKeyPairOperands
        rw [warmKeyWordsForSlot group slot (ptr lane) hRange]
        exact hs
      exact ⟨paired.state lane,.refl,hNext ▸ hAt⟩)
  refine ⟨done,fun lane hl pc cell data hCell => ?_⟩
  rw [hDone]
  apply (hPaired lane hl).2.2
  rw [hShuffle,hMasked,hStart]
  exact hCell

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
