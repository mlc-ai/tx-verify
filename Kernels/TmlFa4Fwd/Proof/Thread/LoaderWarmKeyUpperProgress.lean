-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyHalfProgress
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondReload
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyOddProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part016

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

set_option maxRecDepth 4096 in
/-- The upper half reloads the second saved private pointer before its first exchange. -/
theorem warmKeyUpperFirstOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch ordinal votes : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmKeyNextGroupPc 8)
      (fun lane => warmKeyGroupFrame p l g batch lane 0) ordinal votes ends)
    (hSaved : ∀ lane < 32, warmKeySavedUpper p l X g batch lane (cur.pos lane)) :
    Nonempty (SchedulerWarpReached l X g (warmKeyNextGroupPc 9)
      (fun lane => warmKeyGroupFrame p l g batch lane 1) (ordinal+2) votes ends) := by
  let ptr := fun lane => warmKeyLanePointer p l g batch lane 1
  let pF := warmFirstKeyPacked p l g batch
  let F := fun lane => warmKeyGroupFrame p l g batch lane 0
  let G := fun lane => warmKeyPairMask 8 ::
    warmKeyPairCarry l 2 (warpLane l g lane%l.block) (pF lane)
  let res := warmFirstKeyResidual p l g batch
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
    (fun lane _ => (warmKeyFirstLive hp (lane := lane) hb hLo hHi hTrips 8).1)
    (fun lane _ => (warmKeyFirstLive hp (lane := lane) hb hLo hHi hTrips 8).2) hFresh start
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
    simp [G,pF,base,warmKSecondReload,warmKeyPairCarry,warmFirstKeyPacked,warmFirstKeyCarry,
      warmFirstPagesFrame,warmFirstFrame,openingWarmPublishedFrame,openingWarmFrame,warmStartFrame,
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
  obtain ⟨ready,_⟩ := warmKSecondReload.warpReadOfMaximal hp hMax hg (by decide)
    Flow.code_1072 hRange hAlign (by decide) ptr
    (fun lane _ => (warmKeyLanePointerBounds hp (lane := lane) hb hLo hHi 1).1)
    read hStackReg hReloadFresh hCell
  have hExF (lane : Nat) (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ pF lane) :
      pair.1 ≠ warmKShuffleOutput 8 ∧ pair.1 ≠ warmKShuffleOutput 8+1 := by
    have h : ((pF lane).map Prod.fst).all (fun r => decide (r ≠ 2021 ∧ r ≠ 2022)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  obtain ⟨after,_⟩ := warmKeyLaterPairOfMaximal hp hMax hg (by decide) 8 (by decide) ptr
    (fun lane _ => warmKeyLanePointerBounds hp (lane := lane) hb hLo hHi 1) hExF
    (by intro lane _; set_option maxRecDepth 100000 in kernel_rfl) ready
  exact ⟨after⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
