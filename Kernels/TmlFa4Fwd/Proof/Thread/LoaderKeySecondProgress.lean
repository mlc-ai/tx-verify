-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyLaterProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerReloadProgress
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSecondSlot
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSecondReload
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPacket

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

private theorem completeLaterKeyPairs {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch tile warp shuffles votes : Nat} (hg : g < l.threads)
    (hLen : p.kLength batch < 2^31) (hTile : 128*tile+7 < 2^31)
    (bases : Nat → Nat) (hBases : ∀ lane < 32, bases lane < 2^64 ∧ bases lane%16 = 0)
    {ends : Nat → Option TState} (first : SchedulerWarpReached l X g 617
      (primingKLaterFrame p l batch tile warp bases 7) shuffles votes ends)
    {n : Nat} (hn : n ≤ 7) :
    Nonempty (SchedulerWarpReached l X g (617+8*n)
      (primingKLaterFrame p l batch tile warp bases 7) (shuffles+2*n) votes ends) := by
  induction n with
  | zero => exact ⟨first⟩
  | succ n ih =>
    obtain ⟨cur⟩ := ih (by omega)
    let j : Fin 15 := ⟨n+8,by omega⟩
    have hf : primingKLaterFrame p l batch tile warp bases j =
        primingKLaterFrame p l batch tile warp bases 7 := by
      have hj : ¬ j.val < 7 := by dsimp [j]; omega
      funext lane
      simp only [primingKLaterFrame,primingKPointerReg,ite_eq_right hj]
      rfl
    have hPc : primingKPredicatePc (primingKLaterPair j) = 617+8*n := by
      change 550+8*(n+8+1)+(if n+8+1 < 8 then 0 else 1)-
        (if n+8+1 = 8 then 7 else 6) = _
      split_ifs <;> omega
    obtain ⟨next,_⟩ := primingKMaskedPairOfMaximal hp hMax hg hLen hTile bases hBases j
      (by dsimp [j]; omega) (hf.symm ▸ hPc.symm ▸ cur)
    have hNext : kCopyPc (primingKLaterPair j)+2 = 617+8*(n+1) := by
      change 550+8*(n+8+1)+(if n+8+1 < 8 then 0 else 1)+2 = _
      split_ifs <;> omega
    have hShuffles : shuffles+2*n+2 = shuffles+2*(n+1) := by omega
    exact ⟨hf ▸ hNext ▸ hShuffles ▸ next⟩

/-- The tracked first K packet reaches its commit after issuing all its vector pairs. -/
theorem primingKeyPacketBoundaryOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch head tile shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hh : head < p.kvHeads) (hTile : 128*tile+7 < 2^31)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 538
      (primingKMaskInputs p l batch tile (warpIndex l g)) shuffles votes ends)
    (hSaved : ∀ lane < 32, ∀ slot : Fin 2,
      let thread := warpLane l g lane
      let row := primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val
      PrimingCellValue X thread (cur.pos lane) 534 (sourceScratchAccess l thread slot)
        (b64 (primingKRowPointer p batch head row)).toBytes) :
    let warp := warpIndex l g
    let bases := fun lane => primingKRowPointer p batch head (primingLaneRow tile (32*warp+lane)+64)
    Nonempty (SchedulerWarpReached l X g 673
      (primingKLaterFrame p l batch tile warp bases 7) (shuffles+32) votes ends) := by
  dsimp only
  let warp := warpIndex l g
  let bases₀ := primingKeyLaneBase p batch head tile warp
  let bases₁ := fun lane => primingKRowPointer p batch head (primingLaneRow tile (32*warp+lane)+64)
  have hBases₀ (lane : Nat) (_ : lane < 32) : bases₀ lane < 2^64 ∧ bases₀ lane%16 = 0 :=
    primingStoredPointerBounds hp hb hh
  have hBases₁ (lane : Nat) (_ : lane < 32) : bases₁ lane < 2^64 ∧ bases₁ lane%16 = 0 :=
    primingStoredPointerBounds hp hb hh
  have hLen : p.kLength batch < 2^31 := by have := (hp.lengths batch hb).2.2; omega
  obtain ⟨loaded,hFirst⟩ := primingKeyFirstPointerReloadWithEvents hp hMax hg hb hh hTile cur
    (fun lane hl => by
      simpa only [primingKeyLaneBase,warp,Fin.val_zero,Nat.mul_zero,Nat.add_zero]
        using hSaved lane hl 0)
  obtain ⟨broadcast⟩ := primingKeyBroadcastOfMaximal hp hMax hg bases₀ loaded
  obtain ⟨first,_⟩ := primingKeyFirstPairOfMaximal hp hMax hg bases₀ hBases₀ broadcast
  obtain ⟨beforeLast⟩ := primingKFirstHalfOfMaximal hp hMax hg hLen hTile bases₀ hBases₀ first
    (j := 6) (by decide)
  obtain ⟨last,hAtLeastTwo,hLast⟩ := primingKFirstHalfPairOfMaximal hp hMax hg hLen hTile
    bases₀ hBases₀ 6 beforeLast
  let F := fun lane =>
    (132,.pred (decide (kvCopyRow tile (32*warp+lane) 8 < p.kLength batch))) ::
      primingKPacketFrame p l batch tile warp bases₀ lane
  obtain ⟨atReload,hPos,hBefore⟩ := last.toSchedulerWarpAt.advanceLocalPreserving
    (pc' := 609) (G := F) (fun lane hl => primingKSecondPointerDecode hLen hTile bases₀
      (last.checkpoint lane hl))
  let ready := last.reframe atReload hPos hBefore
  have hLocal := hp.localMemory.2.1
  have hAlign := hp.localMemory.1
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  let site := primingKSecondReload
  have hLatest (lane : Nat) (hl : lane < 32) :
      PrimingCellValue X (warpLane l g lane) (ready.pos lane) 534
        (site.cell (warpLane l g lane) l.localBase) (b64 (bases₁ lane)).toBytes := by
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hLane : 14 ≤ warpIndex l (warpLane l g lane) := by
      rw [show warpIndex l (warpLane l g lane) = warpIndex l g from hSame.2.symm]
      exact hw
    have hSaved₁ : PrimingCellValue X (warpLane l g lane) (cur.pos lane) 534
        (sourceScratchAccess l (warpLane l g lane) 1) (b64 (bases₁ lane)).toBytes := by
      simpa only [bases₁,warp,Fin.val_one,Nat.mul_one] using hSaved lane hl 1
    have hFinal := primingSecondSlotLatestAfterFirstHalf hp hMax.1 hLane
      (hFirst lane hl) (hLast lane hl true) (by rfl) hSaved₁
    have hCount := hAtLeastTwo lane hl
    have hEnd : last.pos lane - 2 + (if true then 1 else 0) + 1 = last.pos lane := by
      simp only [ite_true]
      omega
    change PrimingCellValue X (warpLane l g lane) (atReload.pos lane) 534 _ _
    rw [hPos]
    exact hEnd ▸ hFinal
  obtain ⟨loaded₁,_⟩ := site.warpReadOfMaximal hp hMax hg (addr := l.localBase)
    (by decide) Flow.code_609 (by change l.localBase+8 < 2^64; omega)
    (by change (l.localBase+8)%8 = 0; omega) (by decide) bases₁
    (fun lane hl => (hBases₁ lane hl).1) ready
    (fun _ _ => by simp [site,primingKSecondReload,F,primingKPacketFrame,
      primingKSourceInputs,primingKSourceFrame])
    (fun _ _ => by simp [site,primingKSecondReload,F,primingKPacketFrame,
      primingKSourceInputs,primingKSourceFrame]) hLatest
  obtain ⟨second⟩ := loaded₁.advanceLocal
    (G := fun lane => primingKPairPredicate p batch tile warp 7 lane ::
      primingKLaterFrame p l batch tile warp bases₁ 7 lane) (pc' := 610) (fun lane hl => by
        refine ⟨_,.refl,?_⟩
        at_select (loaded₁.checkpoint lane hl))
  obtain ⟨after,_⟩ := primingKCopyAfterMaskOfMaximal hp hMax hg bases₁ hBases₁ 7 second
  simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.reduceMul] using
    completeLaterKeyPairs hp hMax hg hLen hTile bases₁ hBases₁ after (n := 7) (by decide)

end
end PTX.Kernels.TmlFa4Fwd.Loader
