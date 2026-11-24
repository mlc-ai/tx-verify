-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderValueHalfProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderValueSecondSlotProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerReloadProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part013
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

/-- The warp is about to publish its first V packet after both vector-copy halves. -/
abbrev OpeningValueCommitReached (p : Params) (l : Launch) (X : Execution)
    (g batch tile warp shuffles votes : Nat) (bases residual : Nat → Nat)
    (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 903 (vHalfFrame p l batch tile warp 1 bases residual)
    shuffles votes ends

/-- Both real V halves issue all their vectors. The second reloaded pointer is still
the last lane-private store despite the first half's broadcasts and cache copies. -/
theorem primingVPacketOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch tile warp shuffles votes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (bases : Fin 2 → Nat → Nat) (residual firstLoad : Nat → Nat)
    (hBases : ∀ slot lane, lane < 32 → bases slot lane < 2^64 ∧ bases slot lane%16 = 0)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 805 (fun lane => primingVReloadWords 0 (bases 0 lane) ++
      vPacketFrame p l batch tile warp lane residual) shuffles votes ends)
    (hFirst : ∀ lane < 32, let thread := warpLane l g lane
      X.get (thread,firstLoad lane) = some ⟨804,.rd
        ((primingVPointerReload 0).word thread l.localBase 0) (pointerReadBytes (bases 0 lane) 0)⟩)
    (hBefore : ∀ lane < 32, firstLoad lane ≤ cur.pos lane)
    (hSaved : ∀ lane < 32, let thread := warpLane l g lane
      PrimingCellValue X thread (firstLoad lane) 799 (sourceScratchAccess l thread 1)
        (b64 (bases 1 lane)).toBytes) :
    ∃ _ : OpeningValueCommitReached p l X g batch tile warp (shuffles+32) votes (bases 1)
        residual ends,
      ∃ pos : Fin 16 → Nat → Nat, ∀ pair,
        VPacketPairIssued p l X g batch tile warp pair (bases (vPacketSlot pair)) (pos pair) := by
  obtain ⟨firstDone,low,hLow⟩ := vPacketHalfOfMaximal hp hMax hg 0 (bases 0) residual (hBases 0) cur
  obtain ⟨second⟩ := firstDone.advanceLocal (pc' := 854)
    (G := fun lane => vPacketCarry p l batch tile warp lane residual) (fun lane hl => by
      have hs := firstDone.checkpoint lane hl
      exact ⟨_,.refl,hs.mono ((holds_append ..).mp hs.2.2.2.2).2⟩)
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLatest (lane : Nat) (hl : lane < 32) :
      let thread := warpLane l g lane
      PrimingCellValue X thread (second.pos lane) 799 (sourceScratchAccess l thread 1)
        (b64 (bases 1 lane)).toBytes := by
    let thread := warpLane l g lane
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hw' : 14 ≤ warpIndex l thread := by
      have hThis : warpIndex l thread = warpIndex l g := hSame.2.symm
      rw [hThis]
      exact hw
    have hAfter : cur.pos lane ≤ second.pos lane := by
      by_contra! hBad
      have hCount := Flow.countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hBad.le
      rw [second.ordinals.shfl lane hl,cur.ordinals.shfl lane hl] at hCount
      omega
    exact primingVSecondSlotLatestAtCursor hp hMax.1 (g := thread) hw' (hFirst lane hl) rfl
      (second.recorded lane hl) (second.localSteps lane hl) (second.checkpoint lane hl).1
      ((hBefore lane hl).trans hAfter) (hSaved lane hl)
  let site := primingVPointerReload 1
  have hWidth : l.localBase+site.offset < 2^64 := by
    have := hp.localMemory.2.1
    change l.localBase+8 < 2^64
    omega
  have hAlign : (l.localBase+site.offset)%8 = 0 := by
    have := hp.localMemory.1
    change (l.localBase+8)%8 = 0
    omega
  have hFresh (lane : Nat) (_hl : lane < 32) :
      ∀ pair ∈ vPacketCarry p l batch tile warp lane residual,
      pair.1 ≠ site.lowReg ∧ pair.1 ≠ site.highReg := by
    intro pair hm
    have hAudit : ((vPacketCarry p l batch tile warp lane residual).map Prod.fst).all
        (fun r => decide (r ≠ site.lowReg ∧ r ≠ site.highReg)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (List.mem_map_of_mem hm))
  obtain ⟨secondWords,_⟩ := site.warpReadOfMaximal hp hMax hg
    (by decide) Flow.code_854 hWidth hAlign
    (by decide) (bases 1) (fun lane hl => (hBases 1 lane hl).1) second
    (fun _ _ => by simp [site,primingVPointerReload,vPacketCarry,vPacketFrame,primingVPacketFrame])
    hFresh hLatest
  obtain ⟨last,high,hHigh⟩ :=
    vPacketHalfOfMaximal hp hMax hg 1 (bases 1) residual (hBases 1) secondWords
  let which (pair : Fin 16) : Fin 8 := ⟨vPacketSelect pair,Nat.mod_lt _ (by decide)⟩
  have hOrd : shuffles+16+16 = shuffles+32 := by omega
  refine ⟨hOrd ▸ last,(fun pair => if (vPacketSlot pair).val = 0 then low (which pair)
    else high (which pair)),?_⟩
  intro pair
  have hPart : vHalfPair (vPacketSlot pair) (which pair) = pair := by
    apply Fin.ext
    change 8*(pair.val/8)+pair.val%8 = pair.val
    omega
  have hSlots : ∀ slot : Fin 2, slot = 0 ∨ slot = 1 := by decide
  rcases hSlots (vPacketSlot pair) with h | h
  · have hEq : vHalfPair 0 (which pair) = pair := by rwa [h] at hPart
    simpa only [h,Fin.val_zero,ite_true,hEq] using hLow (which pair)
  · have hEq : vHalfPair 1 (which pair) = pair := by rwa [h] at hPart
    simpa only [h,Fin.val_one,Nat.one_ne_zero,ite_false,hEq] using hHigh (which pair)

end PTX.Kernels.TmlFa4Fwd.Loader
