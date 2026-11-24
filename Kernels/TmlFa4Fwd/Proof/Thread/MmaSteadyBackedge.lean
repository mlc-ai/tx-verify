-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyKeyWait
import all Kernels.TmlFa4Fwd.Proof.MmaLoopCounter
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Flow.Code.Part039

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Loader Epilogue

noncomputable section

def steadyBackedgeFrame (l : Launch) (visit remaining : Nat) : List (Nat × Value) :=
  steadyKeyRing visit ++ (7205,b32 (visit%2))::(7204,wideCounterWord remaining)::steadyPorts l

private def backedgeRingFrame (l : Launch) (visit : Nat) : List (Nat × Value) :=
  [(7207,b32 (readyStage (2*visit+1)).val),(7208,b32 (readyWord (2*visit+1))),
    (7205,b32 (visit%2))] ++ steadyPorts l

private theorem backedgeRingStep {l : Launch} {g visit remaining : Nat} {t : TState}
    (ht : At t 2524 (steadyBackedgeFrame l visit remaining)) :
    ∃ u, run kernel [] l g 6 t = some u ∧
      At u 2530 ((7204,wideCounterWord remaining)::backedgeRingFrame l (visit+1)) := by
  let use := 2*visit+2
  have hSucc : use+1 = 2*(visit+1)+1 := by dsimp only [use]; omega
  have hAdvance (s : Fin 3) (phase : Bool) : Seg kernel [] l g 5 2524
      [(1192,b32 s.val),(2572,loaderPhaseWord phase)] 2529
      [(7207,b32 ((s.val+1)%3)),(7208,loaderPhaseWord (loaderNextPhase s phase))] := by
    fin_cases s <;> cases phase <;> intro u hu <;>
      dsimp only [loaderPhaseWord,loaderNextPhase] at hu ⊢ <;> seg_fp hu using decide
  have hAdvance' := hAdvance (readyStage use) (readyParity use)
  rw [← readyStage_succ, ← readyParity_succ, loaderPhaseWord_ready, loaderPhaseWord_ready,
    hSucc] at hAdvance'
  obtain ⟨u,hu,hU⟩ := hAdvance'.apply
    (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  have hIn : At t 2524 ((7205,b32 (visit%2))::(7204,wideCounterWord remaining)::steadyPorts l) :=
    ht.mono ht.2.2.2.2.2.2
  obtain ⟨_,hKeep⟩ := activeDrainLocalKeep hIn (by decide) (by decide) (by
    change ((kernel.code.drop 2524).take 5).all
      (fun ins => [7205,7204,2535,2610,2614,2615,2618,1190].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hu
  have hToggle (i : Fin 2) : Seg kernel [] l g 1 2529 [(7205,b32 i.val)] 2530
      [(7205,b32 ((i.val+1)%2))] := by
    fin_cases i <;> intro v hv <;> dsimp at hv ⊢ <;> seg_fp hv using decide
  have hToggle' := hToggle ⟨visit%2,Nat.mod_lt _ (by decide)⟩
  have hParity : (visit%2+1)%2 = (visit+1)%2 := by omega
  change Seg kernel [] l g 1 2529 [(7205,b32 (visit%2))] 2530
    [(7205,b32 ((visit%2+1)%2))] at hToggle'
  rw [hParity] at hToggle'
  obtain ⟨v,hv,hV⟩ := hToggle'.apply (hU.mono ⟨hKeep.1,trivial⟩)
  have hInter := hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,hKeep.2⟩)
  obtain ⟨_,hKeep'⟩ := activeDrainLocalKeep hInter (by decide) (by decide) (by
    change ((kernel.code.drop 2529).take 1).all
      (fun ins => [7207,7208,7204,2535,2610,2614,2615,2618,1190].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide) hv
  exact ⟨v,run_comp hu hv,hV.mono
    ⟨hKeep'.2.2.1,hKeep'.1,hKeep'.2.1,hV.2.2.2.2.1,hKeep'.2.2.2⟩⟩

private theorem backedgeCounter {l : Launch} {g visit remaining : Nat} {t : TState}
    (hRemaining : 2 ≤ remaining) (hBound : remaining < 2^32) (hPositive : 0 < visit)
    (ht : At t 2530 ((7204,wideCounterWord remaining)::backedgeRingFrame l visit)) :
    ∃ u, run kernel [] l g 4 t = some u ∧
      At u (if 2 < remaining then 2291 else 2534) (steadyFrame l visit (remaining-1)) := by
  have hWord : wideCounterWord remaining = counterWord remaining :=
    ite_eq_right (show remaining ≠ 2^32+1 by omega)
  have hTail : At t 2530 [(7204,counterWord remaining)] :=
    ht.mono ⟨hWord ▸ ht.2.2.2.2.1,trivial⟩
  obtain ⟨u,hu,hU⟩ := counterTail (l := l) (g := g) hRemaining hBound t hTail
  have hShort : Seg kernel [] l g 2 2530 [(7204,counterWord remaining)] 2532
      [(7204,counterWord (remaining-1))] := by
    have hWidth : 2^32-remaining < 2^32 := by omega
    intro w hw
    simp only [counterWord] at hw ⊢
    seg_fp hw using
      (simp only [b32,truncBits_ofNat hWidth (by decide),
        show truncBits 32 (BitVec.ofInt 64 1) = 1#64 by rfl]
       exact congrArg (Value.bits 32) (incrementBits hRemaining hBound))
  obtain ⟨v,hv,hV⟩ := hShort.apply hTail
  have hLast : Seg kernel [] l g 1 2532 [] 2533 [(7206,b32 1)] := by
    intro w hw
    seg_fp hw using decide
  obtain ⟨w,hw,hW⟩ := hLast.apply (hV.mono trivial)
  have hSame : w = u := Option.some.inj ((run_comp hv hw).symm.trans hu)
  have hAcc : u.regs 7206 = some (b32 1) := hSame ▸ hW.2.2.2.2.1
  have hBranch := hU.mono (G := [(399,.pred (decide (2 < remaining))),(7206,b32 1)])
    ⟨hU.2.2.2.2.1,hAcc,trivial⟩
  obtain ⟨z,hz,hZ⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2533 _ hBranch hBranch.2.2.2.2.1 (by simp)
  obtain ⟨_,hFrame⟩ := activeDrainLocalKeep (ht.mono ht.2.2.2.2.2) (by decide)
    (by decide) (by
      change ((kernel.code.drop 2530).take 4).all
        (fun ins => [7207,7208,7205,2535,2610,2614,2615,2618,1190].all
          fun r => !(writesRegs ins.op).contains r) = true
      decide +kernel) (by decide +kernel) (run_comp hu hz)
  have hNext : wideCounterWord (remaining-1) = counterWord (remaining-1) :=
    ite_eq_right (show remaining-1 ≠ 2^32+1 by omega)
  have hCounter :=
    schedulerLocalFrame (regs := [7204]) (lo := 2533) (len := 1) (r := 7204)
      (by decide +kernel) rfl hz hU.1.ge (by rw [hU.1]) (by simp)
  refine ⟨z,run_comp hu hz,?_⟩
  simp only [decide_eq_true_eq] at hZ
  apply hZ.mono
  simp only [steadyFrame, hPositive, ↓reduceIte, hNext]
  exact ⟨hFrame.1,hFrame.2.1,hFrame.2.2.1,hZ.2.2.2.2.2.1,
    hCounter.trans hU.2.2.2.2.2.1,hFrame.2.2.2⟩

variable {l : Launch} {X : Execution} {g visit remaining shuffles votes : Nat}

/-- Each completed recurring body consumes one KV trip and selects the next recurring
or final PV traversal with the advanced ring and probability parities. -/
theorem steadyBackedgeReachedFramedWithPosition {ends : Nat → Option TState}
    {extra : List (Nat × Value)} (hRemaining : 2 ≤ remaining) (hBound : remaining < 2^32)
    (cur : SchedulerWarpReached l X g 2524
      (fun _ => steadyBackedgeFrame l visit remaining ++ extra) shuffles votes ends)
    (hExtra : ((kernel.code.drop 2524).take 10).all
      (fun ins => (extra.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true) :
    ∃ next : SchedulerWarpReached l X g (if 2 < remaining then 2291 else 2534)
      (fun _ => steadyFrame l (visit+1) (remaining-1) ++ extra) shuffles votes ends,
      next.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  have ht := cur.checkpoint lane hl
  have hParts := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨u,hu,hU⟩ := backedgeRingStep (g := warpLane l g lane) (ht.mono hParts.1)
  obtain ⟨v,hv,hV⟩ := backedgeCounter (g := warpLane l g lane) hRemaining hBound (by omega) hU
  obtain ⟨path,hKept⟩ := activeDrainLocalKeep (ht.mono hParts.2) (by decide) (by decide)
    hExtra (by decide +kernel) (run_comp hu hv)
  exact ⟨v,path,hV.mono ((holds_append ..).mpr ⟨hV.2.2.2.2,hKept⟩)⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
