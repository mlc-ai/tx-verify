-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasRendezvousProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasSignalProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Correction

/-- The released repeated Bias rendezvous reaches the actual FMA cursor.
The leader records the empty credit and all lanes retain their live inputs. -/
theorem repeatedBiasReturnOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (biasFencePc true+3) F)
    (hKeep : Holds c.ready.regs (biasKeep l g warp true))
    (hStable : ∀ x ∈ F, x.1 ∉ biasReleaseWritten true)
    (bias : Nat → Option ℝ)
    (hBias : ∀ i : Fin 16, BiasUnpacked true i c.ready (fun k =>
      biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1)))) :
    ∃ after : OpeningTripCursor l X g (biasBodyStart true) F,
      after.ending = c.ending ∧
      after.pos = (if laneOf l g = 0 then c.pos+1 else c.pos) ∧
      (laneOf l g = 0 → X.get (g,c.pos) = some ⟨5278,
        .arrive (signalLoc l g (stageOf warp) (biasReleaseSite true)) 0 1 true .cta⟩) ∧
      ∀ i : Fin 16, BiasUnpacked true i after.ready (fun k =>
        biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1))) := by
  obtain ⟨u,hBranch,hStart,hBranchFrame⟩ :=
    biasReleaseBranchFrame warp true (c.checkpoint.mono hKeep)
  have transfer {s : TState} (hRegisters : ∀ r ∉ biasReleaseWritten true,
      s.regs r = c.ready.regs r) :
      Holds s.regs F ∧ (∀ i : Fin 16, BiasUnpacked true i s (fun k =>
        biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1)))) := by
    constructor
    · apply Epilogue.holdsSchedulerFrame (regs := F.map Prod.fst) c.checkpoint.2.2.2.2
      · intro r hr
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
        exact hRegisters x.1 (hStable x hx)
      · exact fun _ hx => List.mem_map_of_mem hx
    · intro i k hk
      have hI := i.isLt
      have hRegs (r : Nat) (hr : r = (biasUnpackRegs true i k).1 ∨
          r = (biasUnpackRegs true i k).2) : r ∉ biasReleaseWritten true := by
        simp only [biasUnpackRegs,biasUnpackTop,ite_true] at hr
        change r ∉ [8315,633,1051,4236,4237,4238]
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        omega
      exact ⟨(hRegisters _ (hRegs _ (.inl rfl))).trans (hBias i k hk).1,
        (hRegisters _ (hRegs _ (.inr rfl))).trans (hBias i k hk).2⟩
  by_cases hLane : laneOf l g = 0
  · rw [ite_eq_left hLane] at hStart
    let site := biasReleaseSite true
    obtain ⟨v,hSetup,hV⟩ := (biasReleaseSetup hp g warp true).apply hStart
    let newState := next (mbarStateDest v (some (signalSite site).state))
    have hSteps := c.localSteps.trans ((run_rtg hBranch).trans (run_rtg hSetup))
    obtain ⟨he,hPast,hAfter⟩ := signalOfMaximal hp hg (stageOf warp) site
      hV.1 hV.2.2.2.1 hV.2.2.2.2.1 hV.2.2.2.2.2.1
      c.recorded c.remaining hSteps c.positive c.bounded
      (fun hEnd => ⟨X,hMax,rfl,c.released hEnd⟩)
    have hRegisters r (hr : r ∉ biasReleaseWritten true) :
        newState.regs r = c.ready.regs r := by
      have hState : r ≠ (signalSite site).state := by
        intro heq
        exact hr (heq ▸ List.mem_cons_self)
      have hScratch : r ∉ biasReleaseSetupRegs true :=
        fun h => hr (List.mem_cons_of_mem _ h)
      have hFrame := biasReleaseSetupFrame true hStart.1 hSetup r hScratch
      simpa only [newState,next,mbarStateDest,Function.update_of_ne hState] using
        (hFrame.trans (hBranchFrame r))
    have hPc : newState.pc = biasBodyStart true := by
      change v.pc+1 = biasBodyStart true
      rw [hV.1]
      rfl
    have hAt : At newState (biasBodyStart true) F :=
      ⟨hPc,hV.2.1,hV.2.2.1,hV.2.2.2.1,(transfer hRegisters).1⟩
    let after : OpeningTripCursor l X g (biasBodyStart true) F :=
      ⟨c.pos+1,newState,newState,c.ending,by omega,len_of_get he,
        Prologue.releasedIfLast he (by intro h; cases h),hAt,hPast,hAfter,.refl⟩
    exact ⟨after,rfl,by simp only [after,ite_eq_left hLane],fun _ => he,
      (transfer hRegisters).2⟩
  · rw [ite_eq_right hLane] at hStart
    have hFacts := transfer (fun r _ => hBranchFrame r)
    let after : OpeningTripCursor l X g (biasBodyStart true) F :=
      ⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hStart.mono hFacts.1,
        c.recorded,c.remaining,c.localSteps.trans (run_rtg hBranch)⟩
    exact ⟨after,rfl,by simp only [after,ite_eq_right hLane],fun h => (hLane h).elim,hFacts.2⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
