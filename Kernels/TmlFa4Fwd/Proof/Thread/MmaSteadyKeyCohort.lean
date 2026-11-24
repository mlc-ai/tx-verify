-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyOpeningCohorts
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyKeyWait

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- One delivered K cohort advances the actual first-product cursor to its QK
setup, returning the successful wait as well as the exact count change. -/
theorem steadyKeyPollOfDelivered {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g visit remaining shuffles votes : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 12)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2344
      (fun _ => ((2595,b32 (valueDescriptorLow l (2*visit+1)))::
        steadyValueFrame l visit remaining) ++ steadyIterationRoots l) shuffles votes ends)
    (hDelivered : Protocol.LoaderReady.DeliveredCohort l X g
      (readyStage (2*visit+2)) ((2*visit+2)/3))
    (hOrdinal : ∀ lane < 32,
      okPolls ⟨.shared,g/l.block,readyAddr l (2*visit+2)⟩
        ((X.tr (warpLane l g lane)).take (cur.pos lane)) = (2*visit+2)/3) :
    ∃ done : SchedulerWarpReached l X g 2355
      (fun _ => steadyFirstQkFrame l visit remaining true) shuffles votes ends,
      ∀ lane < 32, cur.pos lane < done.pos lane ∧
        Thread.Mma.ReadyPoll l X (warpLane l g lane) (done.pos lane-1)
          (readyStage (2*visit+2)) (readyWord (2*visit+2)) true .cta ∧
        (∀ other, okPolls other ((X.tr (warpLane l g lane)).take (done.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) +
            if other = ⟨.shared,g/l.block,readyAddr l (2*visit+2)⟩ then 1 else 0) ∧
        elections X (warpLane l g lane) (done.pos lane) =
          elections X (warpLane l g lane) (cur.pos lane) := by
  let value := (2595,b32 (valueDescriptorLow l (2*visit+1)))
  let extra := value::steadyIterationRoots l
  obtain ⟨base,hBase⟩ := cur.advanceLocalWithPosition (pc' := 2344)
    (G := fun _ => steadyValueFrame l visit remaining ++ extra) (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hf := (holds_append ..).mp ht.2.2.2.2.2
      exact ⟨_,.refl,ht.mono ((holds_append ..).mpr ⟨hf.1,ht.2.2.2.2.1,hf.2⟩)⟩)
  obtain ⟨poll,hPoll⟩ := steadyKeyWaitReachedFramedWithPosition hp base (by
    change ((kernel.code.drop 2344).take 8).all
      (fun ins => (2595::(steadyIterationRoots l).map Prod.fst).all
        (fun r => !(writesRegs ins.op).contains r)) = true
    rw [steadyIterationRoots_regs]
    decide +kernel)
  obtain ⟨next,hNext⟩ := mmaWarpCachePollOfDelivered hp hMax hg hWarp 6 poll
    (fun _ _ => by
      refine ⟨?_,?_,?_⟩
      · intro pair hm
        rcases List.mem_append.mp hm with hm | hm
        · simp [steadyKeyFrame,steadyKeyRing,steadyValueFrame,steadyFrame,steadyPorts,waitSite]
            at hm ⊢
          aesop
        · rcases List.mem_cons.mp hm with rfl | hm
          · change (2595 : Nat) ≠ 9681
            decide
          · exact fun he => (by decide : (waitSite 6).result ∉ steadyIterationRootRegs)
              (he ▸ steadyIterationRoots_valid l pair hm)
      · simp [steadyKeyFrame,waitSite]
      · simp [steadyKeyFrame,steadyKeyRing,waitSite])
    (by rw [hPoll,hBase]; exact hOrdinal) hDelivered
  obtain ⟨done,hDone⟩ : ∃ out : SchedulerWarpReached l X g 2355
      (fun _ => steadyFirstQkFrame l visit remaining true) shuffles votes ends,
      out.pos = next.pos := by
    apply next.advanceLocalWithPosition
    intro lane hl
    have ht := next.checkpoint lane hl
    have hf := (holds_append ..).mp ht.2.2.2.2
    have hr := (holds_append ..).mp hf.2.2
    refine ⟨_,.refl,ht.mono ?_⟩
    unfold steadyFirstQkFrame steadyValueCarry
    exact (holds_append ..).mpr ⟨(holds_append ..).mpr ⟨(holds_append ..).mpr
      ⟨hf.1,hr.1⟩,hf.2.1,trivial⟩,hr.2⟩
  refine ⟨done,?_⟩
  intro lane hl
  have hData := hNext lane hl
  rw [hDone]
  rw [hPoll,hBase] at hData
  refine ⟨hData.1,?_,hData.2.2.1,hData.2.2.2⟩
  have hCta : (warpLane l g lane)/l.block = g/l.block :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.2.symm
  refine ⟨_,hData.2.1,?_⟩
  simp only [Thread.Mma.Observation.readyObject,Loader.readySlot_address,hCta,readyAddr,
    Nat.add_assoc]

end
end PTX.Kernels.TmlFa4Fwd.Mma
