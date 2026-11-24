-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Polls.Role
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Free
public import Kernels.FlashAttn4Fwd.Proof.Protocol.FreeBlocked

@[expose] public section

/-! # The staging-free polls have a blocker

A correction thread at `fWait st` or at the tail's `tailWait` (stage 1) polls the stage's free
barrier (`FreePollFacts.poll`), which has a final state (`state_of_time`). When that state's phase
has the poll's parity, a store lane of its CTA is one free arrival short of the thread's
successful polls (`Output.free_short`, in a safe execution, whose histories do not fault), so it
lags the thread (`FreePollFacts.lag`) and is a blocker (`Sched.blk_of_lags`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- **A correction thread at a staging-free poll polls with a blocker when not ready.** -/
theorem free_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (hW : WaitInputs L X)
    (hF : FreePollFacts L X) {g : Nat} (hp : Frame.Pending L X g)
    (_hrel : Step.Released L X g)
    {d : Correction.D} (hσ : St L X g (X.tr g).length = some (some (.inr (.corr d))))
    (hsite : (∃ st, d.site = .fWait st) ∨ d.site = .tailWait) :
    Sched.PollBlocked (timed L) X g := by
  have hX := hmax.1
  have hg : g < L.threads := hp.1
  have hw := (prologueFacts hpre hX).role_warp hg hσ
  obtain ⟨st, hfs⟩ : ∃ st, FreeSite d.site st := by
    rcases hsite with ⟨st, h⟩ | h
    · exact ⟨st, Or.inl h⟩
    · exact ⟨1, Or.inr ⟨h, rfl⟩⟩
  have ht : Time.regT < stateTime L g (.inr (.corr d)) := by
    rcases hfs with h | ⟨h, -⟩ <;> simp only [stateTime, Time.correction, h, Time.tailTime] <;>
      exact Time.fixed_lt (by decide)
  obtain ⟨before, hstate⟩ := state_of_time hpre hX hI hW hg hσ ht (.oFree st)
  refine Sched.pollBlocked_of (hF.poll hg hσ hfs) hstate (fun hpar => ?_)
  obtain ⟨b, hb⟩ := Output.free_short hpre hX hI.output hW.tmem
    (InitFirst.outputInit hpre hX hI.cluster hW.tmem hI.init hI.output)
    (fun w pc _ _ _ _ he => hI.rings.spins (Frame.lt_of_get hX he) he) st.isLt ⟨hg, rfl, hw.1, hw.2⟩
    (fun _ hr => InitFirst.fault_free (hs.2 X hX) hr) hstate hpar
  obtain ⟨hy, hcy⟩ := Output.storeThread_facts hpre (cta_lt hg) b
  have hwy : warpOf L (Output.storeThread L (ctaOf L g) b) = 13 := by
    have := b.isLt
    simp only [Output.storeThread, warpOf, hpre.block]
    omega
  refine Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg (ne_nil_of_role hσ) hσ hy
    (congrArg L.clusterOfCta hcy)
    (hF.lag hg hy hcy hwy hσ hfs (by omega))

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
