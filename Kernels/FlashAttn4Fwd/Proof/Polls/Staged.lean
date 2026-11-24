-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Polls.Role
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Staged
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StagedBlocked

@[expose] public section

/-! # The staged polls have a blocker

A store lane at its `wait st` site polls stage `st`'s staged barrier (`StagedPollFacts.poll`),
which has a final state (`state_of_time`). When that state's phase has the poll's parity, a
correction thread of its CTA has no more staged arrivals than the lane's successful polls
(`Output.staged_short`, in a safe execution, whose histories do not fault), so it lags the lane
(`StagedPollFacts.lag`) and is a blocker (`Sched.blk_of_lags`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- **A store lane at a staged poll polls with a blocker when not ready.** -/
theorem staged_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (hW : WaitInputs L X)
    (hF : StagedPollFacts L X) {g : Nat} (hp : Frame.Pending L X g)
    (_hrel : Step.Released L X g)
    {d : Store.D} (hσ : St L X g (X.tr g).length = some (some (.inr (.store d))))
    (hsite : ∃ st, d.site = .wait st) : Sched.PollBlocked (timed L) X g := by
  have hX := hmax.1
  have hg : g < L.threads := hp.1
  have hw : warpOf L g = 13 := (prologueFacts hpre hX).role_warp hg hσ
  obtain ⟨st, hst⟩ := hsite
  have ht : Time.regT < stateTime L g (.inr (.store d)) := by
    simp only [stateTime, Time.store, hst, Time.storeAt]
    exact Time.fixed_lt (by decide)
  obtain ⟨before, hstate⟩ := state_of_time hpre hX hI hW hg hσ ht (.oStaged st)
  refine Sched.pollBlocked_of (hF.poll hg hσ hst) hstate (fun hpar => ?_)
  obtain ⟨a, ha⟩ := Output.staged_short hpre hX hI.output hW.tmem
    (InitFirst.outputInit hpre hX hI.cluster hW.tmem hI.init hI.output)
    (fun w pc _ _ _ _ he => hI.rings.spins (Frame.lt_of_get hX he) he) st.isLt ⟨hg, rfl, hw⟩
    (fun _ hr => InitFirst.fault_free (hs.2 X hX) hr) hstate (by simpa using hpar)
  obtain ⟨hy, hcy, hwy⟩ := Stats.corrThread_facts hpre (cta_lt hg) a
  refine Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg (ne_nil_of_role hσ) hσ hy
    (congrArg L.clusterOfCta hcy)
    (hF.lag hg hy hcy (by omega) (by omega) hσ hst (by omega))

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
