-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Polls.Role
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Credit
public import Kernels.FlashAttn4Fwd.Proof.Protocol.CreditBlocked

@[expose] public section

/-! # The statistics credit polls have a blocker

A softmax thread at a credit poll (`statsW k`) polls its stage's credit barrier
(`CreditPollFacts.poll`), which has a final state (`state_of_time`). When that state's phase has
the poll's parity, a correction thread of its CTA is one credit arrival short of the thread's
successful polls (`Stats.credit_short`, in a safe execution, whose histories do not fault), so it
lags the thread (`CreditPollFacts.lag`) and is a blocker (`Sched.blk_of_lags`). The credit gate
needs the partner arrival premise `Stats.SoftArrives` (`Stats.softArrives`, from `OlderFacts`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- **A softmax thread at a credit poll polls with a blocker when not ready.** -/
theorem credit_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (hW : WaitInputs L X)
    (hF : CreditPollFacts L X) (hsoft : Stats.SoftArrives L X) {g : Nat}
    (hp : Frame.Pending L X g) (_hrel : Step.Released L X g)
    {d : Softmax.D} (hσ : St L X g (X.tr g).length = some (some (.inr (.softmax d))))
    (hsite : ∃ k, d.site = .statsW k) : Sched.PollBlocked (timed L) X g := by
  have hX := hmax.1
  have hg : g < L.threads := hp.1
  have hw : warpOf L g < 8 := (prologueFacts hpre hX).role_warp hg hσ
  have hst : warpOf L g / 4 < 2 := by omega
  have ht : Time.regT < stateTime L g (.inr (.softmax d)) := by
    obtain ⟨k, hk⟩ := hsite
    simp only [stateTime, Time.softmax, hk]
    fin_cases k <;> simp only [Time.tailTime] <;> exact Time.fixed_lt (by decide)
  obtain ⟨before, hstate⟩ := state_of_time hpre hX hI hW hg hσ ht (.stats ⟨_, hst⟩)
  refine Sched.pollBlocked_of (hF.poll hg hσ hsite) hstate (fun hpar => ?_)
  obtain ⟨a, ha⟩ := Stats.credit_short hpre hX hW.stats hW.tmem
    (InitFirst.statsInit hpre hX hI.cluster hW.tmem hI.init hW.stats) hsoft
    (fun w pc _ _ _ _ he => hI.rings.spins (Frame.lt_of_get hX he) he) hst ⟨hg, rfl, hw, rfl⟩
    (fun _ hr => InitFirst.fault_free (hs.2 X hX) hr) hstate hpar
  obtain ⟨hy, hcy, hwy⟩ := Stats.corrThread_facts hpre (cta_lt hg) a
  refine Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg (ne_nil_of_role hσ) hσ hy
    (congrArg L.clusterOfCta hcy)
    (hF.lag hg hy hcy (by omega) (by omega) hσ hsite (by omega))

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
