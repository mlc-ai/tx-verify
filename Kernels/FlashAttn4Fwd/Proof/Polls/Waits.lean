-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.PollWaits
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsArrives
public import Kernels.FlashAttn4Fwd.Proof.SafeGlue2
public import Kernels.FlashAttn4Fwd.Proof.Polls.Loader
public import Kernels.FlashAttn4Fwd.Proof.Polls.MmaRing
public import Kernels.FlashAttn4Fwd.Proof.Polls.PReady
public import Kernels.FlashAttn4Fwd.Proof.Polls.P2
public import Kernels.FlashAttn4Fwd.Proof.Polls.Handshake
public import Kernels.FlashAttn4Fwd.Proof.Polls.SFull
public import Kernels.FlashAttn4Fwd.Proof.Polls.Credit
public import Kernels.FlashAttn4Fwd.Proof.Polls.OFull
public import Kernels.FlashAttn4Fwd.Proof.Polls.Free
public import Kernels.FlashAttn4Fwd.Proof.Polls.Staged

@[expose] public section

/-! # Every mbarrier poll has a blocker when its object is not ready

This file sits outside the layers (as `ProgressFacts.lean` does): it joins the thread layer's
`ProgressPolls` and the protocols' blocker exports into the progress layer's `PollsBlocked`. A
released pending thread at a poll is at one of the wait classes, picked by its site, and the
class lemma (`Polls/*.lean`) gives `PollBlocked` (`pollBlocked_at`). The statistics credit class
uses `Stats.SoftArrives`, from the older facts (`Stats.softArrives`); the S-full and O-full
classes use the routes' context (`routeCtx`, as the safety glue builds it). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A thread at an mbarrier poll has a blocker when the object is not ready**, by its wait
class. -/
theorem pollBlocked_at (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (hW : WaitInputs L X)
    (hQ : ProgressPolls L X) (hN : PollInputs P L X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) {d : ThreadD}
    (hσ : St L X g (X.tr g).length = some (some d)) (hk : nextKind d = .wait) :
    Sched.PollBlocked (timed L) X g := by
  have hX := hmax.1
  have hsoft : Stats.SoftArrives L X := Stats.softArrives hpre hX hW.stats hN.older
  have hRC := routeCtx hpre hX hN.route hN.pready hN.p2 hN.sfull hN.ofull hW.stats hI.tmem
    hI.init hI.cluster hsoft fun w pc _ _ _ _ he => hI.rings.spins (Frame.lt_of_get hX he) he
  rcases d with p | r
  · cases hs : p.site <;> simp [nextKind, prologueKind, hs] at hk
  · cases r with
    | idle s => cases hs : s.site <;> simp [nextKind, idleKind, hs] at hk
    | loader d => exact loader_pollBlocked hpre hs hmax hI hW hQ.loader hp hrel hσ hk
    | mma d =>
      cases hsite : d.site <;> simp [nextKind, mmaKind, hsite] at hk
      · exact mmaRing_pollBlocked hpre hs hmax hI hW hQ.mmaRing hp hrel hσ (.inl ⟨_, hsite⟩)
      · exact mmaRing_pollBlocked hpre hs hmax hI hW hQ.mmaRing hp hrel hσ (.inr ⟨_, hsite⟩)
      · exact pReady_pollBlocked hpre hs hmax hI hW hQ.pReady hRC hp hrel hσ ⟨_, hsite⟩
      · exact p2_pollBlocked hpre hs hmax hI hW hQ.p2 hRC hp hrel hσ ⟨_, _, hsite⟩
      · exact handshake_pollBlocked hpre hs hmax hI hW hQ.handshake hp hrel hσ hsite
    | store d =>
      cases hsite : d.site <;> simp [nextKind, storeKind, hsite] at hk
      exact staged_pollBlocked hpre hs hmax hI hW hQ.staged hp hrel hσ ⟨_, hsite⟩
    | softmax d =>
      cases hsite : d.site <;> simp [nextKind, softmaxKind, hsite] at hk
      · exact credit_pollBlocked hpre hs hmax hI hW hQ.credit hsoft hp hrel hσ ⟨_, hsite⟩
      · exact sFull_pollBlocked hpre hs hmax hI hW hQ.sFull hRC hp hrel hσ ⟨_, hsite⟩
    | corr d =>
      cases hsite : d.site <;> simp [nextKind, corrKind, hsite] at hk
      · exact oFull_pollBlocked hpre hs hmax hI hW hQ.oFull hRC hp hrel hσ ⟨_, hsite⟩
      · exact free_pollBlocked hpre hs hmax hI hW hQ.free hp hrel hσ (.inl ⟨_, hsite⟩)
      · exact free_pollBlocked hpre hs hmax hI hW hQ.free hp hrel hσ (.inr hsite)

/-- **`PollsBlocked` from the thread layer's facts**, for every consistent execution. -/
theorem pollsBlocked (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hA : ∀ X, Consistent L kernel asms mem0 X → AsyncInputs P L X)
    (hW : ∀ X, Consistent L kernel asms mem0 X → WaitInputs L X)
    (hQ : ∀ X, Consistent L kernel asms mem0 X → ProgressPolls L X)
    (hN : ∀ X, Consistent L kernel asms mem0 X → PollInputs P L X) : PollsBlocked L mem0 :=
  fun X _ _ hmax hp hrel hσ hk =>
    pollBlocked_at hpre hs hmax (hA X hmax.1) (hW X hmax.1) (hQ X hmax.1) (hN X hmax.1) hp hrel
      hσ hk

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
