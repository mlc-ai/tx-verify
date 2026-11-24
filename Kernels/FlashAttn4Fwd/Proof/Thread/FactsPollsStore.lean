-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsOn
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStore
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Staged

@[expose] public section

/-! # The store lane's staged polls

`StagedPollFacts.poll`: a store lane at its `wait st` site of item `i` polls stage `st`'s staged
barrier of its CTA with the parity `i % 2` (`Store.Ev`), which is that of its
successful polls of the barrier, one per earlier item (`Store.Counts.staged`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`StagedPollFacts.poll`**. -/
theorem StagedPollFacts_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat} {d : Store.D} {st : Fin 2}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.store d))) → d.site = .wait st →
        PollsOn L X g (stagedBar L (ctaOf L g) st) 0 := by
  intro g d st hg hσ hs
  obtain ⟨site, i⟩ := d
  simp only at hs
  subst hs
  refine pollsOn_of_end hpre hX ht hg hσ rfl (fun _ t ins hat hi hc f hf => ?_)
    (fun hJ t ins hat hi hc l p ok acq sc u hfire => ?_)
  · have hfu : Fires (Store.Site.wait st).pc (eventTmpl asms L g t ins.op)
        ⟨(Store.Site.wait st).pc, .ub f⟩ none := by
      rw [hf]
      exact ⟨rfl, rfl⟩
    obtain ⟨_, h⟩ := Store.shape hpre hat hi hc hfu
    cases h
  · obtain ⟨_, hs, rfl, rfl, -⟩ := Store.ev_wait (Store.shape hpre hat hi hc hfire)
    cases hs
    have hJ' : Store.Counts L g ⟨.wait st, i⟩ (X.tr g) := hJ
    have hs := hJ'.staged st
    rw [Store.stagedAt_eq] at hs ⊢
    refine ⟨rfl, ?_⟩
    rw [hs]
    simp [Store.done, Store.before]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
