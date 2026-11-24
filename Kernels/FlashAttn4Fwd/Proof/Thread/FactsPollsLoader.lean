-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsOn
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderUb
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Loader

@[expose] public section

/-! # The loader's polls

`LoaderPollFacts.poll`: a loader thread at a poll site is a lane of warp 14, whose next event
polls the empty barrier of its CTA that the site's ring use names (`Loader.wait_fact`; the ring
register is the use's slot, `Loader.Counts.ring`), with the parity of its successful polls of it
plus one; the site's template is never undefined behaviour (`Cross.SitesTmplOk_loader`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The barrier a loader poll site polls is the partner of `loaderPollBar`. -/
theorem waitBar_partner {g : Nat} {d : Loader.D} (hk : loaderKind d.site = .wait)
    (hs : d.s = Loader.kvB L g d % 6) :
    Loader.waitBar d.site (Loader.kvB L g d) = (loaderPollBar d).partner := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  cases site <;> simp only [loaderKind, reduceCtorEq] at hk
  case wait u =>
    cases u <;> simp only [Loader.waitBar, loaderPollBar, FBar.partner, FBar.kvEmpty.injEq,
      Fin.ext_iff] <;> omega
  case drain k =>
    simp only [Loader.waitBar, loaderPollBar, FBar.partner, FBar.kvEmpty.injEq, Fin.ext_iff]
    omega
  case drainQ => rfl

/-- **`LoaderPollFacts.poll`**. -/
theorem LoaderPollFacts_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat} {d : Loader.D}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.loader d))) → loaderKind d.site = .wait →
        warpOf L g = 14 ∧ PollsOn L X g ((loaderPollBar d).partner.loc L (ctaOf L g)) 1 := by
  intro g d hg hσ hk
  refine ⟨Cross.role_of_state hpre hX hg hσ, ?_⟩
  refine pollsOn_of_end hpre hX ht hg hσ hk
    (fun _ t ins hat hi hc f => Cross.SitesTmplOk_loader hpre hg d t ins hat hi hc f)
    (fun hJ t ins hat hi hc l p ok acq sc u hf => ?_)
  have hJ' : Loader.Counts L g d (X.tr g) := hJ
  obtain ⟨b, hb, hm, hp, -, hbw, -⟩ := Loader.wait_fact hpre hg hJ' hi
    ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf rfl
  rw [waitBar_partner hk hJ'.ring.1] at hbw
  subst hbw
  refine ⟨hm, ?_⟩
  have hoff : ((loaderPollBar d).partner).pollOffset = 1 := by
    revert hb
    cases (loaderPollBar d).partner <;> simp [FBar.isEmpty, FBar.pollOffset]
  rw [hp, ← hm, hoff]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
