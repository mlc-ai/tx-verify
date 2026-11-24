-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # A final O store follows the stage's final O poll

A shared store of a correction lane is a final store of a stage `st` (`FstAt`): the lane has polled
the stage's final O barrier (`144 + 8 st`) successfully once, with parity 0, and has not yet arrived
on the stage's ready barrier (`208 + 8 st`): `corr_fst`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before inRound)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

/-- The stage of a final store site. -/
private def fstOf : Correction.Site → Option (Fin 2)
  | .fst st _ _ => some st
  | _ => none

private theorem fst_tab : ∀ q : Fin 2,
    (∀ s ∈ Correction.allSites, fstOf s = some q →
      (ptsOf (.acquire (144 + 8 * q.val))).countP (before s) = 1 ∧
        (ptsOf (.arrive (208 + 8 * q.val))).countP (before s) = 0) ∧
    (ptsOf (.acquire (144 + 8 * q.val))).countP inRound = 0 ∧
    (ptsOf (.arrive (208 + 8 * q.val))).countP inRound = 0 := by
  decide +kernel

/-- **A shared store of a correction lane**: a final store of a stage whose O poll the lane has made
and whose ready arrival it has not. -/
theorem corr_fst (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, k) = some ⟨pc, .wr a bs⟩)
    (hsh : a.loc.space = .shared) : ∃ st : Fin 2, Correction.FstAt L h st a ∧
      okPolls (obj L h (144 + 8 * st.val)) ((X.tr h).take k) = 1 ∧
      arrivals (obj L h (208 + 8 * st.val)) ((X.tr h).take k) = 0 := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨d, n, hσ, h0, hR, hi, hev1, hevR⟩
  · exact (start_mem hev hi.2 trivial).elim
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (fun _ => nofun)
  obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, hF⟩ := hR h0
  obtain ⟨st, jj, hh, hs⟩ : ∃ st jj hh, d.site = .fst st jj hh := by
    have hev1 := hev1.data_or_vote.resolve_right (by rintro ⟨_,_,h⟩; cases h)
    cases hs : d.site <;>
      simp only [Correction.Ev, show d.scheduler.site = d.site from rfl, hs] at hev1
    case fst st jj hh => exact ⟨st, jj, hh, rfl⟩
    case lse hh =>
      rcases hev1 with ⟨a', bs', hk⟩ | ⟨f, hk⟩
      · have := Correction.lse_wr hat hc hf ⟨hh, hs⟩ rfl
        rw [hsh] at this
        cases this
      · cases hk
    all_goals exfalso
    all_goals try simp only [Epilogue.Ev, Correction.Site.toE, Correction.rdOrUb] at hev1
    all_goals first
      | contradiction
      | (rcases hev1 with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h; done)
      | (rcases hev1 with ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> cases h; done)
      | (rcases hev1 with h | ⟨_, h⟩ <;> cases h; done)
      | (rcases hev1 with h | ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> cases h; done)
      | (obtain ⟨_, _, _, h⟩ := hev1; cases h; done)
      | (obtain ⟨_, _, h⟩ := hev1; cases h; done)
      | (obtain ⟨_, h⟩ := hev1; cases h; done)
  refine ⟨st, Correction.fst_at hp hat hc hf hs rfl, ?_, ?_⟩
  all_goals
    obtain ⟨t1, t2, t3⟩ := fst_tab st
    obtain ⟨e1, e2⟩ := t1 _ (Correction.mem_allSites d.site) (by rw [hs]; rfl)
  · have c1 : n (.corr (.acquire (144 + 8 * st.val))) = _ := hQ.cnt _ (by simp)
    simp only [Correction.Control.D.scheduler] at c1
    rw [corr_okPolls, count hσ, c1, passed, e1, t2, Nat.mul_zero]
  · have c1 : n (.corr (.arrive (208 + 8 * st.val))) = _ := hQ.cnt _ (by simp)
    simp only [Correction.Control.D.scheduler] at c1
    rw [corr_arrivals, count hσ, c1, passed, e2, t3, Nat.mul_zero]

/-- **The final O poll of a stage** is one, of parity 0, with acquire semantics. -/
theorem corr_o_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    (st : Fin 2) (hk : 1 ≤ okPolls (obj L h (144 + 8 * st.val)) ((X.tr h).take k)) :
    ∃ j < k, ∃ pc, X.get (h, j) =
      some ⟨pc, .wait (obj L h (144 + 8 * st.val)) 0 true true .cta⟩ := by
  obtain ⟨j, pc, par, acq, sc, hjk, he, hcnt⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (m := obj L h (144 + 8 * st.val)) (h := h) (f := k)
      (c := 0) (by omega)
  have hst := st.isLt
  rcases corr_mbar_use hp hX hFw hw hw1 he (l := obj L h (144 + 8 * st.val)) rfl
    (fun _ h => by cases h) with ⟨_, -, -, hk'⟩ | ⟨o, ok, -, hl, hk'⟩
  · cases hk'
  · obtain rfl := (obj_off hl).2
    simp only [Kind.wait.injEq] at hk'
    obtain ⟨-, hpar, -, rfl, rfl⟩ := hk'
    rw [hcnt] at hpar
    have : par = 0 := by
      rw [hpar]
      unfold corrΔ
      rw [ite_eq_right (by omega)]
    subst this
    exact ⟨j, hjk, pc, he⟩

private theorem ready_tab : ∀ q : Fin 2, (∀ s ∈ Correction.allSites,
    Correction.arrOff s = 208 + 8 * q.val →
      (ptsOf (.acquire (144 + 8 * q.val))).countP (before s) = 1) ∧
    (ptsOf (.acquire (144 + 8 * q.val))).countP inRound = 0 := by
  decide +kernel

/-- **A ready arrival follows the stage's final O poll.** -/
theorem corr_ready_o (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    (st : Fin 2) {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L h (208 + 8 * st.val)) tx c rel sc⟩) :
    okPolls (obj L h (144 + 8 * st.val)) ((X.tr h).take k) = 1 := by
  rcases corr_counts_nonvote hp hX hFw hw hw1 he (fun _ => nofun) (fun _ _ => nofun) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, -, hev, hc⟩
  · obtain ⟨c', hc'⟩ := start_mbar hev hx (l := obj L h (208 + 8 * st.val)) rfl
    cases hc'
  rcases corr_mbar2 hev (l := obj L h (208 + 8 * st.val)) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  obtain ⟨t1, t2⟩ := ready_tab st
  rw [corr_okPolls, hc, hQ.cnt _ (by simp), passed,
    t1 _ (Correction.mem_allSites _) (obj_inj hl).symm, t2, Nat.mul_zero]

end
end PTX.Kernels.TmlFa4Fwd.Proof
