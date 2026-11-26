-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.FollowD
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.StrictChain
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Shape
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Nc
import Lemmas.Kernel.StrictSite

@[expose] public section

/-! # Warpgroup 2 makes no undefined behaviour

`dequant_noUb`: an event fired from a state of warpgroup 2 of a followed lane is no undefined
behaviour, and the machine stops at it only if it is the exit, when the data the lane read is valid
before every event (`hdq`, from the lane's own events being no undefined behaviour:
`Protocol/Values/DqValid.lean`).

The state before the event of the data thread machine is strictly good and fires the event from its
site's template (`dq_strict`: the step before it is strict, by the startup's or by
`dataStepFor_all`), so each site's template is no fault: the set-up and the barrier by the shape
table, the polls and the shared accesses at aligned addresses of the lane (`dq_nonub`), the length
loads through a set pointer (`deq_words`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Dequant

/-- The set-up's pointers are set at the length loads (from the words the state has recorded). -/
private theorem lenOk_of_words {d : Control.D} (h : deqWordsOk P L g d) : LenOk P d := by
  constructor
  · intro hs
    simp only [deqWordsOk, hs] at h
    exact h.1
  · intro hs
    simp only [deqWordsOk, hs] at h
    exact h.1


/-- The machine stops at a warpgroup-2 event only at the exit. -/
private theorem stop_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Control.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .dequant, d⟩, n)))
    (hnu : ∀ f, e.kind ≠ .ub f) (h : Control.succ P L g d e = none) : e.kind = .exit := by
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := deq_fired hp hX he hnu hσ
  have hok := deq_words hp hX hσ d n rfl
  obtain ⟨-, hk⟩ := shape hp hat hi hc hf
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | exit => simpa [EvK] using hk
  | lenA =>
    simp only [deqWordsOk] at hok
    rw [Control.deq_topk hp hX he hat hi hc hf hok.1 rfl] at h
    simp at h
  | lenB =>
    simp only [deqWordsOk] at hok
    rw [Control.deq_extra hp hX he hat hi hc hf hok.1 rfl] at h
    simp at h
  | smr | fpx | arrD | arrF | bar | store _ _ => simp [Control.succ] at h
  | wq =>
    simp only [EvK, PollEv] at hk
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · simp [Control.succ, hk] at h
    · exact absurd hk (hnu f)
  | wraw | wsv =>
    simp only [EvK, PollEv] at hk
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · simp [Control.succ, Control.poll, hk] at h
    · exact absurd hk (hnu f)
  | scale _ =>
    simp only [EvK, LoadEv] at hk
    rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · simp [Control.succ, hk] at h
    · exact absurd hk (hnu f)
  | raw _ _ =>
    simp only [EvK, LoadEv] at hk
    rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · simp [Control.succ, Control.dataRd, hk] at h
    · exact absurd hk (hnu f)

end Dequant


open Dequant Dequant.Data in
/-- **Warpgroup 2 makes no undefined behaviour.** -/
theorem dequant_noUb (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hdq : ∀ g k, NoUbBefore X g k → DqValid X g k)
    (g k : Nat) (e : Event) (he : X.get (g, k) = some e) (ha : AliveIn P L X g k .dequant) :
    (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit) := by
  obtain ⟨σ, hσ, hr⟩ := aliveIn_iff.mp ha
  cases hr with
  | dequant d n =>
  have hg := Frame.lt_of_get hX he
  have hJ := (follow_iff.mp hFw g hg k).2 _ hσ
  have hw : 8 ≤ warp L g ∧ warp L g < 12 := by
    obtain ⟨-, -, -, hg2⟩ := hJ
    have hg3 : wgOf L g = 2 := hg2
    simp only [wgOf, tidOf] at hg3
    simp only [warp]
    omega
  have hk := noUbBefore_of_get hX he
  have hv := hdq g k hk
  obtain ⟨st, hst, -, -⟩ := followD hp hX hFw hw he ⟨_, hσ⟩ hv k le_rfl
  have h1 := control_of_data hst
  rw [hσ] at h1
  obtain ⟨dD, nD, rfl, hdc⟩ : ∃ dD nD, st = (.inr ⟨.inl .dequant, dD⟩, nD) ∧ dD.c = d := by
    rcases deq_slot hFw hw hg hst with ⟨b, hb⟩ | ⟨dD, hdD⟩
    · obtain ⟨q, nq⟩ := st
      obtain rfl : q = .inl b := hb
      simp [eraseThread, Code.eraseSum] at h1
    · obtain ⟨q, nq⟩ := st
      obtain rfl : q = .inr ⟨.inl .dequant, dD⟩ := hdD
      simp [eraseThread, Code.eraseSum, Code.eraseStubs, eraseFrag, dequantErase] at h1
      exact ⟨dD, nq, rfl, h1.1.symm⟩
  obtain ⟨t, o, ins, hgood, hc, hf⟩ := Frame.strict_site (C := threadD P L)
    (fun _ _ => threadD_sound hp) hX he hst (fun j dj ej hj hej hs hn =>
      dq_prev hp hX hFw hw hj he hv (fun f ej' hget => hk.ne (by omega) hget f) hej hs hn)
  have hlen : LenOk P dD.c := by
    rw [hdc]
    exact lenOk_of_words (deq_words hp hX hσ d n rfl)
  have hnu := dq_nonub (w := warpW L g) hp dD hlen hgood.1 hgood.2 hc hf
  refine ⟨hnu, fun hs => ?_⟩
  have h1' := Code.counted_next_eq_none_iff.mp (next_none_of_stops he hσ hs)
  have h2 : Control.succ P L g d e = none := by
    simpa only [Code.glue_next_inr, Option.map_eq_none_iff] using h1'
  exact stop_exit hp hX he hσ hnu h2

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
