-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IdleLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Shape
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Steps
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads

@[expose] public section

/-! # Warpgroup 1's head and idle code make no undefined behaviour

`wg1_noUb`: an event fired from a state of the head or the idle code of a followed lane is no
undefined behaviour, and the machine stops at it only if it is an exit. The state before the event
is strictly good (`strict_event_nontma`: the step before it is strict, the head's shuffle for the
words `4`, `5` and the idle code's by `Wg1.stepFor_hsh`), so the event is its site's:

* the head's events are the `setmaxnreg` and the shuffle, whose dispatch follows every word;
* the idle code's length loads read through a set pointer (`idle_ok`): a `.nc` read of the row's
  word (`Wg1.idle_topk_read`), whose four bytes `Pre` gives (`rebuild_topk`); its barrier and its
  return are no undefined behaviour by their shapes. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **Warpgroup 1's head and idle code make no undefined behaviour.** -/
theorem wg1_noUb (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (g k : Nat) (e : Event) (he : X.get (g, k) = some e) (ha : AliveIn P L X g k .wg1) :
    (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit) := by
  obtain ⟨σ, hσ, hr⟩ := aliveIn_iff.mp ha
  obtain ⟨t, o, ins, hgood, hc, hf⟩ := strict_event_nontma hp hX he hσ (.inl hr)
  have hnone := fun hs => next_none_of_stops he hσ hs
  cases hr with
  | head s n =>
    obtain ⟨hat, hinv⟩ := hgood
    have hex : Wg1.exitOf s = none := by
      simpa [wg1Enter] using Code.gatedExit_none.mp hinv.2
    have hev : Wg1.Ev L g s e := Wg1.shape hp (g := g) hat hinv.1 hc hf
    cases s with
    | smr =>
      obtain ⟨inst, h⟩ := hev
      refine ⟨fun f hk => (by rw [h] at hk; cases hk), fun hs => ?_⟩
      have := thread_next_none_head (hnone hs)
      simp [Wg1.succ] at this
    | hsh =>
      obtain ⟨r, ok, h⟩ := hev
      refine ⟨fun f hk => (by rw [h] at hk; cases hk), fun hs => ?_⟩
      have := thread_next_none_head (hnone hs)
      obtain ⟨pc, kd⟩ := e
      simp only at h
      subst h
      exact absurd this (by simpa [Wg1.succ] using Wg1.dispatch_ne r)
    | _ => simp [Wg1.exitOf] at hex
  | idle s n =>
    obtain ⟨hat, hinv⟩ := hgood
    have hev : Wg1.IEv s e := Wg1.ishape hp (g := g) hat hinv.1 hc hf
    have hok : idleOk P s := idle_ok hσ s n rfl
    have hrow := (ctaid_lt hp g).2
    cases s with
    | ldA =>
      obtain ⟨x, hx⟩ := len_ptr hok
      obtain ⟨bs, hr⟩ := Wg1.idle_topk_read hp hx rfl hat hc hf
      refine ⟨fun f hk => (by rw [hr.1] at hk; cases hk), fun hs => ?_⟩
      have h0 := thread_next_none_sub (hnone hs)
      have hb := rebuild_topk hp hX hrow hx he hr
      simp only [subFrag, idleCode, Wg1.idle, Wg1.isucc, Wg1.afterNc, hr.1, hb] at h0
      cases h0
    | ldB =>
      obtain ⟨x, hx⟩ := len_ptr hok
      obtain ⟨bs, hr⟩ := Wg1.idle_extra_read hp hx rfl hat hc hf
      refine ⟨fun f hk => (by rw [hr.1] at hk; cases hk), fun hs => ?_⟩
      have h0 := thread_next_none_sub (hnone hs)
      have hb := rebuild_extra hp hX hrow hx he hr
      simp only [subFrag, idleCode, Wg1.idle, Wg1.isucc, Wg1.afterNc, hr.1, hb] at h0
      cases h0
    | bar =>
      refine ⟨fun f hk => (by rw [hev] at hk; cases hk), fun hs => ?_⟩
      have h0 := thread_next_none_sub (hnone hs)
      simp [subFrag, idleCode, Wg1.idle, Wg1.isucc] at h0
    | ret =>
      exact ⟨fun f hk => (by rw [hev] at hk; cases hk), fun _ => hev⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
