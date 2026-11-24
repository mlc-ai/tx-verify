-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundMachine
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

public section

/-! # Trace order of issued asynchronous Tensor Core operations -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcDrainTrace

open PTX PTX.Flow _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- Every asynchronous Tensor Core operation is a query copy, QK MMA or PV MMA. -/
theorem async_site (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) {i : Nat} (hi : X.TcAsync (g, i)) :
    ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧
      ((∃ k, d.site = .qCopy k) ∨ (∃ k, d.site = .qkMma k) ∨ ∃ k, d.site = .pvMma k) := by
  obtain ⟨e, he, hk⟩ : ∃ e, X.get (g, i) = some e ∧
      ((∃ dst sp acc mask, e.kind = .tc (.mma dst sp acc mask)) ∨
        (∃ sp, e.kind = .tc (.cp sp)) ∨ ∃ sp, e.kind = .tc (.shift sp)) := by
    rcases hi with ⟨dst, sp, acc, mask, _, he⟩ | ⟨sp, _, he⟩ | ⟨sp, _, he⟩
    · exact ⟨_, he, .inl ⟨dst, sp, acc, mask, rfl⟩⟩
    · exact ⟨_, he, .inr (.inl ⟨sp, rfl⟩)⟩
    · exact ⟨_, he, .inr (.inr ⟨sp, rfl⟩)⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by
    rcases hk with ⟨_, _, _, _, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩ <;> simp [hk])
  rcases Wg0ScoreSources.writer_fields hpre hg hf (hk.imp id (Or.imp id Or.inr)) with
    ⟨s, j, _, _, hSt⟩ | ⟨s, j, rfl, hSite, _⟩ | ⟨s, j, rfl, hSite, _⟩ | ⟨s, j, rfl, hSite, _⟩
  · rcases hk with ⟨_, _, _, _, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hSt] at hk <;> cases hk
  · exact ⟨s, hd, .inl ⟨j, hSite⟩⟩
  · exact ⟨s, hd, .inr (.inl ⟨j, hSite⟩)⟩
  · exact ⟨s, hd, .inr (.inr ⟨j, hSite⟩)⟩

private theorem rank_le_of_le (hg : g < L.threads)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) {j i : Nat} {d f : Machine.ThreadD}
    (hj : Frame.stateAt (Machine.code P L) X g j = some (some d))
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some f)) (hji : j ≤ i)
    (hLen : i ≤ (X.tr g).length) : rank P L g f ≤ rank P L g d := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hji
  clear hji
  induction n generalizing f with
  | zero =>
    rw [Nat.add_zero, hj] at hi
    obtain rfl := Option.some.inj (Option.some.inj hi)
    rfl
  | succ n ih =>
    have hlt : j + n < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j + n) = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨q, r, hq, hr, hNext⟩ := FollowedPrefix.step_at hi (by omega) he
    have heq : r = f := by
      rw [Nat.add_succ, hr] at hi
      exact Option.some.inj (Option.some.inj hi)
    subst r
    obtain ⟨_, hf⟩ := (Frame.trace hs hX hg).fired_at he hq
    have hStep := Bound.rank_step hpre (Exists.choose_spec hf).1.2 hf hNext
    have hPrev := ih hq hlt.le
    omega

/-- All query copies of the elected lane precede its actual PV commits. -/
theorem copy_before_pv_commit (hs : ∀ g < L.threads, (Machine.code P L g).Sound) {i c : Nat}
    {q p : Wg1Mma.D} {e : Event} {k : Fin 16} (he : X.get (g, i) = some e)
    (hq : Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)))
    (hp : Frame.stateAt (Machine.code P L) X g c = some (some (.mma p))) (hCopy : q.site = .qCopy k)
    (hCommit : p.site = .pvCommit) : i < c := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.fired_site hs hX he hq
  have hInv : Wg1Mma.Inv P L g q := hi
  have hZero := hInv.prefix_i (show Wg1Mma.PrefixSite q.site by rw [hCopy]; trivial)
  by_contra! hNo
  have hb := rank_le_of_le hpre hX hg hs hp hq hNo (PTX.len_of_get he).le
  have hk := k.isLt
  simp only [rank, mmaRank, hCopy, hCommit, hZero, Nat.sub_zero, mmaOrdinal] at hb
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcDrainTrace
