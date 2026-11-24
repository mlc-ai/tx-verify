-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WyNext
public import Kernels.InklingRelDecode.Proof.Progress.WuAll

@[expose] public section

/-!
# The polled object has a final state

The second clause of `Sched.PollBlocked` asks for the state of the polled object after its whole
history (`stateBefore (X.objects m) (X.objects m).length`). By `Interface.pollAt_final_of` it has
one once the thread has a barrier-1 event followed by another event. A thread at a poll has made at
least two barrier-1 events: its time is above `c1` (every poll site is in the loop's bands or in the
epilogue, `pollAt_time`), and the time of a state is at most `capB` of its barrier-1 count
(`Wu.tbl_at`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wy
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **A state at a poll is timed after the second generation of barrier 1.** -/
theorem pollAt_time {s : TSt} {m : Loc} {par : Nat} (h : PollAt L g s m par) :
    Wt.c1 < Wt.time g s := by
  cases s with
  | w s =>
    cases s with
    | loader d P =>
      obtain ⟨hs, -, -⟩ := h
      have := Wt.loaderT_band d (by rw [hs]; rfl)
      show Wt.c1 < Wt.loaderT d
      unfold Wt.slot Wt.loop0 Wt.c1 at *
      omega
    | mma d P =>
      have hq : Mma.QkSite d.site ∨ Mma.PvSite d.site := by
        rcases h with ⟨hs, -, -⟩ | ⟨hs, -, -⟩ <;> rw [hs]
        · exact .inl trivial
        · exact .inr trivial
      have := Wt.mmaT_band d hq
      show Wt.c1 < Wt.mmaT d
      unfold Wt.slot Wt.loop0 Wt.c1 Wt.bandM at *
      omega
    | _ => exact h.elim
  | d s =>
    cases s with
    | sm d =>
      have hl : Sm.LateSite d.site := by
        rcases h with ⟨hs, -, -⟩ | ⟨hs, -, -⟩ <;> rw [hs] <;> trivial
      have := Wt.smT_band d hl
      show Wt.c1 < Wt.smT d
      unfold Wt.slot Wt.loop0 Wt.c1 Wt.bandS at *
      omega
    | epi d =>
      show Wt.c1 < Wt.epiT d
      unfold Wt.epiT Wt.epi0 Wt.c1 Wt.loop0 Wt.span
      omega
    | _ => exact h.elim

/-- **A thread at a poll has made at least two barrier-1 events.** -/
theorem pollAt_b1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {s : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some s)) (hinv : (threadCode L g Q).inv s)
    {m : Loc} {par : Nat} (h : PollAt L g s m par) : 2 ≤ b1N X g (X.tr g).length := by
  obtain ⟨-, -, -, h1, -⟩ := Wu.tbl_at hpre hX hS hR le_rfl hσ hinv
  have ht := pollAt_time h
  by_contra hlt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show b1N X g (X.tr g).length ≤ 1 by omega) with
    h0 | h0 <;> rw [h0] at h1 <;> simp only [Wu.capB] at h1 <;>
    (try simp only [Wt.c0, Wt.c1] at h1 ht) <;> omega

/-- The count of a prefix one shorter is at least one below. -/
theorem countP_take_pred {α : Type} (p : α → Bool) (l : List α) :
    l.countP p ≤ (l.take (l.length - 1)).countP p + 1 := by
  conv_lhs => rw [← List.take_append_drop (l.length - 1) l]
  rw [List.countP_append]
  have : (l.drop (l.length - 1)).countP p ≤ 1 := by
    refine le_trans (List.countP_le_length) ?_
    simp only [List.length_drop]
    omega
  omega

/-- **The polled object has a final state.** -/
theorem pollAt_final (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) (hg : g < L.threads)
    {s : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some s)) (hinv : (threadCode L g Q).inv s)
    {m : Loc} {par : Nat} (h : PollAt L g s m par) :
    ∃ before, MBarrier.stateBefore (X.objects m) (X.objects m).length = some before := by
  have h2 := pollAt_b1 hpre hX hS hR hσ hinv h
  have hc := countP_take_pred (Execution.isBarId 1) (X.tr g)
  simp only [b1N, List.take_length] at h2
  have hpos : 0 < (X.tr g).length := by
    rcases Nat.eq_zero_or_pos (X.tr g).length with h0 | h0
    · rw [List.length_eq_zero_iff.mp h0] at h2
      simp at h2
    · exact h0
  exact pollAt_final_of hpre hX hg (j := (X.tr g).length - 1)
    (by simp only [b1N]; omega) (by omega) h

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wy
