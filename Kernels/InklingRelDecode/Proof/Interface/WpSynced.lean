-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WpPoll
public import Kernels.InklingRelDecode.Proof.Interface.WpSoft

@[expose] public section

/-!
# `PollSynced` from the polls' sites and the warp collectives

ERR-NONUNIFORM-GUARD asks, of two lanes of a warp polling at one position before a poll branch,
an order between them unless they poll one object at a branch an assumption selects
(`PollSynced`). Every poll of the kernel is at one of six sites (`poll_at`), whose positions are
distinct (`pollIdx`), so the two polls are at one site; every poll branch after them is selected
by `pollAgree` (`pollPc_sel`). So only polls of different objects need an order:

* `o_done` (the softmax region's `waitO`) and `o_final` (the epilogue's `wait`) are polled at one
  object per CTA (`PollAt`), and the lanes of a warp are of one CTA: their objects are equal;
* at the ring polls the object is a function of the CTA and the iteration (`PollAt`), so polls of
  different objects are in different iterations. The poll of the lane in the earlier iteration is
  ordered before the other's: at the softmax region's `s_ready` poll by `soft_met`; at the loader's
  `kv_empty` poll and the MMA warp's `kv_ready` and `p_ready` polls by `WorkerMet`, the same
  statement for the worker sites (`pollSynced_of`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two worker states at one ring poll site of the loader or the MMA warp, the first in an earlier
iteration. -/
def WorkerAhead : TSt → TSt → Prop
  | .w (.loader d _), .w (.loader d' _) => d.site = .wait ∧ d'.site = .wait ∧ d.i < d'.i
  | .w (.mma d _), .w (.mma d' _) =>
    ((d.site = .kvWait ∧ d'.site = .kvWait) ∨ (d.site = .pWait ∧ d'.site = .pWait)) ∧ d.i < d'.i
  | _, _ => False

/-- **The worker ring polls are met**: of two lanes of a warp polling at the loader's `wait`, or
both at the MMA warp's `kvWait` or both at its `pWait`, the poll of the lane in the earlier
iteration is ordered before the other's. -/
def WorkerMet (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k k' : Nat} {e : Event} {s s' : TSt}, SameWarp L g h → X.get (g, k) = some e →
    (∃ pc m p ok acq sc, e = ⟨pc, .wait m p ok acq sc⟩) → St Q L X g k = some (some s) →
    St Q L X h k' = some (some s') → k' < (X.tr h).length → WorkerAhead s s' →
    PollBefore L kernel X (g, k) (h, k')

/-- The six kinds of poll states, with the index of their position. -/
theorem poll_cases {g : Nat} {s : TSt} {m : Loc} {p : Nat} (h : PollAt L g s m p) :
    (∃ d, s = .d (.sm d) ∧ d.site = .waitS ∧ m = EvW.sReady L (g / L.block) (d.i % 2) ∧
      pollIdx (pollPc s) = 0) ∨
    (∃ d, s = .d (.sm d) ∧ m = EvW.oDone L (g / L.block) ∧ pollIdx (pollPc s) = 1) ∨
    (∃ d P, s = .w (.loader d P) ∧ d.site = .wait ∧ m = EvW.kvEmpty L (g / L.block) (d.i % 3) ∧
      pollIdx (pollPc s) = 2) ∨
    (∃ d P, s = .w (.mma d P) ∧ d.site = .kvWait ∧ m = EvW.kvReady L (g / L.block) (d.i % 3) ∧
      pollIdx (pollPc s) = 3) ∨
    (∃ d P, s = .w (.mma d P) ∧ d.site = .pWait ∧
      m = EvW.pReady L (g / L.block) ((d.i - 1) % 2) ∧ pollIdx (pollPc s) = 4) ∨
    (∃ d, s = .d (.epi d) ∧ m = EvW.oFinal L (g / L.block) ∧ pollIdx (pollPc s) = 5) := by
  cases s with
  | w s =>
    cases s with
    | loader d P =>
      obtain ⟨hs, rfl, -⟩ := h
      exact .inr (.inr (.inl ⟨d, P, rfl, hs, rfl, by simp [pollPc, hs, idx_loader]⟩))
    | mma d P =>
      rcases h with ⟨hs, rfl, -⟩ | ⟨hs, rfl, -⟩
      · exact .inr (.inr (.inr (.inl ⟨d, P, rfl, hs, rfl, by simp [pollPc, hs, idx_kvWait]⟩)))
      · exact .inr (.inr (.inr (.inr (.inl ⟨d, P, rfl, hs, rfl,
          by simp [pollPc, hs, idx_pWait]⟩))))
    | _ => exact h.elim
  | d s =>
    cases s with
    | sm d =>
      rcases h with ⟨hs, rfl, -⟩ | ⟨hs, rfl, -⟩
      · exact .inl ⟨d, rfl, hs, rfl, by simp [pollPc, hs, idx_waitS]⟩
      · exact .inr (.inl ⟨d, rfl, rfl, by simp [pollPc, hs, idx_waitO]⟩)
    | epi d =>
      obtain ⟨hs, rfl, -⟩ := h
      exact .inr (.inr (.inr (.inr (.inr ⟨d, rfl, rfl, by simp [pollPc, hs, idx_epi]⟩))))
    | _ => exact h.elim

/-- **Polls of one position by two lanes of a warp at different objects are ordered**, given the
worker ring polls (`WorkerMet`). -/
theorem pollSynced_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hA : LaneAgree Q L X) (hW : WorkerMet Q L X) :
    PollSynced L kernel asms X := by
  intro g h k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hpb hd
  obtain ⟨s, hσ, hpa, hpc⟩ := poll_at hpre hX hf he
  obtain ⟨s', hσ', hpa', hpc'⟩ := poll_at hpre hX hf he'
  have hsel := pollPc_sel hpa
  rw [← hpc] at hsel
  have hne : m ≠ m' := by
    rcases hd with hd | hd
    · exact hd
    · rw [hsel] at hd
      cases hd
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hk' : k' < (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1
  have hc : g / L.block = h / L.block := hw.1.2.2
  have hix : pollIdx (pollPc s) = pollIdx (pollPc s') := by rw [← hpc, ← hpc']
  rcases poll_cases hpa with ⟨d, rfl, hs, rfl, hi⟩ | ⟨d, rfl, rfl, hi⟩ |
      ⟨d, P, rfl, hs, rfl, hi⟩ | ⟨d, P, rfl, hs, rfl, hi⟩ | ⟨d, P, rfl, hs, rfl, hi⟩ |
      ⟨d, rfl, rfl, hi⟩ <;>
    rcases poll_cases hpa' with ⟨d', rfl, hs', rfl, hi'⟩ | ⟨d', rfl, rfl, hi'⟩ |
      ⟨d', P', rfl, hs', rfl, hi'⟩ | ⟨d', P', rfl, hs', rfl, hi'⟩ | ⟨d', P', rfl, hs', rfl, hi'⟩ |
      ⟨d', rfl, rfl, hi'⟩ <;>
    try (exfalso; omega)
  · -- `s_ready`
    rcases Nat.lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (soft_met hpre hX hf hA hw he rfl hσ hs hσ' hs' hk' hlt)
    · exact absurd (by rw [hc, heq]) hne
    · exact .inr (soft_met hpre hX hf hA (sameWarp_symm hw) he' rfl hσ' hs' hσ hs hk hgt)
  · -- `o_done`
    exact absurd (by rw [hc]) hne
  · -- `kv_empty`
    rcases Nat.lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (hW hw he ⟨_, _, _, _, _, _, rfl⟩ hσ hσ' hk' ⟨hs, hs', hlt⟩)
    · exact absurd (by rw [hc, heq]) hne
    · exact .inr (hW (sameWarp_symm hw) he' ⟨_, _, _, _, _, _, rfl⟩ hσ' hσ hk ⟨hs', hs, hgt⟩)
  · -- `kv_ready`
    rcases Nat.lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (hW hw he ⟨_, _, _, _, _, _, rfl⟩ hσ hσ' hk' ⟨.inl ⟨hs, hs'⟩, hlt⟩)
    · exact absurd (by rw [hc, heq]) hne
    · exact .inr (hW (sameWarp_symm hw) he' ⟨_, _, _, _, _, _, rfl⟩ hσ' hσ hk ⟨.inl ⟨hs', hs⟩, hgt⟩)
  · -- `p_ready`
    rcases Nat.lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (hW hw he ⟨_, _, _, _, _, _, rfl⟩ hσ hσ' hk' ⟨.inr ⟨hs, hs'⟩, hlt⟩)
    · exact absurd (by rw [hc, heq]) hne
    · exact .inr (hW (sameWarp_symm hw) he' ⟨_, _, _, _, _, _, rfl⟩ hσ' hσ hk ⟨.inr ⟨hs', hs⟩, hgt⟩)
  · -- `o_final`
    exact absurd (by rw [hc]) hne

end
end PTX.Kernels.InklingRelDecode.Proof.Wp
