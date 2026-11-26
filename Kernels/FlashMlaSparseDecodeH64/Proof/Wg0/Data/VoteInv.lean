-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Carry

@[expose] public section

/-! # The vote before the probability stores

At the sites of the probability stores (`ost`) the block in progress holds the event of the
warp's vote (pc 578): the chain reaches `ost` only from `vote` or from `ost`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64.Proof

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The sites of the probability stores. -/
def postVote (s : Site) : Bool := match s with | .ost _ => true | _ => false

theorem succOk_ost {c c' : Control.D} {k : Fin 4} (h : succOk c c' = true)
    (hs : c'.site = .ost k) : c.site = .vote ∨ ∃ k', c.site = .ost k' := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  case sld a k' => fin_cases k' <;> simp at h
  case pst k' => fin_cases k' <;> simp at h
  case pld k' => fin_cases k' <;> simp at h
  case rstw k' => fin_cases k' <;> simp at h
  case ost2 c' k' => fin_cases k' <;> simp at h

/-- Past the vote the block in progress has its event. -/
def VoteInv (l : List Event) (d : D) : Prop :=
  d.ok = true → postVote d.c.site = true → ∃ e ∈ (w0Fin l).2, e.pc = 578

theorem voteInv_step {l : List Event} {d : D} {c' : Control.D} {e : Event}
    (hI : VoteInv l d) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    VoteInv (l ++ [e]) (dataNext L d c' e) := by
  intro hok hpost
  by_cases hs : d.c.site = .arrS
  · exfalso
    simp only [dataNext, hs] at hok hpost
    simp only [Control.succ, hs] at hc
    split at hc <;> cases hc <;> simp [postVote] at hpost
  rw [dataNext_eq hs] at hok hpost
  simp only at hok hpost
  obtain ⟨k, hk⟩ : ∃ k, c'.site = .ost k := by
    cases h : c'.site <;> simp [postVote, h] at hpost
    exact ⟨_, rfl⟩
  have hsucc : succOk d.c c' = true := (Bool.and_eq_true_iff.mp hok).2
  have hn1122 : ¬ e.pc = w0ArrSPc := fun h => hs (site_pc_1122 (hpc ▸ h))
  have hn200 : ¬ e.pc = w0ArrLPc := fun h => by
    have h1 := site_pc_200 (hpc ▸ h)
    rcases succOk_ost hsucc hk with h2 | ⟨k', h2⟩ <;> rw [h1] at h2 <;> cases h2
  rw [w0Fin_snoc]
  simp only [hn1122, hn200, ite_false]
  rcases succOk_ost hsucc hk with hv | ⟨k', hk'⟩
  · refine ⟨e, by simp, ?_⟩
    rw [hpc, hv]; rfl
  · have hok' : d.ok = true := by
      rcases Bool.or_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1 with h | h
      · rw [hk'] at h; simp [isStart] at h
      · exact h
    obtain ⟨f, hf, hf578⟩ := hI hok' (by rw [hk']; rfl)
    exact ⟨f, by simp [hf], hf578⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
