-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Machine

@[expose] public section

/-! # The MMA warp's election in its ledger

After the election every count of the reference invariant holds one election (`elect_one`), and
the only site whose event is an election is the election site, at pc 1853 with the full mask
(`ev_elect`; a hand-back fires no event of its own). A step from a site after the election
stays after it and is no hand-back (`succ_post`). For the proof that the role's lane won its
election (`Common/MmaWon.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

/-- **After the election the ledger holds one election.** -/
theorem elect_one {d : D} {n : Cnt → Nat} (hc : RefCore L g d n) (hs : d.site ≠ .elect) :
    n .elect = 1 := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  unfold RefCore at hc
  cases site <;> simp only [Site.inLoop, Bool.false_eq_true, ↓reduceIte] at hc
  case elect => exact absurd rfl hs
  case exit =>
    rcases hc with hc | hc <;> rw [hc .elect (by simp)] <;> simp [cntAt, proCnt, loopCnt]
  case qCopy k =>
    rw [hc .elect (by simp)]
    simp only [cntAt, proCnt, loopCnt, Site.pro, ind]
    have h1 : 1 ≤ 12 + k.val := by omega
    simp [h1]
  case outBar => rw [hc .elect (by simp)]; simp [cntAt, proCnt, loopCnt]
  all_goals first
    | (rw [hc.2 .elect (by simp)]; simp [cntAt, proCnt, loopCnt])
    | (rw [hc .elect (by simp)]; simp [cntAt, proCnt, loopCnt, Site.pro, ind])


/-- **An election event is the election site's**, at pc 1853 with the full mask. -/
theorem ev_elect {d : D} {pc mk inst ld : Nat} (hl : ∀ s, d.site ≠ .leave s)
    (hev : Ev L g d ⟨pc, .elect mk inst ld⟩) :
    d.site = .elect ∧ pc = 1853 ∧ mk = 2 ^ 32 - 1 := by
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hpc hk
  cases site <;> simp [EvK, PollEv, CommitEv, MmaEv] at hk
  case elect => exact ⟨rfl, hpc, by omega⟩
  case leave s => exact absurd rfl (hl s)

/-- A site after the election that is no hand-back. -/
def Post (s : Site) : Prop := s ≠ .elect ∧ ∀ i, s ≠ .leave i

/-- **A step from a site after the election stays after it.** -/
theorem succ_post {P : Params} {d d' : D} {f : Event} (hs : Post d.site)
    (h : succ P L g d f = some (some d')) : Post d'.site := by
  obtain ⟨hs, hl⟩ := hs
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [succ, ncWord, poll] at h
  case elect => exact absurd rfl hs
  case leave i => exact absurd rfl (hl i)
  all_goals ((repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h)
  all_goals simp [Post, afterTopk, lensD, loopEntry, loopEnd]
  all_goals (split_ifs <;> simp)

/-- **The elected lane's first site is after the election.** -/
theorem lead_post {P : Params} (d : D) : Post (leadNext P L g d).site := by
  unfold leadNext afterTopk lensD
  split_ifs <;> simp [Post]

/-- **A step keeps the two length words** except at the election and the two length loads. -/
theorem words_step {P : Params} {d a : D} {f : Event} (he : d.site ≠ .elect)
    (ht : d.site ≠ .loadTopk) (hx : d.site ≠ .loadExtra)
    (h : succ P L g d f = some (some a)) :
    a.l0 = d.l0 ∧ a.l1 = d.l1 ∧ a.site ≠ .loadTopk ∧ a.site ≠ .loadExtra := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [succ, poll] at h
  case elect => exact absurd rfl he
  case loadTopk => exact absurd rfl ht
  case loadExtra => exact absurd rfl hx
  all_goals ((repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h)
  all_goals (try unfold loopEntry)
  all_goals (try unfold loopEnd)
  all_goals (repeat' split) <;> simp

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
