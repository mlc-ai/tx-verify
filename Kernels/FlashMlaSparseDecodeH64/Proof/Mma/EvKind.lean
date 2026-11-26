-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Objs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Time

@[expose] public section

/-! # The MMA warp's sites by their event's kind

A tensor copy is fired at a Q load, on `bar_q_tma` (`ev_tensor`); an arrival at the arrival on
`bar_q_tma` (`ev_arrive`); a commit at one of the three commit sites, on its object
(`ev_commit`); a poll at one of the four wait sites, on its object (`ev_wait`). With the
reference invariant at a prologue site, the counts are those of its place (`pro_cnt`). For the
role's trace-level counts (`Mma/Export/Count.lean`, `Mma/Export/Time.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat} {d : D} {pc : Nat}

theorem ev_tensor (hl : ∀ s, d.site ≠ .leave s) {a : Nat} {s : TensorCopy.Spec}
    (hev : Ev L g d ⟨pc, .tensorIssue a s⟩) :
    ∃ i, d.site = .qLoad i ∧ s.mbar = smLoc L g (qTmaW L) 0 := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [EvK, PollEv, CommitEv, MmaEv] at hk
  case qLoad i => exact ⟨i, rfl, hk.1⟩
  case leave i => exact absurd rfl (hl i)

theorem ev_arrive (hl : ∀ s, d.site ≠ .leave s) {l : Loc} {tx c : Nat} {r : Bool}
    {sc : MbarScope} (hev : Ev L g d ⟨pc, .arrive l tx c r sc⟩) :
    d.site = .qArrive ∧ l = smLoc L g (qTmaW L) 0 := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [EvK, PollEv, CommitEv, MmaEv] at hk
  case qArrive => exact ⟨rfl, hk.1⟩
  case leave i => exact absurd rfl (hl i)

theorem ev_commit (hl : ∀ s, d.site ≠ .leave s) {s : TcCommit.Spec}
    (hev : Ev L g d ⟨pc, .tc (.commit s)⟩) :
    (d.site = .qCopyCommit ∧ s.mbar = smLoc L g (qUtccpW L) 0) ∨
      (d.site = .qkCommit ∧ s.mbar = smLoc L g (qkW L d.pha) 0) ∨
      (d.site = .pvCommit ∧ s.mbar = smLoc L g (svW L d.pha) 0) := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [EvK, PollEv, CommitEv, MmaEv] at hk
  case qCopyCommit => exact .inl ⟨rfl, hk.1⟩
  case qkCommit => exact .inr (.inl ⟨rfl, hk.1⟩)
  case pvCommit => exact .inr (.inr ⟨rfl, hk.1⟩)
  case leave i => exact absurd rfl (hl i)

theorem ev_wait (hl : ∀ s, d.site ≠ .leave s) {l : Loc} {q : Nat} {ok a : Bool}
    {sc : MbarScope} (hev : Ev L g d ⟨pc, .wait l q ok a sc⟩) :
    (d.site = .qWait ∧ l = smLoc L g (qTmaW L) 0) ∨
      (d.site = .qCopyWait ∧ l = smLoc L g (qUtccpW L) 0) ∨
      (d.site = .kvWait ∧ l = smLoc L g (readyW L d.pha) 0) ∨
      (d.site = .soWait ∧ l = smLoc L g (soW L d.pha) 0) := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [EvK, PollEv, CommitEv, MmaEv] at hk
  case qWait => exact .inl ⟨rfl, hk.1⟩
  case qCopyWait => exact .inr (.inl ⟨rfl, hk.1⟩)
  case kvWait => exact .inr (.inr (.inl ⟨rfl, hk.1⟩))
  case soWait => exact .inr (.inr (.inr ⟨rfl, hk.1⟩))
  case leave i => exact absurd rfl (hl i)

/-- **The counts at a prologue site** are those of its place. -/
theorem pro_cnt {n : Cnt → Nat} (hc : RefCore L g d n) (hs : ProSite d.site) {c : Cnt}
    (hu : c ≠ .ub) : n c = cntAt (objs L g) d.site.pro 0 0 false c :=
  (core_pro hs).mp hc c hu

/-- **From the arrival on `bar_q_tma` on, the eight Q loads are made.** -/
theorem tma_eight {n : Cnt → Nat} (hc : RefCore L g d n) (hl : ∀ s, d.site ≠ .leave s)
    (hpc : 1929 ≤ d.site.pc) (hx : d.site.pc < 3611) : n .tma = 8 := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  unfold RefCore at hc
  cases site <;> simp only [Site.pc] at hpc hx <;> simp only [Site.inLoop, Bool.false_eq_true,
    ↓reduceIte] at hc
  case leave i => exact absurd rfl (hl i)
  all_goals first
    | omega
    | (rw [hc.2 .tma (by simp)]; simp [cntAt, proCnt, loopCnt])
    | (rw [hc .tma (by simp)]; simp [cntAt, proCnt, loopCnt, Site.pro]; done)
    | (rw [hc .tma (by simp)]; simp [cntAt, proCnt, loopCnt, Site.pro]; omega)

/-- **The exit's counts**: before the length loads, or after the CTA barrier. -/
theorem exit_cnt {n : Cnt → Nat} (hc : RefCore L g d n) (hs : d.site = .exit) :
    (∀ c, c ≠ .ub → n c = cntAt (objs L g) 1 0 0 false c) ∨
      ∀ c, c ≠ .ub → n c = cntAt (objs L g) 31 (rounds d.l0 d.l1) 0 true c := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  subst hs
  exact hc

/-- **Before the commit to `bar_q_utccp`**, after a Q load, the place is at most the commit's. -/
theorem place_pre_commit {n : Cnt → Nat} (hc : RefCore L g d n) (hl : ∀ s, d.site ≠ .leave s)
    (h8 : 1 ≤ n .tma) (h0 : n (.commit (objs L g).qUt) = 0) : place d ≤ 31 := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  unfold RefCore at hc
  cases site <;> simp only [Site.inLoop, Bool.false_eq_true, ↓reduceIte] at hc
  case leave i => exact absurd rfl (hl i)
  case exit =>
    rcases hc with hc | hc
    · rw [hc .tma (by simp)] at h8; simp [cntAt, proCnt, loopCnt] at h8
    · rw [hc _ (by simp)] at h0; simp [cntAt, proCnt, loopCnt] at h0
  all_goals first
    | (rw [hc.2 _ (by simp)] at h0; simp [cntAt, proCnt, loopCnt, Site.idx] at h0)
    | (rw [hc _ (by simp)] at h0; simp [cntAt, proCnt, loopCnt, Site.pro] at h0; done)
    | (simp [place, Site.ord, Site.inLoop]; done)
    | (rename_i k; have := k.isLt; simp [place, Site.ord, Site.inLoop]; omega)

/-- Place 31 is the commit to `bar_q_utccp`. -/
theorem place_31 (h : place d = 31) : d.site = .qCopyCommit := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [place, Site.ord, Site.inLoop, Site.off, endPlace, endSlot, mmaBlk0, loopBase,
    mmaOff, mmaOrg, stride, blockCap] at h ⊢ <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
