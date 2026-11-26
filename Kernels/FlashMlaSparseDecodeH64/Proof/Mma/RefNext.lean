-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefStep

@[expose] public section

/-! # The MMA warp's reference invariant is kept by every step

`ref_step`: from a state with `Ref`, an event of the state's shape that the machine follows leads
to a state with `Ref` for the bumped counts (an undefined-behaviour event bumps the class `ub`,
after which `Ref` asks nothing). `siteOk_next`: every state the machine reaches has its launch
facts (`SiteOk`): a length load's pointer is set, and the only hand-back state is the idle code's
first event (`leave (idleFirst P L g)`). -/

/-! # The MMA warp's reference invariant across a step of the block loop

One declaration per loop site: the objects of the events are the phase's (`LoopOk`: the phase
word is `r % 2`), the counts advance by `loop_*`; the block's end (`next_pvCommit`) moves to
block `r + 1` with its words (`end_words`) or to the CTA barrier, whose step reaches the exit
(`next_outBar`). -/

/-! # The MMA warp's reference invariant across a prologue step

`StepRef P L g s`: from a state at site `s` with `RefCore`, an event of the site's kind that is not
undefined behaviour, at a pc of the role, leads to a state with `RefCore` for the bumped counts.
One declaration per prologue site; the step from the last fence enters the block loop
(`next_qCopyFence`, by `rounds_pos`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The step obligation of the reference invariant at site `s`. -/
def StepRef (P : Params) (L : Launch) (g : Nat) (s : Site) : Prop :=
  ∀ (l0 l1 neg cnt pha par : BitVec 64) (n : Cnt → Nat) (e : Event) (d' : D),
    inRole e = true → (∀ f, e.kind ≠ .ub f) → RefCore L g ⟨s, l0, l1, neg, cnt, pha, par⟩ n →
    EvK L g ⟨s, l0, l1, neg, cnt, pha, par⟩ e →
    succ P L g ⟨s, l0, l1, neg, cnt, pha, par⟩ e = some (some d') →
    RefCore L g d' (Code.bump cls n e)

/-- A prologue site. -/
macro "pro_site" : term => `((by refine ⟨rfl, ?_, ?_⟩ <;> simp))

theorem next_elect : StepRef P L g .elect := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨inst, ld, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = some .elect := by simp [kindOf, hk]
  have hB := pro_bump (B := cntAt (objs L g) 1 0 0 false) hpc hK pro_site hJ pro_elect
  simp only [succ, hk, Option.some.injEq] at hn
  subst hn
  refine core_one ?_ hB
  split_ifs
  · unfold leadNext afterTopk lensD
    split_ifs <;> first | exact .inl rfl | exact .inr ⟨pro_site, rfl⟩
  · exact .inr ⟨pro_site, rfl⟩

theorem next_loadTopk : StepRef P L g .loadTopk := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨a, bs, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = none := by simp [kindOf, hk]
  have hB := pro_bump (B := cntAt (objs L g) 1 0 0 false) hpc hK pro_site hJ
    (by simp [plus_none, Site.pro])
  obtain ⟨x, rfl⟩ := ncWord_some hn
  refine core_one ?_ hB
  unfold afterTopk lensD
  split_ifs <;> exact .inr ⟨pro_site, rfl⟩

theorem next_loadExtra : StepRef P L g .loadExtra := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨a, bs, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = none := by simp [kindOf, hk]
  have hB := pro_bump (B := cntAt (objs L g) 1 0 0 false) hpc hK pro_site hJ
    (by simp [plus_none, Site.pro])
  obtain ⟨x, rfl⟩ := ncWord_some hn
  refine core_one ?_ hB
  unfold lensD
  split_ifs <;> exact .inr ⟨pro_site, rfl⟩

theorem next_qLoad (k : Fin 8) : StepRef P L g (.qLoad k) := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨a, s, hk, -⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = some .tma := by simp [kindOf, hk]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  have := k.isLt
  by_cases h7 : k.val = 7
  · simp only [h7, ↓reduceIte]
    refine pro_next hpc hK pro_site pro_site hJ ?_
    simp only [Site.pro, h7]
    exact pro_tma 8 (by omega) (by omega)
  · simp only [h7, ↓reduceIte]
    refine pro_next hpc hK pro_site pro_site hJ ?_
    simp only [Site.pro, fin_succ k h7]
    exact pro_tma (1 + k.val) (by omega) (by omega)

theorem next_qArrive : StepRef P L g .qArrive := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  have hk : e.kind = .arrive (smLoc L g (qTmaW L) 0) 65536 1 true .cta := hev
  have hK : kindOf e = some (.arrive (objs L g).qTma) := by simp [kindOf, hk, qTma_eq]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  exact pro_next hpc hK pro_site pro_site hJ pro_arrive

theorem next_qWait : StepRef P L g .qWait := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨ok, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  rw [← qTma_eq] at hk
  exact pro_poll hpc hk pro_site pro_site hJ hn pro_acqQ

theorem next_qFence : StepRef P L g .qFence := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  have hk : e.kind = .tc .fenceAfter := hev
  have hK : kindOf e = none := by simp [kindOf, hk]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  exact pro_next hpc hK pro_site pro_site hJ (pro_none 11 (.inl rfl))

theorem next_qCopy (k : Fin 16) : StepRef P L g (.qCopy k) := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨s, hk, -⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = some .cp := by simp [kindOf, hk]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  have := k.isLt
  by_cases h15 : k.val = 15
  · simp only [h15, ↓reduceIte]
    refine pro_next hpc hK pro_site pro_site hJ ?_
    simp only [Site.pro, h15]
    exact pro_cp 27 (by omega) (by omega)
  · simp only [h15, ↓reduceIte]
    refine pro_next hpc hK pro_site pro_site hJ ?_
    simp only [Site.pro, fin_succ k h15]
    exact pro_cp (12 + k.val) (by omega) (by omega)

theorem next_qCopyCommit : StepRef P L g .qCopyCommit := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨s, hk, hm, -⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = some (.commit (objs L g).qUt) := by simp [kindOf, hk, hm, qUt_eq]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  exact pro_next hpc hK pro_site pro_site hJ pro_commit

theorem next_qCopyWait : StepRef P L g .qCopyWait := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨ok, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  rw [← qUt_eq] at hk
  exact pro_poll hpc hk pro_site pro_site hJ hn pro_acqU

/-- **The loop's entry**: block `0` with its words, or the barrier for a total below 64. -/
theorem next_qCopyFence : StepRef P L g .qCopyFence := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  have hk : e.kind = .tc .fenceAfter := hev
  have hK : kindOf e = none := by simp [kindOf, hk]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  have hB := pro_bump (B := cntAt (objs L g) 31 0 0 false) hpc hK pro_site hJ
    (pro_none 30 (.inr rfl))
  unfold loopEntry
  split_ifs with h
  · unfold RefCore
    simp only [rounds, h, ↓reduceIte]
    exact hB
  · have h' : scmpi .lt .s (r27 l0 l1) 64 = false := by simpa using h
    obtain ⟨h1, h2, hneg⟩ := rounds_pos h'
    have h0 : (i32 0).toNat = 0 := by decide
    refine (core_loop rfl).2 ⟨⟨h', h1, h2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [h0]; omega
    · simp only [h0]; decide
    · simp only [h0]; decide
    · simp only [h0]; decide
    · simpa only [h0, Nat.add_zero] using hneg
    · rw [h0]; exact hB

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The loop words of a loop state. -/
theorem loopOk_of {s : Site} {l0 l1 neg cnt pha par : BitVec 64} {n : Cnt → Nat}
    (hs : s.inLoop = true) (hJ : RefCore L g ⟨s, l0, l1, neg, cnt, pha, par⟩ n) :
    LoopOk ⟨s, l0, l1, neg, cnt, pha, par⟩ :=
  ((core_loop hs).1 hJ).1

/-- A step inside a block that changes only the site. -/
theorem loop_site {d : D} {s : Site} {n : Cnt → Nat} {e : Event} {X : Option Cnt}
    (hpc : inRole e = true) (hk : kindOf e = X) (hd : d.site.inLoop = true)
    (hs : s.inLoop = true) (hJ : RefCore L g d n)
    (hc : ∀ c, plus (cntAt (objs L g) 31 d.cnt.toNat d.site.idx false) X c =
      cntAt (objs L g) 31 d.cnt.toNat s.idx false c) :
    RefCore L g { d with site := s } (Code.bump cls n e) :=
  loop_next (d' := { d with site := s }) hpc hk hd hs id rfl hJ hc

theorem next_kvWait : StepRef P L g .kvWait := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨-, -, -, -, -, hpha, -, -⟩ := loopOk_of rfl hJ
  obtain ⟨ok, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  simp only at hpha
  rw [hpha, ← ready_eq] at hk
  exact loop_poll hpc hk rfl rfl hJ hn (loop_acqR _)

theorem next_soWait : StepRef P L g .soWait := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨-, -, -, -, -, hpha, -, -⟩ := loopOk_of rfl hJ
  obtain ⟨ok, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  simp only at hpha
  rw [hpha, ← so_eq] at hk
  exact loop_poll hpc hk rfl rfl hJ hn (loop_acqS _)

theorem next_kvFence : StepRef P L g .kvFence := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  have hk : e.kind = .tc .fenceAfter := hev
  have hK : kindOf e = none := by simp [kindOf, hk]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  exact loop_site hpc hK rfl rfl hJ (loop_none _ 1 (.inl rfl))

theorem next_soFence : StepRef P L g .soFence := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  have hk : e.kind = .tc .fenceAfter := hev
  have hK : kindOf e = none := by simp [kindOf, hk]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  exact loop_site hpc hK rfl rfl hJ (loop_none _ 20 (.inr rfl))

theorem next_qk (k : Fin 16) : StepRef P L g (.qk k) := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨s, hk, -⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = some .mma := by simp [kindOf, hk]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  have := k.isLt
  by_cases h15 : k.val = 15
  · simp only [h15, ↓reduceIte]
    refine loop_site hpc hK rfl rfl hJ ?_
    rw [show (Site.qk k).idx = 17 by simp only [Site.idx]; omega]
    exact loop_mma1 _ 17 (by omega) (by omega)
  · simp only [h15, ↓reduceIte]
    refine loop_site hpc hK rfl rfl hJ ?_
    rw [show (Site.qk k).idx = 2 + k.val from rfl,
      show (Site.qk (k + 1)).idx = 2 + k.val + 1 by simp only [Site.idx, fin_succ k h15]; omega]
    exact loop_mma1 _ (2 + k.val) (by omega) (by omega)

theorem next_pv (k : Fin 8) : StepRef P L g (.pv k) := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨s, hk, -⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = some .mma := by simp [kindOf, hk]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  have := k.isLt
  by_cases h7 : k.val = 7
  · simp only [h7, ↓reduceIte]
    refine loop_site hpc hK rfl rfl hJ ?_
    rw [show (Site.pv k).idx = 28 by simp only [Site.idx]; omega]
    exact loop_mma2 _ 28 (by omega) (by omega)
  · simp only [h7, ↓reduceIte]
    refine loop_site hpc hK rfl rfl hJ ?_
    rw [show (Site.pv k).idx = 21 + k.val from rfl,
      show (Site.pv (k + 1)).idx = 21 + k.val + 1 by simp only [Site.idx, fin_succ k h7]; omega]
    exact loop_mma2 _ (21 + k.val) (by omega) (by omega)

theorem next_qkCommit : StepRef P L g .qkCommit := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨-, -, -, -, -, hpha, -, -⟩ := loopOk_of rfl hJ
  obtain ⟨s, hk, hm, -⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  simp only at hpha
  rw [hpha, ← qk_eq] at hm
  have hK : kindOf e = some (.commit ((objs L g).qk (cnt.toNat % 2))) := by
    simp [kindOf, hk, hm]
  simp only [succ, Option.some.injEq] at hn
  subst hn
  exact loop_site hpc hK rfl rfl hJ (loop_commitK _)

/-- **The block's end**: block `r + 1` with its words, or the CTA barrier after the last block. -/
theorem next_pvCommit : StepRef P L g .pvCommit := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  obtain ⟨hlt, h1R, hR, hr, hcnt, hpha, hpar, hneg⟩ := loopOk_of rfl hJ
  simp only at hlt h1R hR hr hcnt hpha hpar hneg
  obtain ⟨s, hk, hm, -⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hm' := hm
  rw [hpha, ← sv_eq] at hm'
  have hK : kindOf e = some (.commit ((objs L g).sv (cnt.toNat % 2))) := by
    simp [kindOf, hk, hm']
  obtain ⟨-, hB⟩ := loop_bump (B := cntAt (objs L g) 31 (cnt.toNat + 1) 0 false) hpc hK rfl hJ
    (loop_end _)
  simp only [succ, Option.some.injEq] at hn
  subst hn
  generalize cnt.toNat = r at hlt hr hcnt hpha hpar hneg hB
  subst hcnt hpha hpar hneg
  obtain ⟨e1, e2, e3, e4, e5⟩ := end_words hr hR
  unfold loopEnd parNext
  rw [e4] at e5
  simp only [e1, e2, e3, e4, e5]
  split_ifs with hc
  · have hr1 : r + 1 < rounds l0 l1 := by simp at hc; omega
    have hw : (W (r + 1)).toNat = r + 1 := toNat_W (by omega)
    refine (core_loop rfl).2 ⟨⟨hlt, h1R, hR, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [hw]
    · exact hr1
    · exact hB
  · have hr1 : r + 1 = rounds l0 l1 := by simp at hc; omega
    unfold RefCore
    rw [← hr1]
    exact hB

theorem next_outBar : StepRef P L g .outBar := by
  intro l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn
  have hk : e.kind = .bar 12 none .sync := hev
  have hK : kindOf e = some (.bar 12) := by simp [kindOf, hk]
  have hJ' : ∀ c, c ≠ .ub → n c = cntAt (objs L g) 31 (rounds l0 l1) 0 false c := hJ
  simp only [succ, Option.some.injEq] at hn
  subst hn
  unfold RefCore
  exact .inr (core_bump hpc hJ' fun c _ => hK ▸ bar_step c)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- **`RefCore` is kept by every step** on an event of the state's kind that is not undefined
behaviour. -/
theorem core_step {d d' : D} {n : Cnt → Nat} {e : Event} (hpc : inRole e = true)
    (hu : ∀ f, e.kind ≠ .ub f) (hJ : RefCore L g d n) (hev : EvK L g d e)
    (hn : succ P L g d e = some (some d')) : RefCore L g d' (Code.bump cls n e) := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  have h : StepRef P L g s := by
    cases s with
    | elect => exact next_elect
    | loadTopk => exact next_loadTopk
    | loadExtra => exact next_loadExtra
    | qLoad k => exact next_qLoad k
    | qArrive => exact next_qArrive
    | qWait => exact next_qWait
    | qFence => exact next_qFence
    | qCopy k => exact next_qCopy k
    | qCopyCommit => exact next_qCopyCommit
    | qCopyWait => exact next_qCopyWait
    | qCopyFence => exact next_qCopyFence
    | kvWait => exact next_kvWait
    | kvFence => exact next_kvFence
    | qk k => exact next_qk k
    | qkCommit => exact next_qkCommit
    | soWait => exact next_soWait
    | soFence => exact next_soFence
    | pv k => exact next_pv k
    | pvCommit => exact next_pvCommit
    | outBar => exact next_outBar
    | trap | exit | leave _ => intro _ _ _ _ _ _ _ _ _ _ _ _ _ hn; simp [succ] at hn
  exact h l0 l1 neg cnt pha par n e d' hpc hu hJ hev hn

/-- **The reference invariant is kept by every step** the machine follows. -/
theorem ref_step {d d' : D} {n : Cnt → Nat} {e : Event} (hJ : Ref L g d n) (hev : Ev L g d e)
    (hn : succ P L g d e = some (some d')) : Ref L g d' (Code.bump cls n e) := by
  intro h0
  have hpc := inRole_of_next hev.1 hn
  have hn0 : n .ub = 0 := by
    simp only [Code.bump] at h0
    omega
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu
    simp [Code.bump, cls, hpc, kindOf, hf] at h0
  · exact core_step hpc (fun f h => hu ⟨f, h⟩) (hJ hn0) hev.2 hn

/-- The sites that `SiteOk` asks nothing of. -/
def Site.plain : Site → Bool
  | .loadTopk | .loadExtra | .leave _ => false
  | _ => true

theorem siteOk_plain {d : D} (h : d.site.plain = true) : SiteOk P L g d := by
  refine ⟨fun hs => ?_, fun hs => ?_, fun s hs => ?_⟩ <;> rw [hs] at h <;> cases h

/-- The election's successors. -/
theorem siteOk_elect {l0 l1 neg cnt pha par : BitVec 64} {d' : D} {e : Event}
    (hn : succ P L g ⟨.elect, l0, l1, neg, cnt, pha, par⟩ e = some (some d')) :
    SiteOk P L g d' := by
  simp only [succ] at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    split_ifs
    · simp only [leadNext, afterTopk, lensD]
      split_ifs with h1 h2 h3 h4
      · exact siteOk_plain rfl
      · exact siteOk_plain rfl
      · exact siteOk_plain rfl
      · exact ⟨nofun, fun _ => Bool.eq_false_iff.mpr h3, nofun⟩
      · exact ⟨fun _ => Bool.eq_false_iff.mpr h2, nofun, nofun⟩
    · exact ⟨nofun, nofun, fun s h => by cases h; rfl⟩
  · cases hn

/-- The length loads' successors. -/
theorem siteOk_nc {s : Site} (hs : s = .loadTopk ∨ s = .loadExtra)
    {l0 l1 neg cnt pha par : BitVec 64} {d' : D} {e : Event}
    (hn : succ P L g ⟨s, l0, l1, neg, cnt, pha, par⟩ e = some (some d')) : SiteOk P L g d' := by
  rcases hs with rfl | rfl <;> simp only [succ] at hn <;> obtain ⟨x, rfl⟩ := ncWord_some hn
  · simp only [afterTopk, lensD]
    split_ifs with h1 h2
    · exact siteOk_plain rfl
    · exact siteOk_plain rfl
    · exact ⟨nofun, fun _ => Bool.eq_false_iff.mpr h1, nofun⟩
  · simp only [lensD]
    split_ifs <;> exact siteOk_plain rfl

/-- A poll's successor is its site or the poll. -/
theorem plain_poll {d d' : D} {e : Event} {s : Site} (hd : d.site.plain = true)
    (hs : s.plain = true) (hn : poll d e s = some (some d')) : d'.site.plain = true := by
  unfold poll at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    split_ifs
    · exact hs
    · exact hd
  · cases hn

/-- The other sites' successors. -/
theorem siteOk_rest {s : Site} (hs : s.plain = true) (he : s ≠ .elect)
    {l0 l1 neg cnt pha par : BitVec 64} {d' : D} {e : Event}
    (hn : succ P L g ⟨s, l0, l1, neg, cnt, pha, par⟩ e = some (some d')) : SiteOk P L g d' := by
  refine siteOk_plain ?_
  cases s with
  | elect => exact absurd rfl he
  | loadTopk | loadExtra | leave _ => cases hs
  | trap | exit => simp [succ] at hn
  | qWait | qCopyWait | kvWait | soWait => exact plain_poll rfl rfl hn
  | qCopyFence =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    unfold loopEntry
    split_ifs <;> rfl
  | pvCommit =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    unfold loopEnd
    split_ifs <;> rfl
  | _ =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    first | rfl | (split_ifs <;> rfl)

/-- **Every state the machine reaches by a step has `SiteOk`.** -/
theorem siteOk_next {d d' : D} {e : Event} (hn : succ P L g d e = some (some d')) :
    SiteOk P L g d' := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases s with
  | elect => exact siteOk_elect hn
  | loadTopk => exact siteOk_nc (.inl rfl) hn
  | loadExtra => exact siteOk_nc (.inr rfl) hn
  | leave _ => simp [succ] at hn
  | _ => refine siteOk_rest ?_ ?_ hn <;> first | rfl | simp

/-- The first state has `SiteOk`. -/
theorem siteOk_init : SiteOk P L g init := ⟨nofun, nofun, fun _ h => by cases h⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
