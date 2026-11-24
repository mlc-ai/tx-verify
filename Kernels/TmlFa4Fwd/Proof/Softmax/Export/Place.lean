-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasPoll
public import Kernels.TmlFa4Fwd.Proof.Softmax.Order
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The place of a softmax lane's state in its tile

`soft_place`: a state of a softmax lane is a startup state, before every class of the role, or a
role state whose counts are the places' at its rounds, in the region of the tile of its CTA. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before allSites mem_allSites Reg)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **The tile of a softmax lane** has `B` biased and `P` plain rounds after the first. -/
def SoftTile (p : Params) (L : Launch) (g B P : Nat) : Prop :=
  ∃ R bal, Epilogue.Picked p L g R bal ∧
    (Softmax.nB p L g (softRef p L g R bal)).toNat = B ∧
    (Softmax.nP p L g (softRef p L g R bal)).toNat = P

theorem SoftTile.rounds {B P : Nat} (h : SoftTile p L g B P) : SoftRounds p L g (1 + B + P) := by
  obtain ⟨R, bal, hP, rfl, rfl⟩ := h
  exact ⟨R, bal, hP, rfl⟩

theorem SoftTile.stage {B P : Nat} (h : SoftTile p L g B P) : StageRounds p L g B := by
  obtain ⟨R, bal, hP, rfl, rfl⟩ := h
  exact ⟨R, bal, hP, rfl⟩

theorem SoftTile.picked {B P : Nat} (h : SoftTile p L g B P) : ∃ R bal, Epilogue.Picked p L g R bal
    :=
  let ⟨R, bal, hP, _⟩ := h; ⟨R, bal, hP⟩

theorem exists_softTile (h : ∃ R bal, Epilogue.Picked p L g R bal) : ∃ B P, SoftTile p L g B P :=
  let ⟨R, bal, hP⟩ := h; ⟨_, _, R, bal, hP, rfl, rfl⟩

private theorem done_nat {r : Nat} {n : Int} (h : Softmax.Done r n) : n.toNat = r := by
  rcases h with h | ⟨rfl, h⟩ <;> omega

/-- The region of a site, by its position, and what the site says. -/
private def siteChk (s : Softmax.Site) : Bool :=
  (decide (s.pos < 10064) || (decide (10064 ≤ s.pos) && decide (s.pos ≤ 13307) && s.hasUk) ||
    (decide (13322 ≤ s.pos) && decide (s.pos ≤ 15209) && s.hasUk) ||
    (Softmax.finR s && s.hasUk) ||
    (decide (15228 ≤ s.pos) && s.noTile) ||
    (decide (15228 ≤ s.pos) && !s.noTile && Progress.Sm.late s &&
      [false, true].all fun b =>
        decide ((ptsOf b (.acquire 80)).countP (before s) = 1) &&
        decide ((ptsOf b .nb).countP (before s) = 2) &&
        decide ((ptsOf b .sb).countP (before s) = 1))) &&
  (!s.noTile || (decide (SmWarp.epi s = .exit false)))

private theorem site_chk : allSites.all siteChk = true := by decide +kernel

private theorem cnt_tab (b : Bool) :
    (ptsOf b (.acquire 80)).countP Softmax.inBias = 1 ∧
      (ptsOf b (.acquire 80)).countP Softmax.inPlain = 1 ∧
      (ptsOf b .nb).countP Softmax.inBias = 1 ∧ (ptsOf b .nb).countP Softmax.inPlain = 1 ∧
      (ptsOf b .sb).countP Softmax.inBias = 1 ∧ (ptsOf b .sb).countP Softmax.inPlain = 0 := by
  cases b <;> decide +kernel

/-- **A lane's stage-barrier events are at most one more than the tile's biased rounds.** -/
theorem soft_stage_le (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {B : Nat} (hB : StageRounds p L g B) :
    ((X.tr g).take k).countP (Execution.isBarId (stageId (Prologue.warpIndex L g / 4))) ≤ B + 1 :=
        by
  by_contra hlt
  obtain ⟨j, ⟨pc, kd⟩, hj, hget, hb', hcj⟩ := exists_nthEv (X := X) (g := g) (k := k)
    (p := Execution.isBarId (stageId (Prologue.warpIndex L g / 4))) (n := B + 1) (by omega)
  cases kd <;> simp only [Execution.isBarId, beq_iff_eq, Bool.false_eq_true] at hb'
  subst hb'
  obtain ⟨-, -, -, -, B', hB', hle⟩ := soft_stage_bar hp hX hFw hw
    (by unfold stageId; omega) hget
  obtain rfl := hB.stage rfl hw hw rfl hB'
  rw [hcj] at hle
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g < 8)
include hp hX hFw hub hg hw

/-- **The place of a state of a softmax lane.** -/
theorem soft_place {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    (Progress.time p L g σ < Progress.scanBase ∧
      (∃ s n, σ = (.inl s, n) ∧ ∀ c, n (.soft c) = 0)) ∨
    ∃ d n rb rp, σ = SmWarp.sinj p L g d n ∧ n .ub = 0 ∧ 3 ≤ n .shfl ∧
      (∀ c, c.pointed = true → n (.soft c) = passed (ptsOf (Softmax.lz L g) c) d.scheduler.site rb
          rp) ∧
      (∀ c, d.scheduler.site = .sldw c → d.k = 1) ∧
      SmWarp.SFits p L g d.scheduler (n .shfl) (n .vote) ∧
      (∀ B P, SoftTile p L g B P → Reg B P d.scheduler.site rb rp ∧ d.scheduler.site.noTile = false)
          ∧
      ((¬ ∃ R bal, Epilogue.Picked p L g R bal) →
        d.scheduler.site.pos < 10064 ∨ d.scheduler.site.noTile = true) := by
  have hJ := (goodR hp hX hFw hg k).2 σ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · left
    have hS := (SmWarp.good hp hX hw hg rfl k).2 _ hσ
    have hx : ∀ r, s.site ≠ .enter r := by
      intro r he
      have h1 := hS.1
      simp only [SmWarp.StartW, StartAt0, StartAt, he, ite_self] at h1
    have h1 := Progress.startTime_lt hx
    exact ⟨h1, s, n, rfl, hS.2.2⟩
  cases i with
  | softmax =>
    right
    have hub0 : n .ub = 0 := by
      by_contra h
      obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
      cases kind <;> simp [cls] at hk
      exact hub ⟨(g, j), pc, _, hf⟩
    obtain ⟨-, h3, hR⟩ := JR.softmax hJ
    obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR hub0
    have hcnt : ∀ c', c'.pointed = true →
        n (.soft c') = passed (ptsOf (Softmax.lz L g) c') d.scheduler.site rb rp := fun c' hc' => by
      rw [← hLk c' hc']; exact hQ.cnt c' hc'
    refine ⟨d, n, rb, rp, rfl, hub0, h3, hcnt, hQ.wait, hF, ?_⟩
    have hchk := List.all_eq_true.mp site_chk d.scheduler.site (mem_allSites _)
    simp only [siteChk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hchk
    obtain ⟨hreg, hno⟩ := hchk
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := cnt_tab (Softmax.lz L g)
    -- the tile at a round site
    have tile : d.scheduler.site.hasUk = true → ∃ R bal, Epilogue.Picked p L g R bal ∧
        Softmax.nB p L g d.scheduler.v = Softmax.nB p L g (softRef p L g R bal) ∧
        Softmax.nP p L g d.scheduler.v = Softmax.nP p L g (softRef p L g R bal) := by
      intro huk
      obtain ⟨hFE, hu⟩ := hF
      have hep : SmWarp.epi d.scheduler.site = .ready 0 := by
        revert huk
        cases d.scheduler.site <;> simp [Softmax.Site.hasUk, Softmax.Site.rgn, SmWarp.epi]
      simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
      obtain ⟨R, bal, hC, h0, h1⟩ := hFE
      exact ⟨R, bal, hC.1, nBP hC h0 h1 (hu huk)⟩
    have tileE : d.scheduler.site.hasUk = true → ∀ B P, SoftTile p L g B P →
        Softmax.nB p L g d.scheduler.v = (Softmax.nB p L g d.scheduler.v).toNat ∧
          (Softmax.nB p L g d.scheduler.v).toNat = B ∧ (Softmax.nP p L g d.scheduler.v).toNat = P ∨
        (Softmax.nB p L g d.scheduler.v < 0 ∧ B = 0 ∧ (Softmax.nP p L g d.scheduler.v).toNat = P) :=
            by
      rintro huk B P ⟨R, bal, hP, rfl, rfl⟩
      obtain ⟨R', bal', hP', e1, e2⟩ := tile huk
      obtain ⟨rfl, rfl⟩ := hP.unique hP'
      rw [← e1, ← e2]
      generalize Softmax.nB p L g d.scheduler.v = x
      generalize Softmax.nP p L g d.scheduler.v = y
      omega
    have late : Progress.Sm.late d.scheduler.site = true →
        (∀ b ∈ [false, true], ((ptsOf b (.acquire 80)).countP (before d.scheduler.site) = 1 ∧
          (ptsOf b .nb).countP (before d.scheduler.site) = 2) ∧
          (ptsOf b .sb).countP (before d.scheduler.site) = 1) →
        SoftRounds p L g (1 + rb + rp) ∧ ∀ B, StageRounds p L g B → rb = B := by
      intro hl htab
      obtain ⟨⟨b1, b2⟩, b3⟩ := htab (Softmax.lz L g) (by cases Softmax.lz L g <;> simp)
      have h80 := hcnt (.acquire 80) rfl
      have hnb := hcnt .nb rfl
      have hsb := hcnt .sb rfl
      simp only [passed, t1, t2, t3, t4, t5, t6, b1, b2, b3] at h80 hnb hsb
      have e1 : ((X.tr g).take k).countP (Execution.isBarId (Prologue.warpIndex L g + 3)) =
          (1 + rb + rp) + 1 := by
        rw [soft_isBarId hw, count hσ, hnb]; omega
      have e2 : okPolls (sobj L g 80) ((X.tr g).take k) = 1 + rb + rp := by
        rw [sobj, soft_okPolls hw, count hσ, h80]; omega
      refine ⟨soft_late_rounds hp hX hFw hw e1 e2, fun B hB => ?_⟩
      obtain ⟨B', hB', h1⟩ := soft_late_stage hp hX hFw hw e1 e2
      obtain rfl := hB.stage rfl hw hw rfl hB'
      have h2 := soft_stage_le (k := k) hp hX hFw hw hB
      rw [soft_isStage hw, count hσ, hsb] at h1 h2
      omega
    have done : ∀ {r : Nat} {x : Int}, Softmax.Done r x → x.toNat = r := done_nat
    constructor
    · intro B P hT
      have hnt : d.scheduler.site.noTile = false := by
        rw [Bool.eq_false_iff]
        intro h
        refine noPicked_of_exit (p := p) (L := L) (g := g) hF.1 ?_ hT.picked
        exact hno.resolve_left (by simp [h])
      refine ⟨?_, hnt⟩
      unfold Reg
      rcases hreg with ((((h | h) | h) | h) | h) | h
      · have hpr := hQ.pre (by simp [Softmax.preR, h])
        exact .inl ⟨h, hpr⟩
      · obtain ⟨⟨h1, h2⟩, huk⟩ := h
        obtain ⟨b1, -, b2, -⟩ := hQ.bias (by simp [Softmax.inBias, h1, h2])
        have := tileE huk B P hT
        generalize Softmax.nB p L g d.scheduler.v = x at this b2
        exact .inr (.inl ⟨⟨h1, h2⟩, by omega, b1⟩)
      · obtain ⟨⟨h1, h2⟩, huk⟩ := h
        obtain ⟨-, b2, -, b3⟩ := hQ.plain (by simp [Softmax.inPlain, h1, h2])
        have := done b3
        have := tileE huk B P hT
        generalize Softmax.nB p L g d.scheduler.v = x at *
        generalize Softmax.nP p L g d.scheduler.v = y at *
        exact .inr (.inr (.inl ⟨⟨h1, h2⟩, by omega, by omega⟩))
      · obtain ⟨h1, huk⟩ := h
        obtain ⟨b1, b2⟩ := hQ.fin h1
        have := done b1
        have := done b2
        have := tileE huk B P hT
        simp only [Softmax.finR, Bool.and_eq_true, decide_eq_true_eq] at h1
        generalize Softmax.nB p L g d.scheduler.v = x at *
        generalize Softmax.nP p L g d.scheduler.v = y at *
        exact .inr (.inr (.inr ⟨h1.1, hnt, by omega, by omega⟩))
      · rw [h.2] at hnt; cases hnt
      · obtain ⟨⟨⟨h1, -⟩, hl⟩, htab⟩ := h
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at htab
        obtain ⟨hR, hB⟩ := late hl htab
        have e1 := hB B hT.stage
        have e2 := hR.unique hT.rounds
        exact .inr (.inr (.inr ⟨h1, hnt, e1, by omega⟩))
    · intro hno'
      rcases hreg with ((((h | h) | h) | h) | h) | h
      · exact .inl h
      · exact (hno' (let ⟨R, bal, hP, _⟩ := tile h.2; ⟨R, bal, hP⟩)).elim
      · exact (hno' (let ⟨R, bal, hP, _⟩ := tile h.2; ⟨R, bal, hP⟩)).elim
      · exact (hno' (let ⟨R, bal, hP, _⟩ := tile h.2; ⟨R, bal, hP⟩)).elim
      · exact .inr h.2
      · obtain ⟨⟨⟨h1, -⟩, hl⟩, htab⟩ := h
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at htab
        obtain ⟨⟨R, bal, hP, -⟩, -⟩ := late hl htab
        exact (hno' ⟨R, bal, hP⟩).elim
  | correction => have := (JR.correction hJ (by omega)).1; omega
  | mma => have := (JR.mma hJ).1; omega
  | epilogue => have := (JR.epilogue hJ).1; omega
  | loader b => have := (JR.loader hJ).1; omega
  | stub r => exact (JR.not_stub hJ).elim

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
