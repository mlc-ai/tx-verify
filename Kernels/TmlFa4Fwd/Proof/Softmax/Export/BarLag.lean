-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.PlaceLag
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Lib.ThreadTime
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Softmax.RefEv
import Lemmas.Kernel.Safety.Schedule
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A softmax lane short of a barrier event is early

A softmax lane that has made no more events on a named barrier than a place of its tile has passed
has not exited and is no later than the place (`soft_bar_lag`); one that has made no barrier-2
event is no later than its first (`soft_bar2_first`), and one that has made at most one no later
than its last (`soft_bar2_end`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (ptsOf passed before allSites mem_allSites Reg ordK
  val valT sm)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The named barrier of a barrier class of a softmax lane. -/
def softBarId (L : Launch) (g : Nat) : Softmax.Cnt → Nat
  | .nb => Prologue.warpIndex L g + 3
  | .sb => stageId (Prologue.warpIndex L g / 4)
  | _ => 2

/-- The barrier classes of a softmax lane are the events on its barriers. -/
theorem soft_bar_cls (hw : Prologue.warpIndex L g < 8) {c : Softmax.Cnt}
    (hc : c = .nb ∨ c = .sb ∨ c = .bar2) :
    cls L g (.soft c) = Execution.isBarId (softBarId L g c) := by
  have hw' : g % L.block / 32 < 8 := hw
  funext e
  obtain ⟨pc, kind⟩ := e
  rcases hc with rfl | rfl | rfl <;> cases kind <;>
    simp [Execution.isBarId, cls, Softmax.cls, Softmax.Cnt.pointed, hw', softBarId, soft_nbW hw,
      soft_stage_id hw, Bool.beq_eq_decide_eq]

/-- A tile's rounds are within the time table's slots. -/
theorem SoftTile.bmax (hp : Pre p L m) (hg : g < L.threads) {B P : Nat} (hT : SoftTile p L g B P) :
    1 + B + P ≤ Progress.bmax p := by
  obtain ⟨R, bal, hP⟩ := hT.picked
  have hM : MmaRounds p L g _ := ⟨R, bal, hP, rfl⟩
  rw [hT.rounds.mma rfl hM]
  exact mma_rounds_bmax hp hg hM

/-- The tile of a softmax lane is its stage's. -/
theorem SoftTile.cta {y : Nat} (hc : y / L.block = g / L.block) (hw : Prologue.warpIndex L g < 8)
    (hwy : Prologue.warpIndex L y < 8)
    (hs : Prologue.warpIndex L y / 4 = Prologue.warpIndex L g / 4) {B P : Nat}
    (hT : SoftTile p L g B P) : SoftTile p L y B P := by
  obtain ⟨R, bal, hP⟩ := hT.picked
  obtain ⟨B', P', hT'⟩ := exists_softTile (p := p) (L := L) (g := y)
    ⟨R, bal, Epilogue.Picked.cta hc.symm hP⟩
  have e1 := hT'.stage.stage hc hwy hw hs hT.stage
  have hM : MmaRounds p L g _ := ⟨R, bal, hP, rfl⟩
  have e2 := hT.rounds.mma rfl hM
  have e3 := hT'.rounds.mma hc hM
  obtain rfl := e1
  obtain rfl : P' = P := by omega
  exact hT'

private theorem bar_pts : [Softmax.Cnt.nb, .sb, .bar2].all (fun c => [false, true].all fun b =>
    allSites.all fun s => !(decide (Softmax.sig s = some c)) ||
      (decide (0 < (ptsOf b c).countP (· = s.pos)) && !s.isPoll && !s.delayed && s.first)) =
      true := by decide +kernel

private theorem bar_pt {c : Softmax.Cnt} (hc : c = .nb ∨ c = .sb ∨ c = .bar2) (b : Bool)
    {s : Softmax.Site} (hs : Softmax.sig s = some c) :
    0 < (ptsOf b c).countP (· = s.pos) ∧ s.isPoll = false ∧ s.delayed = false ∧ s.first = true := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp bar_pts c (by
    rcases hc with rfl | rfl | rfl <;> simp)) b (by cases b <;> simp)) s (mem_allSites s)
  simp only [hs, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h1
  obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h1
  exact ⟨h2, h3, h4, h5⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g < 8)
include hp hX hFw hub hg hw

omit hX hFw hg in
/-- The event of a lane at a site of a barrier class is of the class. -/
private theorem bar_ev {c : Softmax.Cnt} (hc : c = .nb ∨ c = .sb ∨ c = .bar2) {d : Softmax.D}
    {e : Event} (he : X.get (g, k) = some e) (hev : Softmax.Ev p L g d e)
    (hs : Softmax.sig d.site = some c) : cls L g (.soft c) e = true := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf =>
    hub ⟨(g, k), e.pc, f, by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  obtain ⟨-, h2, h3, h4⟩ := bar_pt hc false hs
  have hpt : c.pointed = true := by rcases hc with rfl | rfl | rfl <;> rfl
  have h := Softmax.ev_cls (p := p) (c := c) hp hev hne (by rw [h2]; intro h; cases h)
    (by rw [h3]; intro h; cases h) (fun c' h' => by rw [h'] at h4; cases h4)
    (by simp [Softmax.Cnt.sited, hpt])
  have hw' : g % L.block / 32 < 8 := hw
  simp [cls, hpt, hw', h, hs]

/-- **A lane with no more events on a named barrier than a place of its tile has passed** has not
exited and is no later than the place. -/
theorem soft_bar_lag {B P : Nat} (hT : SoftTile p L g B P) {c : Softmax.Cnt}
    (hc : c = .nb ∨ c = .sb ∨ c = .bar2) {s0 : Softmax.Site} {rb0 rp0 : Nat} {a : Nat × Nat}
    (hs : Softmax.sig s0 = some c) (ha : val (Progress.Sm.stage L g) s0 = some a)
    (hR0 : Reg B P s0 rb0 rp0) (hn0 : s0.noTile = false) (hp0 : s0.pos ≤ 15232)
    (hle : (X.tr g).countP (Execution.isBarId (softBarId L g c)) ≤
      passed (ptsOf (Softmax.lz L g) c) s0 rb0 rp0) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ valT p (rb0 + rp0) a := by
  have hpt : c.pointed = true := by rcases hc with rfl | rfl | rfl <;> rfl
  have hw' : g % L.block / 32 < 8 := hw
  obtain ⟨h0, -, -, h4⟩ := bar_pt hc (Softmax.lz L g) hs
  have hb := hT.bmax hp hg
  have hsub : ∀ d : Softmax.D, d.site = s0 → Progress.Sm.subOff d = 0 := fun d hd => by
    unfold Progress.Sm.subOff
    rw [hd]
    cases s0 <;> first | rfl | (exfalso; rcases hc with rfl | rfl | rfl <;> cases hs)
  refine soft_place_lag hp hX hFw hub hg hw hT (Execution.isBarId (softBarId L g c))
    (ptsOf (Softmax.lz L g) c) (fun _ => 0) (e0 := 0) (fun hσ _ hA => ?_) hR0 hn0 h0
    (fun l h => by rw [h] at hs; rcases hc with rfl | rfl | rfl <;> cases hs) hle ?_
    (fun hσ he hev hd _ => ?_) (fun hA hK => ?_) (fun hA hd _ => ?_)
  · rw [← soft_bar_cls hw hc, count hσ, hA.cnt c hpt, Nat.add_zero]
  · have := Progress.scanBase_le_primeBase p
    unfold valT Progress.pipeBase; omega
  · have h1 := bar_ev hp hub hw hc he hev (by rw [hd]; exact hs)
    rwa [soft_bar_cls hw hc] at h1
  · exact soft_time_lt hp hA ha hR0 hp0 hK
  · have h1 := (soft_round_time hA (by rw [hd]; exact ha)).1
    rw [hsub _ hd] at h1
    exact ⟨h1, fun h => by omega⟩

end

/-! ### Barrier 2 -/

private theorem bar2_tab : [false, true].all (fun b => allSites.all fun s =>
    (decide (s = .setmax) || decide (s = .bar1) ||
      decide (1 ≤ (ptsOf b .bar2).countP (before s))) &&
    ((decide ((ptsOf b .bar2).countP (before s) ≤ 1) ==
      !(decide (s = .exit true) || decide (s = .exit false))))) = true := by decide +kernel

private theorem bar2_rnd (b : Bool) : (ptsOf b .bar2).countP Softmax.inBias = 0 ∧
    (ptsOf b .bar2).countP Softmax.inPlain = 0 := by cases b <;> decide +kernel

private theorem end_chk : allSites.all (fun s =>
    (match Progress.Sm.endOff s with
      | some (l, o) => decide (Progress.Sm.late s = l) && decide (s.noTile = !l) &&
          decide (SmWarp.epi s = .exit l) && (decide (s = .exit l) || decide (o ≤ 4)) &&
          (decide (s = .exit l) || decide (s = .barEnd l) || decide (o ≤ 2))
      | none => !s.noTile && decide ((SmWarp.epi s).late = Progress.Sm.late s)) &&
    (!Progress.Sm.late s || decide (15228 ≤ s.pos)) &&
    [0, 1].all fun st => match Progress.Sm.place st s with
      | some (bd, _, o) => decide (bd + o + 1 < Progress.span)
      | none => true) = true := by decide +kernel

/-- A state before the end is before every end, and before the prime region's end when its CTA
picked no tile. -/
theorem soft_early_time (hp : Pre p L m) {d : Softmax.D} {n : Cls → Nat}
    (hF : SmWarp.SFits p L g d (n .shfl) (n .vote)) (he : Progress.Sm.endOff d.site = none) :
    Progress.Sm.time p L g d n < Progress.doneBase p ∧
      ((¬ ∃ R bal, Epilogue.Picked p L g R bal) → d.site.pos < 10064 →
        Progress.Sm.time p L g d n < Progress.endT p false 0) := by
  have hst : Progress.Sm.stage L g = 0 ∨ Progress.Sm.stage L g = 1 := by
    unfold Progress.Sm.stage; split <;> simp
  have hprv : Progress.primeBase p = Progress.scanBase + 2 * Progress.cmax p + 4 := rfl
  have hend : Progress.primeBase p + 1024 ≤ Progress.endBase p := by
    have := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    unfold Progress.endBase Progress.tailBase; omega
  have hdone : Progress.doneBase p = Progress.endBase p + 4 * Progress.cmax p + 8 := rfl
  have htl : Progress.tailBase p ≤ Progress.endBase p := Nat.le_add_right _ _
  have hcm : Progress.cmax p = 7 * (p.batch + 3) + 6 := rfl
  have he0 : Progress.endT p false 0 = Progress.primeBase p + 1000 := by simp [Progress.endT]
  have hchk := List.all_eq_true.mp end_chk d.site (mem_allSites _)
  simp only [he, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨-, hl⟩, hlate⟩, hpl⟩ := hchk
  have hpl' := hpl (Progress.Sm.stage L g) (by rcases hst with h | h <;> simp [h])
  have hsub : Progress.Sm.subOff d ≤ 1 := by unfold Progress.Sm.subOff; split <;> omega
  simp only [Progress.Sm.time, he]
  split
  · rename_i bd past o hpp
    rw [hpp] at hpl'
    simp only [decide_eq_true_eq] at hpl'
    have h1 := Progress.clk_lt_tail (p := p)
      (a := n (.soft (.acquire 80)) - if past then 1 else 0) (o := bd + o + Progress.Sm.subOff d)
      (by omega)
    refine ⟨by omega, fun hno _ => ?_⟩
    exfalso
    have huk : d.site.hasUk = true := by
      revert hpp
      cases d.site <;> simp [Progress.Sm.place, Softmax.Site.hasUk, Softmax.Site.rgn]
    have hFE := hF.1
    have hep : SmWarp.epi d.site = .ready 0 := by
      revert huk
      cases d.site <;> simp [Softmax.Site.hasUk, Softmax.Site.rgn, SmWarp.epi]
    simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
    obtain ⟨R, bal, hC, -⟩ := hFE
    exact hno ⟨R, bal, hC.1⟩
  · split
    · rename_i o ho
      have : o ≤ 3 := by
        revert ho
        cases d.site <;> simp [Progress.Sm.pre] <;> omega
      exact ⟨by omega, fun _ _ => by omega⟩
    · split_ifs with h1 h2 h3
      · exact ⟨by omega, fun _ _ => by omega⟩
      · exact ⟨by omega, fun _ _ => by omega⟩
      · have h6 := Epilogue.fits_coll_le_all hp hF.1
        have h7 : Progress.Out.ballots (Progress.Sm.toE d.site) ≤ 1 := by
          unfold Progress.Out.ballots; split <;> omega
        have h8 : ∀ b c co, Progress.passTime b c co ≤ b + 2 * c := fun b c co => by
          unfold Progress.passTime; split <;> omega
        have h9 := h8 (Progress.endBase p) (n .shfl + Progress.Out.ballots (Progress.Sm.toE d.site))
          (Progress.Out.coll (Progress.Sm.toE d.site))
        refine ⟨by omega, fun _ h => ?_⟩
        rcases hlate with h' | h'
        · rw [h3] at h'; cases h'
        · omega
      · have h6 := Epilogue.fits_coll_le hp hF.1 (hl.trans (by simpa using h3))
        have h7 : Progress.Out.ballots (Progress.Sm.toE d.site) ≤ 1 := by
          unfold Progress.Out.ballots; split <;> omega
        have h8 := Progress.pass_lt_prime (p := p)
          (c := n .shfl + Progress.Out.ballots (Progress.Sm.toE d.site))
          (by unfold Progress.cmax; omega) (Progress.Out.coll (Progress.Sm.toE d.site))
        exact ⟨by omega, fun _ _ => by omega⟩

private theorem nexit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8)
    (h : (X.tr g).countP (Execution.isBarId 2) ≤ 1) :
    ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩ := by
  intro j pc hx
  have := sc_exit_bar2 hp hX hFw hx (by omega)
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g < 8)
include hp hX hFw hub hg hw

omit hp hX hFw hub hg in
/-- The sites with barrier-2 counts. -/
private theorem bar2_site {d : Softmax.Control.D} {n : Cls → Nat} {rb rp : Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)))
    (hc : n (.soft .bar2) = passed (ptsOf (Softmax.lz L g) .bar2) d.scheduler.site rb rp) :
    (((X.tr g).take k).countP (Execution.isBarId 2) = 0 → d.scheduler.site = .setmax ∨
        d.scheduler.site = .bar1) ∧
      (((X.tr g).take k).countP (Execution.isBarId 2) ≤ 1 → ∀ l, d.scheduler.site ≠ .exit l) := by
  obtain ⟨t1, t2⟩ := bar2_rnd (Softmax.lz L g)
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp bar2_tab (Softmax.lz L g)
    (by cases Softmax.lz L g <;> simp)) d.scheduler.site (mem_allSites _)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  simp only [passed, t1, t2, Nat.mul_zero, Nat.add_zero] at hc
  have h2 : ((X.tr g).take k).countP (Execution.isBarId 2) = n (.soft .bar2) := by
    rw [← count hσ]; exact soft_isBar2 hw
  rw [h2, hc]
  obtain ⟨h3, h4⟩ := h1
  refine ⟨fun h => ?_, fun h l hl => ?_⟩
  · rcases h3 with h3 | h3
    · exact h3
    · omega
  · rw [hl] at h4 h
    simp only [h, decide_true] at h4
    cases l <;> simp at h4

/-- **A softmax lane with no barrier-2 event** is no later than its first. -/
theorem soft_bar2_first (h : (X.tr g).countP (Execution.isBarId 2) = 0) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ Progress.scanBase + 3 := by
  have hk : ∀ k, ((X.tr g).take k).countP (Execution.isBarId 2) = 0 := fun k => by
    have := (List.take_sublist k (X.tr g)).countP_le (p := Execution.isBarId 2)
    omega
  have key : ∀ {k σ}, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ < Progress.scanBase + 3 ∨ ∃ d n, σ = SmWarp.sinj p L g d n ∧
        d.scheduler.site = .bar1 ∧ Progress.time p L g σ = Progress.scanBase + 3 := by
    intro k σ hσ
    rcases soft_place hp hX hFw hub hg hw hσ with ⟨h1, -⟩ | ⟨d, n, rb, rp, rfl, -, -, hc, -⟩
    · left; omega
    · rcases (bar2_site hw hσ (hc .bar2 rfl)).1 (hk k) with hs | hs
      · left
        show Progress.Sm.time p L g d.scheduler n < _
        simp [Progress.Sm.time, hs, Progress.Sm.place, Progress.Sm.pre, Progress.Sm.endOff]
      · right
        refine ⟨d, n, rfl, hs, ?_⟩
        show Progress.Sm.time p L g d.scheduler n = _
        simp [Progress.Sm.time, hs, Progress.Sm.place, Progress.Sm.pre, Progress.Sm.endOff]
  refine ⟨nexit hp hX hFw hw (by omega), threadTime_le (fun σ hσ => ?_) fun σ e hσ he => ?_⟩
  · rcases key hσ with h | ⟨_, _, -, -, h⟩ <;> omega
  · rcases key hσ with h | ⟨d, n, rfl, hs, h⟩
    · omega
    · exfalso
      have hev : Softmax.Ev p L g d.scheduler e := by
        rcases SmWarp.open_ev hp hX hFw hw he (fun f hf => hub ⟨(g, _), e.pc, f, by
            rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩) with ⟨s, n', hσ', -⟩ |
          ⟨d', n', hσ', -, -, -, hev⟩
        · rw [hσ] at hσ'; cases hσ'
        · rw [hσ] at hσ'; cases hσ'; exact hev.1
      simp only [Softmax.Ev, hs] at hev
      have h2 : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 2) <
          (X.tr g).countP (Execution.isBarId 2) :=
        Frame.countP_take_lt_countP (P := Execution.isBarId 2) (es := X.tr g) he
          (by simp [Execution.isBarId, hev])
      omega

/-- **A softmax lane with at most one barrier-2 event** is no later than its last, the second
pass's exactly when its CTA picked a tile. -/
theorem soft_bar2_end {l : Bool} (hl : l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal)
    (h : (X.tr g).countP (Execution.isBarId 2) ≤ 1) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ Progress.endT p l 4 := by
  have hk : ∀ k, ((X.tr g).take k).countP (Execution.isBarId 2) ≤ 1 := fun k =>
    le_trans (List.take_sublist k (X.tr g)).countP_le h
  have hdone : Progress.doneBase p ≤ Progress.endT p true 0 := by simp [Progress.endT]
  have hT : ∀ a b, a < b → Progress.endT p l a < Progress.endT p l b := fun a b hab => by
    unfold Progress.endT; split <;> omega
  have h04 := hT 0 4 (by omega)
  have key : ∀ {k σ}, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ < Progress.endT p l 4 ∨ ∃ d n l', σ = SmWarp.sinj p L g d n ∧
        d.scheduler.site = .barEnd l' ∧ Progress.time p L g σ = Progress.endT p l 4 := by
    intro k σ hσ
    rcases soft_place hp hX hFw hub hg hw hσ with ⟨h1, -⟩ |
      ⟨d, n, rb, rp, rfl, -, -, hc, -, hF, hreg, hno⟩
    · left; have := Progress.endT_ge p l 4; omega
    show Progress.Sm.time p L g d.scheduler n < _ ∨ _
    cases hend : Progress.Sm.endOff d.scheduler.site with
    | none =>
      left
      obtain ⟨t1, t2⟩ := soft_early_time hp hF hend
      cases l with
      | true => omega
      | false =>
        have hn : ¬ ∃ R bal, Epilogue.Picked p L g R bal := fun h => by
          have := hl.mpr h; cases this
        have hchk := List.all_eq_true.mp end_chk d.scheduler.site (mem_allSites _)
        simp only [hend, Bool.and_eq_true, Bool.not_eq_true'] at hchk
        have h1 := (hno hn).resolve_right (by rw [hchk.1.1.1]; simp)
        have := t2 hn h1
        omega
    | some lo =>
      obtain ⟨l', o⟩ := lo
      have hchk := List.all_eq_true.mp end_chk d.scheduler.site (mem_allSites _)
      simp only [hend, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨⟨⟨⟨⟨⟨-, hnt⟩, hex⟩, -⟩, ho⟩, -⟩, -⟩ := hchk
      have hll : l' = l := by
        cases l with
        | true =>
          obtain ⟨B, P, hT⟩ := exists_softTile (hl.mp rfl)
          have := (hreg B P hT).2
          rw [hnt] at this
          simpa using this
        | false =>
          cases l' with
          | false => rfl
          | true =>
            exfalso
            have hn : ¬ ∃ R bal, Epilogue.Picked p L g R bal := fun h => by
              have := hl.mpr h; cases this
            rcases hno hn with h1 | h1
            · revert hend h1
              cases d.scheduler.site <;> simp [Progress.Sm.endOff, Softmax.Site.pos,
                  Softmax.Site.pc]
            · rw [hnt] at h1; cases h1
      subst hll
      have ht : Progress.Sm.time p L g d.scheduler n = Progress.endT p l' o := by
        have hpl : Progress.Sm.place (Progress.Sm.stage L g) d.scheduler.site = none := by
          revert hend
          cases d.scheduler.site <;> simp [Progress.Sm.endOff, Progress.Sm.place]
        have hpr : Progress.Sm.pre d.scheduler.site = none := by
          revert hend
          cases d.scheduler.site <;> simp [Progress.Sm.endOff, Progress.Sm.pre]
        simp only [Progress.Sm.time, hpl, hpr, hend]
      have hx := (bar2_site hw hσ (hc .bar2 rfl)).2 (hk k)
      rcases ho with (ho | ho) | ho
      · exact absurd ho (hx l')
      · right
        refine ⟨d, n, l', rfl, ho, ?_⟩
        show Progress.Sm.time p L g d.scheduler n = _
        rw [ht]
        rw [ho] at hend
        simp only [Progress.Sm.endOff, Option.some.injEq, Prod.mk.injEq] at hend
        rw [← hend.2]
      · left
        rw [ht]
        exact hT o 4 (by omega)
  refine ⟨nexit hp hX hFw hw h, threadTime_le (fun σ hσ => ?_) fun σ e hσ he => ?_⟩
  · rcases key hσ with h | ⟨_, _, _, -, -, h⟩ <;> omega
  · rcases key hσ with h | ⟨d, n, l', rfl, hs, h'⟩
    · omega
    · exfalso
      have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, _), e.pc, f, by
        rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
      obtain ⟨hev, hc⟩ : Softmax.Ev p L g d.scheduler e ∧
          ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 2) = 1 := by
        rcases soft_place hp hX hFw hub hg hw hσ with ⟨-, s, n', h1, -⟩ |
          ⟨d', n', rb, rp, h1, -, -, hc, -⟩
        · cases h1
        cases h1
        rcases SmWarp.open_ev hp hX hFw hw he hne with ⟨s, n', hσ', -⟩ |
          ⟨d', n', hσ', -, -, -, hev⟩
        · rw [hσ] at hσ'; cases hσ'
        · rw [hσ] at hσ'; cases hσ'
          refine ⟨hev.1, ?_⟩
          have h1 := (bar2_site hw hσ (hc .bar2 rfl)).1
          have h2 := hk ((X.tr g).length - 1)
          by_contra h3
          rcases h1 (by omega) with h4 | h4 <;> rw [hs] at h4 <;> cases h4
      simp only [Softmax.Ev, hs] at hev
      rcases hev with hev | ⟨f, hev⟩
      · have h2 : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 2) <
            (X.tr g).countP (Execution.isBarId 2) :=
          Frame.countP_take_lt_countP (P := Execution.isBarId 2) (es := X.tr g) he
            (by simp [Execution.isBarId, hev])
        omega
      · exact hne f hev

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
