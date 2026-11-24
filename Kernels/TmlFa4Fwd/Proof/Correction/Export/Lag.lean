-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Lib.CorrGood
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Progress.CorrPre
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A correction lane short of a round is early

`corr_state`: at every state of a correction lane of a CTA with a tile, either the lane is before
the slot after its P-full arrivals of stage `q` (`Progress.clk p (A + 1) 0`), or it is past the
rounds and `A` is two more than the tile's rescale rounds. `corr_early`: a lane with at most `v`
arrivals, `v` at most the rescale rounds, is before slot `v + 1`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (RefQ ptsOf passed before inRound allSites
  mem_allSites)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem CorrRounds.unique {R R' : Nat} (h : CorrRounds p L g R) (h' : CorrRounds p L g R') :
    R = R' := by
  obtain ⟨r, b, hP, rfl⟩ := h
  obtain ⟨r', b', hP', rfl⟩ := h'
  obtain ⟨rfl, rfl⟩ := hP.unique hP'
  rfl

/-- The barriers the lane arrives on once per round: P-full and credit, each of both stages. -/
def corrO (q : Fin 4) : Nat := [96, 104, 192, 200].getD q.val 0

/-- A lane with `A` arrivals on barrier `q` is before offset `tileB q` of slot `A + corrE q`. -/
def corrE (q : Fin 4) : Nat := if q = 3 then 1 else 0
def tileB (q : Fin 4) : Nat := if q = 3 then Progress.bandS 1 else Progress.bandP 0

private theorem nb_tab : ∀ q : Fin 2, (ptsOf (.nb q)).countP inRound = 1 := by decide

private theorem rnd_tab : (ptsOf (.arrive 216)).countP inRound = 0 ∧
    ∀ q : Fin 4, (ptsOf (.arrive (corrO q))).countP inRound = 1 ∧
      (ptsOf (.arrive (corrO q))).countP (before (.fdone 1 1)) = 2 := by decide

private theorem corrO_sm (q : Fin 4) : corrO q = 96 ∨ corrO q = 104 ∨ corrO q = 192 ∨
    corrO q = 200 := by revert q; decide

/-- In a stage's part the slot is at most the P-full arrivals of either stage; past the rounds the
ready arrival is made. -/
private def siteChk (s : Correction.Site) : Bool :=
  ([0, 1, 2, 3].all fun q : Fin 4 =>
    (match Progress.Cr.part s with
      | some (st, past) => decide ((ptsOf (.nb st)).countP (before s) ≤
          (ptsOf (.arrive (corrO q))).countP (before s) + corrE q +
          if past then 1 else 0) &&
          decide (Progress.bandC st.val + (Progress.Cr.tailOff s).getD (Progress.Cr.roundOff s) +
            1 < Progress.span) &&
          decide (past = true → 1 ≤ (ptsOf (.nb st)).countP (before s)) &&
          (decide ((ptsOf (.nb st)).countP (before s) <
            (ptsOf (.arrive (corrO q))).countP (before s) + corrE q +
          if past then 1 else 0) ||
          decide (Progress.bandC st.val + (Progress.Cr.tailOff s).getD (Progress.Cr.roundOff s) +
            1 < tileB q))
      | none => true) &&
    (!Progress.Cr.late s ||
      decide ((ptsOf (.arrive 216)).countP (before s) = 1)))

private theorem site_chk : allSites.all siteChk = true := by decide +kernel

private theorem site_ok (s : Correction.Site) : siteChk s = true :=
  List.all_eq_true.mp site_chk s (mem_allSites s)

private theorem ready_site (s : Correction.Site) :
    ¬ Correction.arrOff s = 216 ∨ s = .fdone 1 1 := by
  have h : allSites.all (fun s => Correction.arrOff s != 216 || s == .fdone 1 1) = true := by
    decide +kernel
  have := List.all_eq_true.mp h s (mem_allSites s)
  simpa using this

/-- A lane that made its ready arrival has two more P-full arrivals than the tile's rescale
rounds. -/
theorem corr_late_rounds (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    (q : Fin 4) (h : 1 ≤ arrivals (obj L g 216) ((X.tr g).take k)) :
    ∃ R, CorrRounds p L g R ∧ R + 2 ≤ arrivals (obj L g (corrO q)) ((X.tr g).take k) := by
  obtain ⟨j, ⟨pc, kd⟩, hj, hget, hb', -⟩ := exists_nthEv (X := X) (g := g) (k := k)
    (p := arrivesOn (obj L g 216)) (n := 0) h
  cases kd <;> simp [arrivesOn, sourceArrive] at hb'
  subst hb'
  have hmono := countP_take_mono (arrivesOn (obj L g (corrO q))) (X.tr g) hj.le
  rcases corr_counts_nonvote hp hX hFw hw hw1 hget (fun f h => by cases h) (fun _ _ => nofun) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, hF, hev, hc⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hx (l := obj L g (216)) rfl
    cases hc
  rcases corr_mbar2 hev (l := obj L g (216)) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  have hs : d.site = .fdone 1 1 := by
    have h1 := ready_site d.site
    simpa using h1.resolve_left (not_not.mpr (obj_inj hl).symm)
  have h1 := hQ.cnt (.arrive (corrO q)) (by simp)
  obtain ⟨t2, t4⟩ := rnd_tab.2 q
  rw [hs] at h1
  simp only [passed, t2, t4] at h1
  have ht := hQ.tail (by rw [hs]; decide)
  have hR : CorrRounds p L g ((Correction.Bs p L g d.v).toNat - 1) := by
    obtain ⟨rv, -, -, hFE, hu⟩ := hF
    simp only [Epilogue.Fits, CorrWarp.toE, show CorrWarp.epi d.site = .ready 0 by rw [hs]; rfl]
      at hFE
    obtain ⟨R, bal, hC, h0, h1⟩ := hFE
    have hb := CorrWarp.bs_ref hC h0 h1 (hu (by rw [hs]; rfl))
    exact ⟨R, bal, hC.1, by rw [hb]; rfl⟩
  refine ⟨_, hR, ?_⟩
  have h2 : arrivals (obj L g (corrO q)) ((X.tr g).take j) = 2 + r * 1 := by
    rw [corr_arrivals, hc, h1]
  unfold arrivals at h2 ⊢
  omega

/-- A correction lane's exit is at the exit site. -/
theorem corr_exit_at {d : Correction.D} {pc : Nat} (hev : Correction.Ev p L g d ⟨pc, .exit⟩) :
    ∃ l, d.site = .exit l := by
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [Correction.Ev] at hev
  case exit l => exact ⟨l, rfl⟩
  all_goals exfalso
  all_goals (try simp only [Epilogue.Ev] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals first
    | cases ‹Kind.exit = _›
    | simp [Correction.Site.toE] at *

private theorem late_epi {s : Correction.Site} (h : Progress.Cr.late s = false) :
    (CorrWarp.epi s).late = false := by
  cases s <;> exact h

/-- **A correction lane of a CTA with a tile exits** after its P-full arrivals. -/
theorem corr_exit_rounds (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    (hT : ∃ R bal, Epilogue.Picked p L g R bal) (q : Fin 4) {pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ R, CorrRounds p L g R ∧ R + 2 ≤ arrivals (obj L g (corrO q)) ((X.tr g).take k) := by
  rcases corr_counts_nonvote hp hX hFw hw hw1 he (fun f h => by cases h) (fun _ _ => nofun) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, hF, hev, hc⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  obtain ⟨l, hs⟩ := corr_exit_at hev
  cases l with
  | false =>
    obtain ⟨rv, -, -, hFE, -⟩ := hF
    exact (noPicked_of_exit hFE (by simp only [hs, CorrWarp.epi]) hT).elim
  | true =>
    refine corr_late_rounds hp hX hFw hw hw1 q ?_
    have h1 := hQ.cnt (.arrive (216)) (by simp)
    have hchk := site_ok d.site
    simp only [siteChk, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hchk
    have h2 := (hchk q (by fin_cases q <;> simp)).2.resolve_left (by
      rw [hs]; simp [Progress.Cr.late])
    rw [corr_arrivals, hc, h1, passed, h2, rnd_tab.1]
    omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : 8 ≤ Prologue.warpIndex L g)
  (hw1 : Prologue.warpIndex L g ≤ 11) (hT : ∃ R bal, Epilogue.Picked p L g R bal) (q : Fin 4)
include hp hX hFw hub hg hw hw1 hT

set_option maxHeartbeats 1000000 in
/-- **A state of a correction lane** of a CTA with a tile. -/
theorem corr_state {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    Progress.time p L g σ + 1 <
        Progress.clk p (arrivals (obj L g (corrO q)) ((X.tr g).take k) + corrE q) (tileB q) ∨
      ∃ R, CorrRounds p L g R ∧
        R + 2 ≤ arrivals (obj L g (corrO q)) ((X.tr g).take k) := by
  have hprime := Progress.primeBase_le_clk p
    (arrivals (obj L g (corrO q)) ((X.tr g).take k) + corrE q) (tileB q)
  have hsp := Progress.scanBase_le_primeBase p
  have h4 : Progress.scanBase + 4 ≤ Progress.primeBase p := by unfold Progress.primeBase; omega
  have hG := (corr_good hp hX hFw ⟨hw, hw1⟩ hg k).2 σ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · left
    have hx : ∀ r, s.site ≠ .enter r := by
      intro r he
      have h1 := hG.1
      simp only [StartAt, he] at h1
    have h1 := Progress.startTime_lt hx
    simp only [Progress.time]
    omega
  cases i with
  | correction =>
    have hub0 : n .ub = 0 := by
      by_contra h
      obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
      cases kind <;> simp [cls] at hk
      exact hub ⟨(g, j), pc, _, hf⟩
    obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, hF⟩ := hG hub0
    have hc := fun c => (count hσ (.corr c))
    have hA : arrivals (obj L g (corrO q)) ((X.tr g).take k) =
        CorrWarp.rc n (.arrive (corrO q)) := by
      rw [corr_arrivals, hc]
    have h96 := hQ.cnt (.arrive (corrO q)) (by simp)
    obtain ⟨t2, -⟩ := rnd_tab.2 q
    have t3 := rnd_tab.1
    simp only [passed, t2, Nat.mul_one] at h96
    have hchk := site_ok d.scheduler.site
    simp only [siteChk, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hchk
    obtain ⟨hpl, hlt⟩ := hchk q (by fin_cases q <;> simp)
    cases hp' : Progress.Cr.part d.scheduler.site with
    | some x =>
      left
      obtain ⟨st, past⟩ := x
      rw [hp'] at hpl
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hpl
      have hnb := hQ.cnt (.nb st) (by simp)
      simp only [passed, nb_tab st, Nat.mul_one] at hnb
      have hn : n (.corr (.nb st)) = CorrWarp.rc n (.nb st) := rfl
      obtain ⟨⟨⟨h1, h2⟩, h4⟩, h3⟩ := hpl
      have hs : Progress.Cr.slot p st past n +
          (if (ptsOf (.nb st)).countP (before d.scheduler.site) <
          (ptsOf (.arrive (corrO q))).countP (before d.scheduler.site) + corrE q +
          if past then 1 else 0
          then 1 else 0) ≤ CorrWarp.rc n (.arrive (corrO q)) + corrE q := by
        unfold Progress.Cr.slot Progress.slotOf
        rw [hn, hnb, h96]
        cases past <;>
          simp only [Bool.false_eq_true, ite_true, ite_false, forall_const] at h1 h4 ⊢ <;>
          split <;> omega
      rw [hA]
      simp only [Progress.time, Progress.roleTime, Progress.Cr.time, hp']
      rcases h3 with h3 | h3
      · simp only [h3, ite_true] at hs
        have := Nat.mul_le_mul_left Progress.span hs
        simp only [Progress.clk] at this ⊢
        rw [Nat.mul_add] at this
        omega
      · have := Nat.mul_le_mul_left Progress.span (le_trans (Nat.le_add_right _ _) hs)
        simp only [Progress.clk] at this ⊢
        omega
    | none =>
      by_cases hlate : Progress.Cr.late d.scheduler.site = true
      · right
        refine corr_late_rounds hp hX hFw hw hw1 q ?_
        have h1 := hQ.cnt (.arrive (216)) (by simp)
        have h2 := hlt.resolve_left (by simp [hlate])
        have h3 : arrivals (obj L g 216) ((X.tr g).take k) =
            CorrWarp.rc n (.arrive (216)) := by
          rw [corr_arrivals, hc]
        have h4 : CorrWarp.rc n (.arrive (216)) = _ := h1
        rw [h3, h4, passed, h2, t3]
        omega
      · left
        have hl : Progress.Cr.late d.scheduler.site = false := by simpa using hlate
        have hend : ∀ o, Progress.Cr.endOff d.scheduler.site ≠ some (true, o) := by
          intro o ho
          apply hlate
          revert ho
          cases d.scheduler.site <;> simp only [Progress.Cr.endOff, Progress.Cr.late,
            Option.some.injEq,
            Prod.mk.injEq, reduceCtorEq, false_implies]
          all_goals exact fun h => h.1
        obtain ⟨hr, ht⟩ := (Progress.Cr.part_none d.scheduler.site).mp hp'
        simp only [Progress.time, Progress.roleTime, Progress.Cr.time, hp']
        split
        · rename_i l o ho
          exfalso
          cases l with
          | true => exact hend o ho
          | false =>
            obtain ⟨rv, -, -, hFE, -⟩ := hF
            refine noPicked_of_exit hFE ?_ hT
            revert ho
            cases hs : d.scheduler.site <;> simp [Progress.Cr.endOff, hs, CorrWarp.epi]
            all_goals exact fun h _ => h
        split
        · omega
        split
        · omega
        have h1 := Progress.corr_coll hp hG hub0 hr ht hl
        unfold Progress.collCount at h1
        have h2 : Progress.Out.ballots (Progress.Cr.toE d.scheduler.site) ≤ 1 := by
          unfold Progress.Out.ballots; split <;> omega
        have h3 := Progress.pass_lt_prime (p := p)
          (c := n .shfl + Progress.Out.ballots (Progress.Cr.toE d.scheduler.site))
          (by omega) (Progress.Out.coll (Progress.Cr.toE d.scheduler.site))
        omega
  | _ => exact hG.elim

/-- **A correction lane with at most `v` arrivals**, `v` at most the rescale rounds plus one, is
before its bound of the time table. -/
theorem corr_early {R v : Nat} (hR : CorrRounds p L g R) (hv : v ≤ R + 1)
    (ha : arrivals (obj L g (corrO q)) (X.tr g) ≤ v) :
    Sched.threadTime (Progress.timed p L) X g < Progress.clk p (v + corrE q) (tileB q) := by
  have key : ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ + 1 < Progress.clk p (v + corrE q) (tileB q) := by
    intro k σ hσ
    have hle : arrivals (obj L g (corrO q)) ((X.tr g).take k) ≤ v :=
      le_trans (List.take_sublist _ _).countP_le ha
    rcases corr_state hp hX hFw hub hg hw hw1 hT q hσ with h | ⟨R', hR', h⟩
    · refine h.trans_le ?_
      have := Nat.mul_le_mul_left Progress.span (Nat.add_le_add_right hle (corrE q))
      unfold Progress.clk
      omega
    · have := hR'.unique hR
      omega
  have h0 : 0 < Progress.clk p (v + corrE q) (tileB q) := by
    have := Progress.primeBase_le_clk p (v + corrE q) (tileB q)
    omega
  unfold Sched.threadTime
  split
  · rename_i d hd; exact Nat.lt_of_succ_lt (key _ d hd)
  · exact h0
  · split
    · rename_i d hd; exact key _ d hd
    · exact h0

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
