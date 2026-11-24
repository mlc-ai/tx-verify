-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Kernels.TmlFa4Fwd.Proof.SmWarp.P2Count
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A softmax lane short of a round is early

`soft_state`: at every state of a softmax lane of a CTA with a tile, either the lane is before the
slot after its P-full arrivals (`Progress.clk p (A + 1) 0`, `A` the arrivals on offset 96 so far),
or it is past the rounds and `A` is the tile's rounds. `soft_early`: a lane with at most `v`
arrivals, `v` less than the rounds, is before slot `v + 1`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before inBias inPlain allSites
  mem_allSites)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem SoftRounds.unique {T T' : Nat} (h : SoftRounds p L g T) (h' : SoftRounds p L g T') :
    T = T' := by
  obtain ⟨R, b, hP, rfl⟩ := h
  obtain ⟨R', b', hP', rfl⟩ := h'
  obtain ⟨rfl, rfl⟩ := hP.unique hP'
  rfl

/-- Points per round. -/
private theorem rnd_tab (b : Bool) :
    (ptsOf b (.acquire 80)).countP inBias = 1 ∧ (ptsOf b (.acquire 80)).countP inPlain = 1 ∧
      (ptsOf b (.arrive 96)).countP inBias = 1 ∧ (ptsOf b (.arrive 96)).countP inPlain = 1 ∧
      (ptsOf b .nb).countP inBias = 1 ∧ (ptsOf b .nb).countP inPlain = 1 := by
  cases b <;> decide +kernel

/-- In a round the slot is at most the P-full arrivals, and the offset is inside the slot; past the
rounds one P-full arrival and one S-full poll are beside the repeated rounds', and two named-barrier
arrivals. -/
private def siteChk (b : Bool) (s : Softmax.Site) : Bool :=
  ([0, 1].all fun st => match Progress.Sm.place st s with
    | some (bd, past, o) => decide ((ptsOf b (.acquire 80)).countP (before s) + midP2 s ≤
        (ptsOf b (.arrive 96)).countP (before s) + if past then 1 else 0) &&
        decide (bd + o + 2 < Progress.span)
    | none => true) &&
  decide (midP2 s ≤ 1) &&
  (!Progress.Sm.late s || (decide (midP2 s = 0) &&
    decide ((ptsOf b (.acquire 80)).countP (before s) = 1) &&
    decide ((ptsOf b (.arrive 96)).countP (before s) = 1) &&
    decide ((ptsOf b .nb).countP (before s) = 2)))

private theorem site_chk : [false, true].all (fun b => allSites.all (siteChk b)) = true := by
  decide +kernel

private theorem site_ok (b : Bool) (s : Softmax.Site) : siteChk b s = true :=
  List.all_eq_true.mp (List.all_eq_true.mp site_chk b (by cases b <;> simp)) s (mem_allSites s)

theorem clk_mono {a b : Nat} (h : a ≤ b) : Progress.clk p a 0 ≤ Progress.clk p b 0 := by
  have := Nat.mul_le_mul_left Progress.span h
  unfold Progress.clk
  omega

private theorem late_epi {s : Softmax.Site} (h : Progress.Sm.late s = false) :
    (SmWarp.epi s).late = false := by
  cases s <;> exact h

/-- A lane with one more named-barrier arrival than its `A` S-full polls is past the tile's `A`
rounds. -/
theorem soft_late_rounds (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {A : Nat}
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId (Prologue.warpIndex L g + 3)) = A + 1)
    (hpoll : okPolls (sobj L g 80) ((X.tr g).take k) = A) : SoftRounds p L g A := by
  obtain ⟨j, ⟨pc, kd⟩, hj, hget, hb', hcj⟩ := exists_nthEv (X := X) (g := g) (k := k)
    (p := Execution.isBarId (Prologue.warpIndex L g + 3)) (n := A) (by omega)
  cases kd <;> simp [Execution.isBarId] at hb'
  subst hb'
  rcases soft_bar hp hX hFw hw hget with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, -, -, h0⟩
  · omega
  · omega
  · omega
  · rw [hcj] at h0
    rcases h0 with h0 | ⟨-, h0⟩
    · exfalso
      have h1 := countP_take_mono (okPoll (sobj L g 80)) (X.tr g) hj.le
      unfold okPolls at h0 hpoll
      omega
    · exact h0

/-- **A softmax lane of a CTA with a tile exits** after the tile's rounds of P-full arrivals. -/
theorem soft_exit_rounds (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8)
    (hT : ∃ R bal, Epilogue.Picked p L g R bal) {pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    SoftRounds p L g (arrivals (sobj L g 96) ((X.tr g).take k)) ∧
      ((X.tr g).take k).countP (isP2 L g) = arrivals (sobj L g 96) ((X.tr g).take k) := by
  have hub : ∀ f, (⟨pc, .exit⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · exfalso
    have hx : exit L g s = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR.2 h0
  obtain ⟨l, hs⟩ := soft_exit_site' hev.1
  cases l with
  | false => exact (noPicked_of_exit hF.1 (by simp only [hs, SmWarp.epi]) hT).elim
  | true =>
    have hA : arrivals (sobj L g 96) ((X.tr g).take k) = c (.arrive 96) := by
      rw [sobj, soft_arrivals hw (by decide), count hσ, hLk _ rfl]
    have h96 := hQ.cnt (.arrive 96) rfl
    have h80 := hQ.cnt (.acquire 80) rfl
    have hnb := hQ.cnt .nb rfl
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := rnd_tab (Softmax.lz L g)
    simp only [passed, t1, t2, t3, t4, t5, t6] at h96 h80 hnb
    have hchk := site_ok (Softmax.lz L g) d.scheduler.site
    simp only [siteChk, Bool.and_eq_true] at hchk
    obtain ⟨-, hlt⟩ := hchk
    have hl : Progress.Sm.late d.scheduler.site = true := by rw [hs]; rfl
    simp only [hl, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨⟨⟨l0, l1⟩, l2⟩, l3⟩ := hlt
    rw [l1] at h80; rw [l2] at h96; rw [l3] at hnb
    have hmid : ((X.tr g).take k).countP (isP2 L g) + midP2 d.scheduler.site = c (.arrive 96) := by
      rw [hLk _ rfl]
      exact p2_count hp hX hFw (Frame.lt_of_get hX he) k _ (Frame.noUbBefore_of_get hX he) hσ h0
    rw [hA]
    refine ⟨soft_late_rounds hp hX hFw hw (k := k) ?_ ?_, by omega⟩
    · rw [soft_isBarId hw, count hσ, ← hLk _ rfl, hnb, h96]; omega
    · rw [sobj, soft_okPolls hw, count hσ, ← hLk _ rfl, h80, h96]

/-- On a lane that wins every election it makes, the counted events are its second P arrivals. -/
theorem isP2_winner (hw : Prologue.warpIndex L g < 8)
    (hwin : ∀ j pc mk inst ld, X.get (g, j) = some ⟨pc, .elect mk inst ld⟩ → ld = laneOf L g) :
    (X.tr g).countP (isP2 L g) = arrivals (sobj L g 112) (X.tr g) := by
  refine List.countP_congr fun e he => ?_
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hget : X.get (g, j) = some ((X.tr g)[j]) := List.getElem?_eq_getElem hj
  generalize (X.tr g)[j] = e at hget
  obtain ⟨pc, kd⟩ := e
  have hbl : Softmax.bl L g 112 = sobj L g 112 := soft_bl hw 112
  cases kd with
  | elect mk inst ld =>
    have := hwin j pc mk inst ld hget
    simp [isP2, this, arrivesOn, sourceArrive]
  | arrive l tx c rel sc => simp [isP2, arrivesOn, sourceArrive, hbl]
  | _ => simp [isP2, arrivesOn, sourceArrive]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g < 8)
  (hT : ∃ R bal, Epilogue.Picked p L g R bal)
include hp hX hFw hub hg hw hT

set_option maxHeartbeats 1000000 in
/-- **A state of a softmax lane** of a CTA with a tile. -/
theorem soft_state {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ∃ μ, ((X.tr g).take k).countP (isP2 L g) + μ = arrivals (sobj L g 96) ((X.tr g).take k) ∧
      (Progress.time p L g σ + 1 <
          Progress.clk p (arrivals (sobj L g 96) ((X.tr g).take k) - μ + 1) 0 ∨
        (SoftRounds p L g (arrivals (sobj L g 96) ((X.tr g).take k)) ∧ μ = 0)) := by
  have hP2 := p2_count hp hX hFw hg k σ (by rintro j _ ⟨pc,_⟩ he f rfl; exact hub ⟨_,pc,f,he⟩) hσ
  have hJ := (goodR hp hX hFw hg k).2 σ hσ
  have hprime : ∀ x, Progress.primeBase p + 1024 ≤ Progress.clk p (x + 1) 0 := fun x =>
    Progress.primeBase_le_clk p _ _
  have hsp := Progress.scanBase_le_primeBase p
  have h4 : Progress.scanBase + 4 ≤ Progress.primeBase p := by unfold Progress.primeBase; omega
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · have hA : arrivals (sobj L g 96) ((X.tr g).take k) = 0 := by
      rw [sobj, soft_arrivals hw (by decide), count hσ]; exact hP2.2
    refine ⟨0, by rw [hA, hP2.1], .inl ?_⟩
    have hS := (SmWarp.good hp hX hw hg rfl k).2 _ hσ
    have hx : ∀ r, s.site ≠ .enter r := by
      intro r he
      have h1 := hS.1
      simp only [SmWarp.StartW, StartAt0, StartAt, he, ite_self] at h1
    have h1 := Progress.startTime_lt hx
    have h2 := hprime (arrivals (sobj L g 96) ((X.tr g).take k) - 0)
    simp only [Progress.time]
    omega
  cases i with
  | softmax =>
    have hub0 : n .ub = 0 := by
      by_contra h
      obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
      cases kind <;> simp [cls] at hk
      exact hub ⟨(g, j), pc, _, hf⟩
    obtain ⟨-, -, hR⟩ := JR.softmax hJ
    obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR hub0
    have hA : arrivals (sobj L g 96) ((X.tr g).take k) = c (.arrive 96) := by
      rw [sobj, soft_arrivals hw (by decide), count hσ, hLk _ rfl]
    have h96 := hQ.cnt (.arrive 96) rfl
    have h80 := hQ.cnt (.acquire 80) rfl
    have hnb := hQ.cnt .nb rfl
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := rnd_tab (Softmax.lz L g)
    simp only [passed, t1, t2, t3, t4, t5, t6] at h96 h80 hnb
    have hn80 : n (.soft (.acquire 80)) = c (.acquire 80) := (hLk _ rfl).symm
    have hchk := site_ok (Softmax.lz L g) d.scheduler.site
    simp only [siteChk, Bool.and_eq_true] at hchk
    obtain ⟨⟨hpl, hm1⟩, hlt⟩ := hchk
    have hmid : ((X.tr g).take k).countP (isP2 L g) + midP2 d.scheduler.site = c (.arrive 96) := by
      rw [hLk _ rfl]; exact hP2 hub0
    rw [hA]
    refine ⟨midP2 d.scheduler.site, hmid, ?_⟩
    cases hp' : Progress.Sm.place (Progress.Sm.stage L g) d.scheduler.site with
    | some x =>
      left
      obtain ⟨bd, past, o⟩ := x
      have hst : Progress.Sm.stage L g ∈ [0, 1] := by
        unfold Progress.Sm.stage; split <;> simp
      have h1 := List.all_eq_true.mp hpl _ hst
      rw [hp'] at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      have hs : Progress.slotOf p (n (.soft (.acquire 80)) - if past then 1 else 0) <
          c (.arrive 96) - midP2 d.scheduler.site + 1 := by
        unfold Progress.slotOf
        rw [hn80]
        omega
      have hso : Progress.Sm.subOff d ≤ 1 := by
        unfold Progress.Sm.subOff; split <;> omega
      have := Progress.clk_lt_of_slot (p := p) (o := bd + o + Progress.Sm.subOff d + 1) (o' := 0)
        hs (by omega)
      simp only [Progress.time, Progress.roleTime, Progress.Sm.time, hp']
      simp only [Progress.clk] at this ⊢
      omega
    | none =>
      have hb := hprime (c (.arrive 96) - midP2 d.scheduler.site)
      by_cases hlate : Progress.Sm.late d.scheduler.site = true
      · right
        simp only [hlate, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
          at hlt
        obtain ⟨⟨⟨l0, l1⟩, l2⟩, l3⟩ := hlt
        refine ⟨?_, l0⟩
        rw [l1] at h80; rw [l2] at h96; rw [l3] at hnb
        refine soft_late_rounds hp hX hFw hw (k := k) ?_ ?_
        · rw [soft_isBarId hw, count hσ, ← hLk _ rfl, hnb, h96]; omega
        · rw [sobj, soft_okPolls hw, count hσ, ← hLk _ rfl, h80, h96]
      · left
        have hend : ∀ o, Progress.Sm.endOff d.scheduler.site ≠ some (true, o) := by
          intro o ho
          apply hlate
          revert ho
          cases d.scheduler.site <;> simp only [Progress.Sm.endOff, Progress.Sm.late,
            Option.some.injEq,
            Prod.mk.injEq, reduceCtorEq, false_implies]
          all_goals exact fun h => h.1
        obtain ⟨hFE, -⟩ := hF
        simp only [Progress.time, Progress.roleTime, Progress.Sm.time, hp']
        split
        · rename_i o ho
          have : o ≤ 3 := by
            revert ho
            cases d.scheduler.site <;> simp [Progress.Sm.pre] <;> omega
          omega
        split
        · rename_i l o ho
          exfalso
          cases l with
          | true => exact hend o ho
          | false =>
            refine noPicked_of_exit hFE ?_ hT
            revert ho
            cases hs : d.scheduler.site <;> simp [Progress.Sm.endOff, hs, SmWarp.epi]
            all_goals exact fun h _ => h
        split
        · omega
        split
        · omega
        have hl : Progress.Sm.late d.scheduler.site = false := by simpa using hlate
        have h1 := Epilogue.fits_coll_le hp hFE (late_epi hl)
        have h2 : Progress.Out.ballots (Progress.Sm.toE d.scheduler.site) ≤ 1 := by
          unfold Progress.Out.ballots; split <;> omega
        have h3 := Progress.pass_lt_prime (p := p)
          (c := n .shfl + Progress.Out.ballots (Progress.Sm.toE d.scheduler.site))
          (by unfold Progress.cmax; omega) (Progress.Out.coll (Progress.Sm.toE d.scheduler.site))
        omega
  | correction => have := (JR.correction hJ (by omega)).1; omega
  | mma => have := (JR.mma hJ).1; omega
  | epilogue => have := (JR.epilogue hJ).1; omega
  | loader b => have := (JR.loader hJ).1; omega
  | stub r => exact (JR.not_stub hJ).elim

/-- **A softmax lane with at most `v` P-full arrivals**, `v` less than the tile's rounds, is before
slot `v + 1`. -/
theorem soft_early {T v : Nat} (hTR : SoftRounds p L g T) (hv : v < T)
    (ha : arrivals (sobj L g 96) (X.tr g) ≤ v) :
    Sched.threadTime (Progress.timed p L) X g < Progress.clk p (v + 1) 0 := by
  have key : ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ + 1 < Progress.clk p (v + 1) 0 := by
    intro k σ hσ
    have hle : arrivals (sobj L g 96) ((X.tr g).take k) ≤ v :=
      le_trans (List.take_sublist _ _).countP_le ha
    obtain ⟨μ, -, h | ⟨h, -⟩⟩ := soft_state hp hX hFw hub hg hw hT hσ
    · refine h.trans_le ?_
      exact clk_mono (by omega)
    · have := h.unique hTR
      omega
  have h0 : 0 < Progress.clk p (v + 1) 0 := by unfold Progress.clk Progress.span; omega
  unfold Sched.threadTime
  split
  · rename_i d hd; exact Nat.lt_of_succ_lt (key _ d hd)
  · exact h0
  · split
    · rename_i d hd; exact key _ d hd
    · exact h0

/-- **A softmax lane with at most `v` second P arrivals and lost elections**, `v` less than the
tile's rounds, is before slot `v + 1`. -/
theorem soft_early2 {T v : Nat} (hTR : SoftRounds p L g T) (hv : v < T)
    (ha : (X.tr g).countP (isP2 L g) ≤ v) :
    Sched.threadTime (Progress.timed p L) X g < Progress.clk p (v + 1) 0 := by
  have key : ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ + 1 < Progress.clk p (v + 1) 0 := by
    intro k σ hσ
    have hle : ((X.tr g).take k).countP (isP2 L g) ≤ v :=
      le_trans (List.take_sublist _ _).countP_le ha
    obtain ⟨μ, hμ, h | ⟨h, h0⟩⟩ := soft_state hp hX hFw hub hg hw hT hσ
    · exact h.trans_le (clk_mono (by omega))
    · have := h.unique hTR
      omega
  have h0 : 0 < Progress.clk p (v + 1) 0 := by unfold Progress.clk Progress.span; omega
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
