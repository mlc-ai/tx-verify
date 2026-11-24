-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.PollLag
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageBar
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Softmax.Align
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax lanes' bias polls and releases in the time table

`soft_bias_at`: a softmax lane at a Bias-full poll has made `u` polls of it, at most the tile's
biased rounds after the first, and is in slot `u`. `soft_free_early`: lane 0 of a softmax warp with
at most `v` releases of the bias empty barrier, at most the biased rounds after the first, is before
the end of the score part of slot `v`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before inBias inPlain allSites
  mem_allSites)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The tile's biased rounds at a site of the rounds' region. -/
theorem stage_rounds_at {d : Softmax.D} {ns nv : Nat} (hF : SmWarp.SFits p L g d ns nv)
    (hep : SmWarp.epi d.site = .ready 0) (huk : d.site.hasUk = true) :
    StageRounds p L g (Softmax.nB p L g d.v).toNat := by
  obtain ⟨hFE, hu⟩ := hF
  simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
  obtain ⟨R, bal, hC, h0, h1⟩ := hFE
  refine ⟨R, bal, hC.1, ?_⟩
  obtain ⟨-, ht, hgx, hcur, hbal, hpv, hnt, -, -⟩ := hC
  have hu := hu huk
  have ht' : d.v.sc.tot = _ := ht
  have hgx' : d.v.sc.gx = _ := hgx
  have hcur' : d.v.sc.cur = _ := hcur
  have hbal' : d.v.sc.bal = _ := hbal
  have hpv' : d.v.sc.pv = _ := hpv
  have hnt' : d.v.sc.nt = _ := hnt
  have hch : Epilogue.chosen d.v.sc =
      Epilogue.chosen (Epilogue.chosenD p (g / L.block) R bal) := by
    simp only [Epilogue.chosen, Epilogue.chosenD, hbal', hgx']
  have h0' : d.v.sc.c0 = Epilogue.qv p (Epilogue.chosen d.v.sc) := h0
  have h1' : d.v.sc.c1 = Epilogue.qv p (Epilogue.addi (Epilogue.chosen d.v.sc) 1) := h1
  simp only [Softmax.nB, Softmax.r169, Softmax.r299, Softmax.r166,
    Softmax.r168, Softmax.r165, Softmax.r1808, Softmax.rowOff, Mma.coords, softRef, hu, h0', h1',
    hch, ht', hcur', hpv', hnt', Epilogue.chosenD, Mma.ukv]

/-- The bias poll's points. -/
private theorem wb_tab : ∀ b : Bool, ∀ r : Bool,
    SmWarp.epi (.wb r) = .ready 0 ∧ (Softmax.Site.wb r).hasUk = true ∧
    (ptsOf b (.acquire 320)).countP (before (.wb r)) = (if r then 1 else 0) ∧
    (ptsOf b (.acquire 320)).countP inBias = 1 ∧ (ptsOf b (.acquire 320)).countP inPlain = 0 := by
  decide +kernel

private theorem wb_reg : Softmax.preR (.wb false) = true ∧
    inBias (Softmax.Site.wb true).pos = true := by decide +kernel

/-- The points of the releases, against the round's slot and offset, on lane 0. -/
private def relChk (s : Softmax.Site) : Bool :=
  let a := (ptsOf true (.arrive 336)).countP (before s)
  let q := (ptsOf true (.acquire 80)).countP (before s)
  (((inPlain s.pos || Softmax.finR s) && decide (a = 1)) ||
  ((Softmax.preR s || inBias s.pos) && ([0, 1].all fun st => match Progress.Sm.place st s with
    | some (bd, past, o) => decide (q - (if past then 1 else 0) < a ∧ bd + o + 3 < Progress.span ∨
        q - (if past then 1 else 0) = a ∧ bd + o + 2 < Progress.bandS st + 41)
    | none => true)) ||
  ([0, 1].all fun st => (Progress.Sm.place st s).isNone)) &&
  (!Progress.Sm.late s || (decide (a = 1) && decide ((ptsOf true .sb).countP (before s) = 1) &&
    decide (q = 1) && decide ((ptsOf true .nb).countP (before s) = 2)))

private theorem rel_chk : allSites.all relChk = true := by decide +kernel

private theorem rel_ok (s : Softmax.Site) : relChk s = true :=
  List.all_eq_true.mp rel_chk s (mem_allSites s)

private theorem rel_rnd : (ptsOf true (.arrive 336)).countP inBias = 1 ∧
    (ptsOf true (.arrive 336)).countP inPlain = 0 ∧
    (ptsOf true (.acquire 80)).countP inBias = 1 ∧
    (ptsOf true (.acquire 80)).countP inPlain = 1 ∧
    (ptsOf true .sb).countP inBias = 1 ∧ (ptsOf true .sb).countP inPlain = 0 ∧
    (ptsOf true .nb).countP inBias = 1 ∧ (ptsOf true .nb).countP inPlain = 1 := by
  decide +kernel

private theorem stage_id' {h : Nat} (hw : Prologue.warpIndex L h < 8) :
    (if Softmax.stg L h then 12 else 11) = stageId (Prologue.warpIndex L h / 4) := by
  have hs : Softmax.stg L h = decide (4 ≤ Prologue.warpIndex L h) := by
    have key : ∀ w < 8, Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 = decide (4 ≤ w) := by decide
    exact key _ hw
  rw [hs]
  unfold stageId
  by_cases h4 : 4 ≤ Prologue.warpIndex L h
  · simp only [h4, decide_true, ↓reduceIte]; omega
  · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

private theorem soft_isStage' {h k : Nat} (hw : Prologue.warpIndex L h < 8) :
    ((X.tr h).take k).countP (Execution.isBarId (stageId (Prologue.warpIndex L h / 4))) =
      ((X.tr h).take k).countP (cls L h (.soft .sb)) := by
  refine List.countP_congr fun e _ => ?_
  have hw' : h % L.block / 32 < 8 := hw
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [Execution.isBarId, cls, Softmax.cls, Softmax.Cnt.pointed, hw', stage_id' hw]

/-- Lane 0 of a warp is the lane the code's `%tid & 31` test selects. -/
theorem lz_of_lane (hp : Pre p L m) {h : Nat} (hl : laneOf L h = 0) : Softmax.lz L h = true := by
  have hm : (h % L.block) % 32 = 0 := hl
  have hlt := Nat.mod_lt h (show 0 < L.block by rw [hp.block]; decide)
  rw [hp.block] at hlt
  have key : ∀ a < 512, a % 32 = 0 → (!Epilogue.scmpi .ne .b
      (Epilogue.andi (BitVec.ofNat 64 a) 31) 0) = true := by decide +kernel
  unfold Softmax.lz
  rw [Softmax.tidW_eq hp]
  exact key _ (by rw [hp.block]; exact hlt) hm

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads)
include hp hX hFw hub hg

/-- **A softmax lane at a Bias-full poll.** -/
theorem soft_bias_at {d : Softmax.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.softmax, d⟩, n)))
    {r : Bool} (hs : d.scheduler.site = .wb r) :
    ∃ B u T, StageRounds p L g B ∧ u ≤ B ∧ SoftRounds p L g T ∧ u < T ∧
      okPolls (sobj L g 320) (X.tr g) = u ∧ n (.soft (.acquire 80)) = u + 1 := by
  obtain ⟨hw, c, rb, rp, hQ, hF, hc, hn⟩ := soft_end hp hX hFw hub hg hσ
  obtain ⟨T, u, hT, hu, hok, hn80⟩ := soft_poll_at hp hX hFw hub hg hσ
    (show midPoll d.scheduler.site = some (1, 0) by rw [hs]; rfl)
  rw [hs, soft_wb_off, Nat.add_zero] at hok
  obtain ⟨t1, t2, t3, t4, t5⟩ := wb_tab (Softmax.lz L g) r
  have hB := stage_rounds_at hF (by rw [hs]; exact t1) (by rw [hs]; exact t2)
  refine ⟨_, u, T, hB, ?_, hT, hu, hok, hn80⟩
  have e := hQ.cnt (.acquire 320) rfl
  rw [hs, passed, t3, t4, t5] at e
  have hok' : okPolls (sobj L g 320) (X.tr g) = c (.acquire 320) := by
    have := soft_okPolls (X := X) (k := (X.tr g).length) hw 320
    rw [List.take_length] at this
    rw [sobj, this, hc _ rfl]
  have hlt : r = true → (rb : Int) < Softmax.nB p L g d.scheduler.v := by
    rintro rfl
    exact (hQ.bias (by rw [hs]; exact wb_reg.2)).2.2.1
  have hr0 : r = false → rb = 0 ∧ rp = 0 := by
    rintro rfl
    exact hQ.pre (by rw [hs]; exact wb_reg.1)
  generalize Softmax.nB p L g d.scheduler.v = N at hlt ⊢
  clear hc hn hQ hF hB hσ
  cases r
  · obtain ⟨rfl, rfl⟩ := hr0 rfl
    simp only [Bool.false_eq_true, ite_false] at e; omega
  · have := hlt rfl
    simp only [ite_true] at e; omega

omit hub hg in
/-- **A lane with one more named-barrier arrival than its S-full polls** has made one more
stage-barrier event than the tile's biased rounds. -/
theorem soft_late_stage {k A : Nat} (hw : Prologue.warpIndex L g < 8)
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId (Prologue.warpIndex L g + 3)) = A + 1)
    (hpoll : okPolls (sobj L g 80) ((X.tr g).take k) = A) :
    ∃ B, StageRounds p L g B ∧
      B + 1 ≤ ((X.tr g).take k).countP
        (Execution.isBarId (stageId (Prologue.warpIndex L g / 4))) := by
  obtain ⟨j, ⟨pc, kd⟩, hj, hget, hb', hcj⟩ := exists_nthEv (X := X) (g := g) (k := k)
    (p := Execution.isBarId (Prologue.warpIndex L g + 3)) (n := A) (by omega)
  cases kd <;> simp [Execution.isBarId] at hb'
  subst hb'
  have h1 := countP_take_mono (okPoll (sobj L g 80)) (X.tr g) hj.le
  have hno : okPolls (sobj L g 80) ((X.tr g).take j) =
      ((X.tr g).take j).countP (Execution.isBarId (Prologue.warpIndex L g + 3)) := by
    rcases soft_bar hp hX hFw hw hget with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, -, -, h0⟩
    · omega
    · omega
    · omega
    · rw [hcj] at h0 ⊢
      rcases h0 with h0 | ⟨h0, -⟩
      · exfalso
        unfold okPolls at h0 hpoll
        omega
      · exact h0
  obtain ⟨B, hB, he⟩ := soft_fin_stage hp hX hFw hw hget hno
  refine ⟨B, hB, ?_⟩
  rw [← he]
  exact countP_take_mono _ (X.tr g) hj.le

set_option maxHeartbeats 1000000 in
/-- **A state of lane 0 of a softmax warp** of a CTA with a tile: in the score part of the slot of
its releases of the bias empty barrier at the latest, or past the biased rounds. -/
theorem soft_free_state (hw : Prologue.warpIndex L g < 8) (hlz : Softmax.lz L g = true)
    (hT : ∃ R bal, Epilogue.Picked p L g R bal) {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    Progress.time p L g σ + 1 < Progress.clk p (arrivals (sobj L g 336) ((X.tr g).take k))
      (Progress.bandS (Progress.Sm.stage L g) + 41) ∨
    ∃ B, StageRounds p L g B ∧ B < arrivals (sobj L g 336) ((X.tr g).take k) := by
  have hJ := (goodR hp hX hFw hg k).2 σ hσ
  generalize hA : arrivals (sobj L g 336) ((X.tr g).take k) = A
  have hprime : Progress.primeBase p + 1024 ≤
      Progress.clk p A (Progress.bandS (Progress.Sm.stage L g) + 41) := by
    unfold Progress.clk Progress.pipeBase; omega
  have hsp := Progress.scanBase_le_primeBase p
  have h4 : Progress.scanBase + 4 ≤ Progress.primeBase p := by unfold Progress.primeBase; omega
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · left
    have hS := (SmWarp.good hp hX hw hg rfl k).2 _ hσ
    have hx : ∀ r, s.site ≠ .enter r := by
      intro r he
      have h1 := hS.1
      simp only [SmWarp.StartW, StartAt0, StartAt, he, ite_self] at h1
    have h1 := Progress.startTime_lt hx
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
    have hA' : A = c (.arrive 336) := by
      rw [← hA, sobj, soft_arrivals hw (by decide), count hσ, hLk _ rfl]
    have h336 := hQ.cnt (.arrive 336) rfl
    have h80 := hQ.cnt (.acquire 80) rfl
    have hsb := hQ.cnt .sb rfl
    have hnb := hQ.cnt .nb rfl
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := rel_rnd
    simp only [hlz, passed, t1, t2, t3, t4, t5, t6, t7, t8] at h336 h80 hsb hnb
    have hn80 : n (.soft (.acquire 80)) = c (.acquire 80) := (hLk _ rfl).symm
    have hchk := rel_ok d.scheduler.site
    simp only [relChk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨hpl, hlt⟩ := hchk
    have hst : Progress.Sm.stage L g ∈ [0, 1] := by
      unfold Progress.Sm.stage; split <;> simp
    -- past the rounds
    have hdone : ∀ {N : Int}, StageRounds p L g N.toNat → Softmax.Done rb N →
        (ptsOf true (.arrive 336)).countP (before d.scheduler.site) = 1 →
        ∃ B, StageRounds p L g B ∧ B < A := by
      intro N hN hd h1
      refine ⟨_, hN, ?_⟩
      rcases hd with h | ⟨rfl, h⟩ <;> omega
    cases hp' : Progress.Sm.place (Progress.Sm.stage L g) d.scheduler.site with
    | some x =>
      obtain ⟨bd, past, o⟩ := x
      rcases hpl with (⟨hreg, ha⟩ | ⟨hreg, hpl⟩) | hpl
      · right
        have hhas : SmWarp.epi d.scheduler.site = .ready 0 ∧ d.scheduler.site.hasUk = true := by
          have key : ∀ s ∈ allSites, (inPlain s.pos || Softmax.finR s) = true →
              SmWarp.epi s = .ready 0 ∧ s.hasUk = true := by decide +kernel
          exact key d.scheduler.site (mem_allSites _) (by simpa using hreg)
        have hN := stage_rounds_at hF hhas.1 hhas.2
        refine hdone hN ?_ ha
        rcases hreg with h | h
        · exact (hQ.plain h).2.2.2
        · exact (hQ.fin h).1
      · left
        have h1 := List.all_eq_true.mp hpl _ hst
        rw [hp'] at h1
        simp only [decide_eq_true_eq] at h1
        have hrp : rp = 0 := by
          rcases hreg with h | h
          · exact (hQ.pre h).2
          · exact (hQ.bias h).1
        have hso : Progress.Sm.subOff d ≤ 1 := by
          unfold Progress.Sm.subOff; split <;> omega
        simp only [Progress.time, Progress.roleTime, Progress.Sm.time, hp']
        rw [hn80]
        generalize Progress.Sm.subOff d = so at hso ⊢
        generalize Progress.bandS (Progress.Sm.stage L g) = bs at h1 ⊢
        generalize (ptsOf true (.arrive 336)).countP (before d.scheduler.site) = a at h336 h1
        generalize (ptsOf true (.acquire 80)).countP (before d.scheduler.site) = q at h80 h1
        clear hpl hQ hF hLk hJ
        have hs0 : c (.acquire 80) - (if past then 1 else 0) ≤
            q - (if past then 1 else 0) + rb := by
          split <;> omega
        generalize (if past then 1 else 0 : Nat) = pa at *
        rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hs : Progress.slotOf p (c (.acquire 80) - pa) < A := by
            unfold Progress.slotOf; omega
          have := Progress.clk_lt_of_slot (p := p) (o := bd + o + so + 1) (o' := bs + 41) hs
            (by omega)
          unfold Progress.clk at this ⊢
          omega
        · have hs : Progress.slotOf p (c (.acquire 80) - pa) ≤ A := by
            unfold Progress.slotOf; omega
          have := Nat.mul_le_mul_left Progress.span hs
          unfold Progress.clk
          omega
      · exfalso
        have h1 := List.all_eq_true.mp hpl _ hst
        rw [hp'] at h1
        cases h1
    | none =>
      by_cases hlate : Progress.Sm.late d.scheduler.site = true
      · right
        simp only [hlate, Bool.not_true, Bool.false_eq_true, false_or] at hlt
        obtain ⟨⟨⟨l0, l1⟩, l2⟩, l3⟩ := hlt
        obtain ⟨B, hB, hle⟩ := soft_late_stage hp hX hFw (k := k)
          (A := okPolls (sobj L g 80) ((X.tr g).take k)) hw (by
            rw [soft_isBarId hw, count hσ, ← hLk _ rfl, hnb, sobj, soft_okPolls hw, count hσ,
              ← hLk _ rfl, h80, l3, l2]
            omega) rfl
        refine ⟨B, hB, ?_⟩
        rw [soft_isStage' hw, count hσ, ← hLk _ rfl, hsb, l1] at hle
        omega
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
        have hle : (SmWarp.epi d.scheduler.site).late = false := by
          revert hl
          cases d.scheduler.site <;> exact id
        have h1 := Epilogue.fits_coll_le hp hFE hle
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

omit hub hg in
/-- A softmax lane of a CTA with a tile exits past the drain's time. -/
theorem soft_exit_time (hw : Prologue.warpIndex L g < 8)
    (hT : ∃ R bal, Epilogue.Picked p L g R bal) {k pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ σ, Frame.stateAt (thread p L) X g k = some (some σ) ∧
      Progress.doneBase p ≤ Progress.time p L g σ := by
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
  obtain ⟨-, hF⟩ := hR.2 h0
  obtain ⟨l, hs⟩ := soft_exit_site' hev.1
  refine ⟨_, hσ, ?_⟩
  cases l with
  | false => exact (noPicked_of_exit hF.1 (by simp only [hs, SmWarp.epi]) hT).elim
  | true =>
    simp only [Progress.time, Progress.roleTime, Progress.Sm.time, hs, Progress.Sm.place,
      Progress.Sm.pre, Progress.Sm.endOff, Progress.endT, ite_true]
    omega

/-- **Lane 0 of a softmax warp with at most `v` releases**, at most the tile's biased rounds after
the first, has not exited and is in the score part of slot `v` at the latest. -/
theorem soft_free_early (hw : Prologue.warpIndex L g < 8) (hlz : Softmax.lz L g = true)
    {B v : Nat} (hB : StageRounds p L g B) (hv : v ≤ B)
    (hd : Progress.clk p v (Progress.bandS (Progress.Sm.stage L g) + 41) ≤ Progress.doneBase p)
    (ha : arrivals (sobj L g 336) (X.tr g) ≤ v) :
    (∀ k pc, X.get (g, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g <
        Progress.clk p v (Progress.bandS (Progress.Sm.stage L g) + 41) := by
  have hT := hB.picked rfl
  have key : ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ + 1 <
        Progress.clk p v (Progress.bandS (Progress.Sm.stage L g) + 41) := by
    intro k σ hσ
    have hle : arrivals (sobj L g 336) ((X.tr g).take k) ≤ v :=
      le_trans (List.take_sublist _ _).countP_le ha
    rcases soft_free_state hp hX hFw hub hg hw hlz hT hσ with h | ⟨B', hB', hlt⟩
    · have := Nat.mul_le_mul_left Progress.span hle
      unfold Progress.clk at h ⊢
      omega
    · have := hB.stage rfl hw hw rfl hB'
      omega
  refine ⟨fun k pc hx => ?_, ?_⟩
  · obtain ⟨σ, hσ, hle⟩ := soft_exit_time hp hX hFw hw hT hx
    have := key _ _ hσ
    omega
  · have h0 : 0 < Progress.clk p v (Progress.bandS (Progress.Sm.stage L g) + 41) := by
      unfold Progress.clk; omega
    unfold Sched.threadTime
    split
    · rename_i d hd; exact Nat.lt_of_succ_lt (key _ d hd)
    · exact h0
    · split
      · rename_i d hd; exact key _ d hd
      · exact h0

omit hub hg in
/-- **A softmax lane of a CTA with a tile exits** after a Bias-full poll of every biased round. -/
theorem soft_exit_bias (hw : Prologue.warpIndex L g < 8) {B k pc : Nat}
    (hB : StageRounds p L g B) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    B + 1 ≤ okPolls (sobj L g 320) ((X.tr g).take k) := by
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
  | false => exact (noPicked_of_exit hF.1 (by simp only [hs, SmWarp.epi]) (hB.picked rfl)).elim
  | true =>
    have h320 := hQ.cnt (.acquire 320) rfl
    have h80 := hQ.cnt (.acquire 80) rfl
    have hsb := hQ.cnt .sb rfl
    have hnb := hQ.cnt .nb rfl
    have t : ∀ b : Bool, ((ptsOf b (.acquire 320)).countP (before (.exit true)) = 1 ∧
        (ptsOf b (.acquire 80)).countP (before (.exit true)) = 1 ∧
        (ptsOf b .sb).countP (before (.exit true)) = 1 ∧
        (ptsOf b .nb).countP (before (.exit true)) = 2) ∧
        ((ptsOf b (.acquire 320)).countP inBias = 1 ∧
        (ptsOf b (.acquire 320)).countP inPlain = 0) ∧
        ((ptsOf b (.acquire 80)).countP inBias = 1 ∧ (ptsOf b (.acquire 80)).countP inPlain = 1) ∧
        ((ptsOf b .sb).countP inBias = 1 ∧ (ptsOf b .sb).countP inPlain = 0) ∧
        (ptsOf b .nb).countP inBias = 1 ∧ (ptsOf b .nb).countP inPlain = 1 := by decide +kernel
    obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2⟩, ⟨b3, b4⟩, ⟨b5, b6⟩, b7, b8⟩ := t (Softmax.lz L g)
    rw [hs] at h320 h80 hsb hnb
    simp only [passed, a1, a2, a3, a4, b1, b2, b3, b4, b5, b6, b7, b8] at h320 h80 hsb hnb
    obtain ⟨B', hB', hle⟩ := soft_late_stage hp hX hFw (k := k)
      (A := okPolls (sobj L g 80) ((X.tr g).take k)) hw (by
        rw [soft_isBarId hw, count hσ, ← hLk _ rfl, hnb, sobj, soft_okPolls hw, count hσ,
          ← hLk _ rfl, h80]
        omega) rfl
    obtain rfl := hB.stage rfl hw hw rfl hB'
    rw [soft_isStage' hw, count hσ, ← hLk _ rfl, hsb] at hle
    rw [sobj, soft_okPolls hw, count hσ, ← hLk _ rfl, h320]
    omega

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
