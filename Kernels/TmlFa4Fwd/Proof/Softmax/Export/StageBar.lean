-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' stage barrier, counted

A stage's named barrier (11, 12) is met once per round that reads the bias slot, after the round's
poll of the slot (`soft_stage_bar`); the arrival that frees the slot follows it (`soft_free_stage`);
after a tile's last round it has been met once more than the tile's biased rounds
(`soft_fin_stage`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (before inBias inPlain ptsOf passed RefQ)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

/-- The stage's named barrier. -/
def stageId (st : Nat) : Nat := 11 + st

/-- **The lane's tile has `B` biased rounds after the first.** -/
def StageRounds (p : Params) (L : Launch) (g B : Nat) : Prop :=
  ∃ R bal, Epilogue.Picked p L g R bal ∧ (Softmax.nB p L g (softRef p L g R bal)).toNat = B

/-- The counts at the sites read here: bias polls, stage barrier, bias releases. -/
private theorem tab (b : Bool) :
    ([Softmax.Site.bsync false, .bsync true, .finarr, .barr false, .barr true].map
      fun s => ((ptsOf b (.acquire 320)).countP (before s), (ptsOf b .sb).countP (before s),
        (ptsOf true (.arrive 336)).countP (before s))) =
      [(1, 0, 0), (2, 1, 1), (1, 1, 1), (1, 1, 0), (2, 2, 1)] ∧
    [(ptsOf b (.acquire 320)).countP inBias, (ptsOf b (.acquire 320)).countP inPlain,
      (ptsOf b .sb).countP inBias, (ptsOf b .sb).countP inPlain,
      (ptsOf true (.arrive 336)).countP inBias, (ptsOf true (.arrive 336)).countP inPlain] =
      [1, 0, 1, 0, 1, 0] := by
  cases b <;> decide +kernel

private theorem regs : Softmax.preR (.bsync false) = true ∧
    inBias (Softmax.Site.bsync true).pos = true := by decide +kernel

theorem soft_stage_id (hw : Prologue.warpIndex L h < 8) :
    (if Softmax.stg L h then 12 else 11) = stageId (Prologue.warpIndex L h / 4) := by
  have hs : Softmax.stg L h = decide (4 ≤ Prologue.warpIndex L h) := by
    have key : ∀ w < 8, Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 = decide (4 ≤ w) := by decide
    exact key _ hw
  rw [hs]
  unfold stageId
  by_cases h4 : 4 ≤ Prologue.warpIndex L h
  · simp only [h4, decide_true, ↓reduceIte]; omega
  · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

theorem soft_isStage (hw : Prologue.warpIndex L h < 8) :
    ((X.tr h).take k).countP (Execution.isBarId (stageId (Prologue.warpIndex L h / 4))) =
      ((X.tr h).take k).countP (cls L h (.soft .sb)) := by
  refine List.countP_congr fun e _ => ?_
  have hw' : h % L.block / 32 < 8 := hw
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [Execution.isBarId, cls, Softmax.cls, Softmax.Cnt.pointed, hw', soft_stage_id
      hw]

/-- The rounds' counts are the picked tile's. -/
private theorem nB_ref {d : Softmax.D} {ns nv R : Nat} {bal : BitVec 64}
    (hC : Epilogue.ChosenVals p L h R bal (SmWarp.toE d) ns nv)
    (h0 : d.v.sc.c0 = Epilogue.qv p (Epilogue.chosen d.v.sc))
    (h1 : d.v.sc.c1 = Epilogue.qv p (Epilogue.addi (Epilogue.chosen d.v.sc) 1))
    (hu : d.v.ukw = Mma.ukv p (Epilogue.chosen d.v.sc)) :
    Softmax.nB p L h d.v = Softmax.nB p L h (softRef p L h R bal) := by
  obtain ⟨-, ht, hgx, hcur, hbal, hpv, hnt, -, -⟩ := hC
  have ht' : d.v.sc.tot = _ := ht
  have hgx' : d.v.sc.gx = _ := hgx
  have hcur' : d.v.sc.cur = _ := hcur
  have hbal' : d.v.sc.bal = _ := hbal
  have hpv' : d.v.sc.pv = _ := hpv
  have hnt' : d.v.sc.nt = _ := hnt
  have hch : Epilogue.chosen d.v.sc =
      Epilogue.chosen (Epilogue.chosenD p (h / L.block) R bal) := by
    simp only [Epilogue.chosen, Epilogue.chosenD, hbal', hgx']
  simp only [Softmax.nB, Softmax.r169, Softmax.r299, Softmax.r166,
    Softmax.r168, Softmax.r165, Softmax.r1808, Softmax.rowOff, Mma.coords, softRef, hu, h0, h1,
    hch, ht', hcur', hpv', hnt', Epilogue.chosenD, Mma.ukv]

/-- The tile's biased rounds at a site of the rounds' region. -/
private theorem stage_at {d : Softmax.D} {ns nv : Nat} (hF : SmWarp.SFits p L h d ns nv)
    (hep : SmWarp.epi d.site = .ready 0) (huk : d.site.hasUk = true) :
    StageRounds p L h (Softmax.nB p L h d.v).toNat := by
  obtain ⟨hFE, hu⟩ := hF
  simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
  obtain ⟨R, bal, hC, h0, h1⟩ := hFE
  exact ⟨R, bal, hC.1, by rw [nB_ref hC h0 h1 (hu huk)]⟩

/-- A lane whose CTA has a tile with rounds has a picked request. -/
theorem StageRounds.picked {g B : Nat} (hc : g / L.block = h / L.block)
    (hB : StageRounds p L g B) : ∃ R bal, Epilogue.Picked p L h R bal := by
  obtain ⟨R, bal, hP, -⟩ := hB
  exact ⟨R, bal, Epilogue.Picked.cta hc hP⟩

/-- **The biased rounds are the stage's.** -/
theorem StageRounds.stage {g B C : Nat} (hc : g / L.block = h / L.block)
    (hw : Prologue.warpIndex L g < 8) (hw' : Prologue.warpIndex L h < 8)
    (hs : Prologue.warpIndex L g / 4 = Prologue.warpIndex L h / 4)
    (hB : StageRounds p L g B) (hC : StageRounds p L h C) : B = C := by
  obtain ⟨R, bal, hP, rfl⟩ := hB
  obtain ⟨R', bal', hP', rfl⟩ := hC
  have hP2 := Epilogue.Picked.cta hc hP
  obtain ⟨rfl, rfl⟩ := hP2.unique hP'
  have hst : Softmax.stg L g = Softmax.stg L h := by
    have key : ∀ w < 8, Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 = decide (4 ≤ w) := by decide
    have e1 : Softmax.stg L g = decide (4 ≤ Prologue.warpIndex L g) := key _ hw
    have e2 : Softmax.stg L h = decide (4 ≤ Prologue.warpIndex L h) := key _ hw'
    rw [e1, e2]
    exact decide_eq_decide.mpr (by omega)
  have e : Softmax.nB p L g (softRef p L g R bal) = Softmax.nB p L h (softRef p L h R bal) := by
    have hct : Epilogue.ctaW L g = Epilogue.ctaW L h := by simp only [Epilogue.ctaW, hc]
    unfold Softmax.nB Softmax.r169 Softmax.r299 Softmax.r168 Softmax.r166 Softmax.r165
      Softmax.r1808 Softmax.rowOff Mma.coords
    simp only [softRef, hst]
    rw [hc, hct]
  rw [e]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L h < 8)
include hp hX hFw hw

/-- **A stage-barrier event** follows one more poll of the bias slot than its earlier ones, which
are at most the tile's biased rounds. -/
theorem soft_stage_bar {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (hid : id = 11 ∨ id = 12) (he : X.get (h, k) = some ⟨pc, .bar id cnt mode⟩) :
    id = stageId (Prologue.warpIndex L h / 4) ∧ cnt = some 128 ∧ mode = .sync ∧
      okPolls (sobj L h 320) ((X.tr h).take k) =
        ((X.tr h).take k).countP (Execution.isBarId id) + 1 ∧
      ∃ B, StageRounds p L h B ∧ ((X.tr h).take k).countP (Execution.isBarId id) ≤ B := by
  rcases soft_counts hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, ns, nv, hQ, hF, hev, hc⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | enter r => simp [exit] at hx
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
    | fence => simp only [Startup.Ev] at hev; cases hev
    | bar =>
      simp only [Startup.Ev, Kind.bar.injEq] at hev
      omega
    | elect j =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
    | init q =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  obtain ⟨⟨b, hs⟩, rfl, rfl, rfl⟩ : (∃ b, d.site = .bsync b) ∧
      id = (if Softmax.stg L h then 12 else 11) ∧ cnt = some 128 ∧ mode = .sync := by
    rcases soft_bar_site hev with ⟨-, rfl, -⟩ | h1 | ⟨-, rfl, -, -⟩
    · omega
    · exact h1
    · exfalso
      rw [soft_nbW hw] at hid
      omega
  rw [soft_stage_id hw]
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [soft_isStage hw, soft_okPolls hw, hc _ rfl, hc _ rfl]
  obtain ⟨t1, t2⟩ := tab (Softmax.lz L h)
  simp only [List.map, List.cons.injEq, Prod.mk.injEq, and_true] at t1 t2
  obtain ⟨a1, a2, -, -, -⟩ := t1
  have c1 := hQ.cnt (.acquire 320) rfl
  have c2 := hQ.cnt .sb rfl
  have hpre := hQ.pre
  have hbias := hQ.bias
  have hst := stage_at hF (by rw [hs]; cases b <;> rfl) (by rw [hs]; cases b <;> rfl)
  clear hF hQ hev hc
  generalize Softmax.nB p L h d.v = nb at hst hbias
  simp only [passed, t2] at c1 c2
  rw [hs] at c1 c2 hpre hbias
  cases b
  · obtain ⟨rfl, rfl⟩ := hpre regs.1
    simp only [a1] at c1 c2
    exact ⟨by omega, _, hst, by omega⟩
  · obtain ⟨rfl, -, hlt, -⟩ := hbias regs.2
    simp only [a2] at c1 c2
    exact ⟨by omega, _, hst, by omega⟩

/-- **The arrival that frees the bias slot** follows one more stage-barrier event than its earlier
ones. -/
theorem soft_free_stage {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (sobj L h 336) tx c rel sc⟩) :
    ((X.tr h).take k).countP (Execution.isBarId (stageId (Prologue.warpIndex L h / 4))) =
      arrivals (sobj L h 336) ((X.tr h).take k) + 1 := by
  rcases soft_counts hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, _, _, hQ, -, hev, hc⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hx (l := sobj L h 336) rfl
    cases hc
  rcases soft_mbar hev (l := sobj L h 336) rfl with ⟨-, hl, hmem⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  rw [soft_bl hw] at hl
  have ho := obj_inj hl
  obtain ⟨b, hs⟩ : ∃ b, d.site = .barr b := by
    revert ho
    cases d.site <;> simp [Softmax.arrOff]
  have hlz := hQ.barr (by rw [hs]; rfl)
  rw [soft_isStage hw, soft_arrivals hw (by decide), hc _ rfl, hc _ rfl, hQ.cnt .sb rfl,
    hQ.cnt (.arrive 336) rfl, hlz, hs]
  obtain ⟨t1, t2⟩ := tab true
  simp only [List.map, List.cons.injEq, Prod.mk.injEq, and_true] at t1 t2
  obtain ⟨-, -, -, a4, a5⟩ := t1
  cases b <;> simp only [passed, t2, a4, a5] <;> omega

/-- **The arrival after the tile's last round** on the correction warps' barrier (as many earlier
ones as S-full polls) follows one more stage-barrier event than the tile's biased rounds. -/
theorem soft_fin_stage {pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (h, k) = some ⟨pc, .bar (Prologue.warpIndex L h + 3) cnt mode⟩)
    (hno : okPolls (sobj L h 80) ((X.tr h).take k) =
      ((X.tr h).take k).countP (Execution.isBarId (Prologue.warpIndex L h + 3))) :
    ∃ B, StageRounds p L h B ∧
      ((X.tr h).take k).countP (Execution.isBarId (stageId (Prologue.warpIndex L h / 4))) =
        B + 1 := by
  rcases soft_counts hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, ns, nv, hQ, hF, hev, hc⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | enter r => simp [exit] at hx
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
    | fence => simp only [Startup.Ev] at hev; cases hev
    | bar =>
      simp only [Startup.Ev, Kind.bar.injEq] at hev
      omega
    | elect j =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
    | init q =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  have hs : d.site = .finarr := by
    rcases soft_bar_site hev with ⟨-, h2, -⟩ | ⟨-, h2, -, -⟩ | ⟨hs, -, -, -⟩
    · omega
    · rw [soft_stage_id hw] at h2; unfold stageId at h2; omega
    · rcases hs with hs | ⟨r, hs⟩
      · exact hs
      · exfalso
        rw [soft_isBarId hw, soft_okPolls hw, hc _ rfl, hc _ rfl, hQ.cnt (.acquire 80) rfl,
          hQ.cnt .nb rfl, hs] at hno
        have t : ∀ b : Bool, ∀ r : Softmax.Rd,
            (ptsOf b (.acquire 80)).countP (before (.narr r)) =
              (ptsOf b .nb).countP (before (.narr r)) + 1 ∧
            (ptsOf b (.acquire 80)).countP inBias = (ptsOf b .nb).countP inBias ∧
            (ptsOf b (.acquire 80)).countP inPlain = (ptsOf b .nb).countP inPlain := by
          intro b r
          cases b <;> cases r <;> decide +kernel
        obtain ⟨e1, e2, e3⟩ := t (Softmax.lz L h) r
        simp only [passed, e1, e2, e3] at hno
        omega
  obtain ⟨t1, t2⟩ := tab (Softmax.lz L h)
  simp only [List.map, List.cons.injEq, Prod.mk.injEq, and_true] at t1 t2
  obtain ⟨-, -, a3, -, -⟩ := t1
  have hst := stage_at hF (by rw [hs]; rfl) (by rw [hs]; rfl)
  have hfin := (hQ.fin (by rw [hs]; decide)).1
  refine ⟨_, hst, ?_⟩
  rw [soft_isStage hw, hc _ rfl, hQ.cnt .sb rfl, hs]
  simp only [passed, t2, a3]
  clear hst hF hQ hev hc
  generalize Softmax.nB p L h d.v = nb at hfin ⊢
  rcases hfin with h | ⟨rfl, h⟩ <;> omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
