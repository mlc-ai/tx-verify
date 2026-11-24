-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageBar
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Lemmas.Protocol.NamedBarArrive
import Lemmas.Protocol.NamedBarMember
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The stage barriers and every softmax lane's bias polls

Stage `st`'s named barrier `11 + st` is met by the 128 lanes of its four softmax warps, once per
round that reads the bias slot. So lane 0's release of round `u` follows every lane's stage-barrier
event of ordinal `u` (`stage_rendezvous`), hence every lane's poll `u` of the bias slot, and a copy
of round `s` follows every lane's polls of the rounds before `s` (`bias_reach`). Counting the items
of the phases a lane observes, its poll with `u` earlier ones observes the two copies of round `u`
(`bias_observes`): the hand-off of `biasHandoff` holds for every lane. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy CtaBarrier
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The stage's softmax warps. -/
def stageWarps (st : Nat) : Finset Nat := {4 * st, 4 * st + 1, 4 * st + 2, 4 * st + 3}

theorem mem_stageWarps {st w : Nat} : w ∈ stageWarps st ↔ w / 4 = st := by
  simp only [stageWarps, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem stage_shape (hp : Pre p L m) {st : Nat} (hst : st < 2) :
    NamedBar.Shape L (some 128) (stageWarps st) (stageId st) := by
  have hcard : (stageWarps st).card = 4 := by
    unfold stageWarps
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_pair (by omega)]
  exact
    { pos := by rw [hcard]; decide
      target := by
        rw [hcard]
        exact NamedBar.target_some_mul (n := 4) (by decide) (by decide)
      bound := by
        intro w hw
        rw [hp.block]
        have := mem_stageWarps.mp hw
        omega
      id_lt := by unfold stageId; omega }

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- An event on a stage barrier is a softmax lane's of the stage. -/
theorem stage_of_bar {h i pc st : Nat} {cnt : Option Nat} {md : BarMode} (hst : st < 2)
    (he : X.get (h, i) = some ⟨pc, .bar (stageId st) cnt md⟩) :
    Prologue.warpIndex L h < 8 ∧ Prologue.warpIndex L h / 4 = st ∧ cnt = some 128 ∧ md = .sync ∧
      okPolls (sobj L h 320) ((X.tr h).take i) = barOrd X h i (stageId st) + 1 ∧
      ∃ B, StageRounds p L h B ∧ barOrd X h i (stageId st) ≤ B := by
  have hid : stageId st = 11 ∨ stageId st = 12 := by unfold stageId; omega
  have hw : Prologue.warpIndex L h < 8 := by
    have hh := Frame.lt_of_get hX he
    by_contra hge
    have h16 := Prologue.warpIndex_lt hp h
    by_cases hc : Prologue.warpIndex L h ≤ 11
    · rcases corr_bar hp hX hFw (by omega) hc he with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨q, h0, -⟩
      · omega
      · omega
      · have := q.isLt; omega
    · have hs := bar_sched hp hX hFw hh he
      have h8 : ¬ Prologue.warpIndex L h < 8 := by omega
      have h12 : Prologue.warpIndex L h = 12 ∨ Prologue.warpIndex L h = 13 ∨
          Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15 := by omega
      simp only [schedB, h8, h12, ite_true, ite_false] at hs
      split_ifs at hs <;> simp only [Prod.mk.injEq] at hs <;> omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := soft_stage_bar hp hX hFw hw hid he
  refine ⟨hw, ?_, h2, h3, h4, h5⟩
  unfold stageId at h1
  omega

theorem stage_sources {st : Nat} (hst : st < 2) :
    NamedBar.Sources L X (some 128) (stageWarps st) (stageId st) := by
  intro e pc cnt ⟨md, he⟩ hg
  obtain ⟨-, h2, h3, -⟩ := stage_of_bar hp hX hFw hst (h := e.1) (i := e.2) he
  exact ⟨mem_stageWarps.mpr h2, h3⟩

/-- An exited softmax lane of a tile met the stage barrier once more than its biased rounds. -/
theorem stage_exit {h jx pcx st : Nat} (hw : Prologue.warpIndex L h < 8)
    (hs : Prologue.warpIndex L h / 4 = st)
    (hx : X.get (h, jx) = some ⟨pcx, .exit⟩) {R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L h R bal) :
    ∃ B, StageRounds p L h B ∧ B + 1 ≤ barOrd X h jx (stageId st) := by
  subst hs
  rcases soft_exit hp hX hFw hw hx with hno | ⟨h1, h2⟩
  · exact absurd ⟨R, bal, hP⟩ hno
  obtain ⟨z, pcz, cntz, mz, hz, hzget, hzo⟩ := exists_bar (X := X) (g := h) (x := jx)
    (c := okPolls (sobj L h 80) ((X.tr h).take jx)) (id := Prologue.warpIndex L h + 3)
    (show _ ≤ barOrd X h jx _ from h1.ge)
  have hm := MbarRing.Poll.okPolls_mono (sobj L h 80) (X.tr h) hz.le
  have hno : okPolls (sobj L h 80) ((X.tr h).take z) =
      ((X.tr h).take z).countP (Execution.isBarId (Prologue.warpIndex L h + 3)) := by
    rcases soft_bar hp hX hFw hw hzget with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, -, -, -, h4⟩
    · omega
    · omega
    · omega
    · rcases h4 with h4 | ⟨h4, -⟩
      · rw [show ((X.tr h).take z).countP (Execution.isBarId (Prologue.warpIndex L h + 3)) =
          okPolls (sobj L h 80) ((X.tr h).take jx) from hzo] at h4
        omega
      · exact h4
  obtain ⟨B, hB, hcnt⟩ := soft_fin_stage hp hX hFw hw hzget hno
  refine ⟨B, hB, ?_⟩
  have := (List.take_sublist_take_left (l := X.tr h) hz.le).countP_le
    (p := Execution.isBarId (stageId (Prologue.warpIndex L h / 4)))
  unfold barOrd
  omega

/-- **The stage rendezvous**: a passed stage-barrier event and the event of the same ordinal of any
lane of the stage, from which its return follows. -/
theorem stage_rendezvous {y j pc h : Nat} {st : Fin 2}
    (hy : X.get (y, j) = some ⟨pc, .bar (stageId st.val) (some 128) .sync⟩)
    (hpass : j + 1 < (X.tr y).length) (hh : SoftIn L g st.val h) (hc : g / L.block = y / L.block) :
    ∃ i pc', X.get (h, i) = some ⟨pc', .bar (stageId st.val) (some 128) .sync⟩ ∧
      barOrd X h i (stageId st.val) = barOrd X y j (stageId st.val) ∧
      Witness L X (.thread (h, i)) (y, j) := by
  have hst := st.isLt
  obtain ⟨hhl, hhc, hhw, hhs⟩ := hh
  have hylt := Frame.lt_of_get hX hy
  have hf : X.IsBarrier (y, j) (stageId st.val) (some 128) pc := hy
  obtain ⟨hyw, hys, -, -, -, By, hBy, hle⟩ := stage_of_bar hp hX hFw hst hy
  have hcta : h / L.block = y / L.block := hhc.trans hc
  obtain ⟨Ry, baly, hPy⟩ := hBy.picked hcta.symm
  obtain ⟨i, pc', md, hi, hord⟩ := NamedBar.Sources.member_arrival_any hX
    (stage_sources hp hX hFw hst) (stage_shape hp hst) hf hpass hcta
    (mem_stageWarps.mpr (show (h % L.block) / 32 / 4 = st.val from hhs))
    (fun ⟨jx, pcx, hx⟩ => by
      obtain ⟨B, hB, hge⟩ := stage_exit hp hX hFw hhw hhs hx hPy
      have hBB := StageRounds.stage hcta hhw hyw (hhs.trans hys.symm) hB hBy
      obtain ⟨z, pcz, cnt, mz, -, hz, hzo⟩ := exists_bar (X := X) (g := h) (x := jx)
        (c := barOrd X y j (stageId st.val)) (id := stageId st.val) (by omega)
      obtain ⟨-, -, hcnt, -⟩ := stage_of_bar hp hX hFw hst hz
      rw [hcnt] at hz
      exact ⟨z, pcz, mz, hz, hzo⟩)
  obtain ⟨-, -, -, rfl, -⟩ := stage_of_bar hp hX hFw hst hi
  refine ⟨i, pc', hi, hord, ?_⟩
  have hS := stage_sources hp hX hFw hst
  have hG := stage_shape hp hst
  have hsame : SameCta L h y := ⟨hhl, hylt, hcta⟩
  have hke := hS.arrive_key_of_credit hX hG hi hhl hsame.2.2.symm hf hpass hord.symm
  obtain ⟨key, hkf, hdone⟩ := ctaBarDone_of_returned hX hf hpass
  have hkey := hS.arrival_key hX hG hf (CtaBarK.arrival hkf)
  simp only at hkey hke
  rw [hkey, ← hord] at hkf hdone
  obtain ⟨ic, hcomp⟩ := hdone
  exact Witness.of_ctaBarCounted hkf hcomp hke hsame.2.2

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
