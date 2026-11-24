-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Channels
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Lag
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Pick
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Lag
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Final
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Winner
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lag
import Lemmas.Kernel.Progress.HandoffBlockers
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The P polls of the MMA warp are blocked by an earlier lane -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem p_cta_lt (hp : Pre p L m) (hg : g < L.threads) {y : Nat} (hy : y / L.block = g / L.block) :
    y < L.threads := by
  have hb := hp.block
  have h1 : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
  rw [← hy] at h1
  exact (Nat.div_lt_iff_lt_mul (by omega)).mp h1

/-- The softmax lanes of the CTA have one round more than the MMA warp's rescale rounds. -/
theorem soft_rounds {R y : Nat} (hR : MmaRounds p L g R) (hy : y / L.block = g / L.block) :
    ∃ T, SoftRounds p L y T ∧ T = R + 1 := by
  obtain ⟨r, bal, hP, -⟩ := id hR
  have h : SoftRounds p L y _ := ⟨r, bal, picked_cta hy.symm hP, rfl⟩
  exact ⟨_, h, h.mma hy hR⟩

/-- The correction lanes of the CTA have the MMA warp's rescale rounds. -/
theorem corr_rounds (hp : Pre p L m) (hg : g < L.threads) {R y : Nat} (hR : MmaRounds p L g R)
    (hy : y / L.block = g / L.block) : CorrRounds p L y R := by
  obtain ⟨r, bal, hP, -⟩ := id hR
  have h : CorrRounds p L y _ := ⟨r, bal, picked_cta hy.symm hP, rfl⟩
  have h2 := (h.mma hp (p_cta_lt hp hg hy)).unique (hR.cta hy.symm)
  rw [h2] at h
  exact h

/-- **The P polls of warp 12** (P full and second P): when the barrier's final phase has the poll's
parity the lane has an earlier blocker. A producer short of the round is before the slot of the
poll. -/
theorem p_lag (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X)
    (hg : g < L.threads) (hg12 : Prologue.warpIndex L g = 12) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Mma.minj p L g d n)))
    {o r : Nat} (hR : ∃ R, MmaRounds p L g R ∧ r ≤ R)
    (htime : Progress.clk p (r + 1) 0 ≤ Progress.time p L g (Mma.minj p L g d n))
    (hn : n (.mma (.acquire (obj L g o))) = r) (hok : okPolls (obj L g o) (X.tr g) = r)
    (hst : ∃ st : Fin 2, o = 96 + 8 * st.val ∨ o = 112 + 8 * st.val) :
    ∃ before, MBarrier.stateBefore (X.objects (obj L g o))
        (X.objects (obj L g o)).length = some before ∧
      (before.phase % 2 = n (.mma (.acquire (obj L g o))) % 2 →
        Sched.Blk (Progress.timed p L) X g) := by
  obtain ⟨R, hR, hrR⟩ := hR
  obtain ⟨st, hst⟩ := hst
  have hT : ∃ R bal, Epilogue.Picked p L g R bal := by
    obtain ⟨R, bal, hP, -⟩ := hR
    exact ⟨R, bal, hP⟩
  have hmm : MmaIn L g g := ⟨hg, rfl, hg12⟩
  have hne : X.tr g ≠ [] := by
    intro h0
    rw [show (X.tr g).length = 0 by rw [h0]; rfl, Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ
  have hcta : ∀ {y}, y / L.block = g / L.block → ∃ R bal, Epilogue.Picked p L y R bal := by
    rintro y hy
    obtain ⟨R, bal, hP⟩ := hT
    exact ⟨R, bal, picked_cta hy.symm hP⟩
  have blk : ∀ y, y < L.threads → y / L.block = g / L.block →
      (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) →
      Sched.threadTime (Progress.timed p L) X y < Progress.clk p (r + 1) 0 →
      Sched.Blk (Progress.timed p L) X g := by
    intro y hyt hy hx ht
    refine Sched.blk_of_lags hX hub hg hne hσ hyt (by rw [hy]) fun _ => ⟨hx, ?_⟩
    exact ht.trans_le htime
  rcases hst with rfl | rfl
  · obtain ⟨f, hf⟩ := final_exists hp hX hFw hg (i := .mma) hσ (by simp [IsEntry])
      (o := 96 + 8 * st.val) (by simp only [ObjOff]; omega) (pObj hp hX hFw g st).init
    refine ⟨f, hf, fun hpar => ?_⟩
    obtain ⟨hph, a, ha⟩ := p_blocked hp hX hFw hff g st hmm hf (by rw [hok]; exact hn ▸ hpar)
    obtain ⟨hyc, hyw⟩ := pLane_facts hp (g / L.block) st.isLt a
    generalize pLane L (g / L.block) st.val a = y at ha hyc hyw
    rw [hph, hok] at ha
    have hyt := p_cta_lt hp hg hyc
    rcases hyw with ⟨h8, hst'⟩ | ⟨h8, h11⟩
    · have hin : SoftIn L g st.val y := ⟨hyt, hyc, h8, hst'⟩
      obtain ⟨T, hT', hTR⟩ := soft_rounds hR hyc
      rw [← soft_obj_eq hin 96] at ha
      refine blk y hyt hyc (fun k pc hx => ?_)
        (soft_early hp hX hFw hub hyt h8 (hcta hyc) hT' (by omega) ha)
      have h1 := (soft_exit_rounds hp hX hFw h8 (hcta hyc) hx).1.unique hT'
      have h2 : arrivals (sobj L y 96) ((X.tr y).take k) ≤ arrivals (sobj L y 96) (X.tr y) :=
        (List.take_sublist _ _).countP_le
      omega
    · have hC := corr_rounds hp hg hR hyc
      have hq : ∀ st : Fin 2, ∃ q : Fin 4, corrO q = 96 + 8 * st.val ∧ corrE q = 0 ∧
          tileB q ≤ Progress.span := by decide
      obtain ⟨q, hqo, hqe, hqb⟩ := hq st
      rw [← obj_cta hyc, ← hqo] at ha
      refine blk y hyt hyc (fun k pc hx => ?_)
        ((corr_early hp hX hFw hub hyt h8 h11 (hcta hyc) q hC (by omega) ha).trans_le ?_)
      · obtain ⟨R', hR', h1⟩ := corr_exit_rounds hp hX hFw h8 h11 (hcta hyc) q hx
        have := hR'.unique hC
        have h2 : arrivals (obj L y (corrO q)) ((X.tr y).take k) ≤
            arrivals (obj L y (corrO q)) (X.tr y) := (List.take_sublist _ _).countP_le
        omega
      · rw [hqe]
        unfold Progress.clk
        rw [Nat.add_zero, Nat.mul_succ]
        omega
  · obtain ⟨f, hf⟩ := final_exists hp hX hFw hg (i := .mma) hσ (by simp [IsEntry])
      (o := 112 + 8 * st.val) (by simp only [ObjOff]; omega) (p2Obj hp hX hFw g st).init
    refine ⟨f, hf, fun hpar => ?_⟩
    obtain ⟨hph, a, ha⟩ := p2_blocked hp hX hFw hff g st hmm hf (by rw [hok]; exact hn ▸ hpar)
    obtain ⟨hzp, hwp⟩ := p2Prod_spec (X := X) (g := g) hp st.isLt a
    have hb4 := a.isLt
    have hst2 := st.isLt
    obtain ⟨z, hzt, hzc, hzw, hwin⟩ := warp_winner hp hX hg (w := 4 * st.val + a.val) (by omega)
    rw [hph, hok] at ha
    have h8 : Prologue.warpIndex L z < 8 := by omega
    have hin : SoftIn L g st.val z := ⟨hzt, hzc, h8, by omega⟩
    obtain ⟨T, hT', hTR⟩ := soft_rounds hR hzc
    -- the warp's winner is its second P producer, or has made no arrival
    have harr : arrivals (obj L g (112 + 8 * st.val)) (X.tr z) ≤ r := by
      by_contra hgt
      obtain ⟨e, he, hea⟩ := List.countP_pos_iff.mp
        (show 0 < arrivals (obj L g (112 + 8 * st.val)) (X.tr z) by omega)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
      have hget : X.get (z, j) = some ((X.tr z)[j]) := List.getElem?_eq_getElem hj
      generalize (X.tr z)[j] = e at hget hea
      obtain ⟨pc, kd⟩ := e
      cases kd <;> simp [arrivesOn, sourceArrive] at hea
      subst hea
      obtain ⟨a', rfl⟩ := p2Prod_of hp hX hFw st.isLt ⟨j, pc, _, _, _, _, hget⟩
      obtain ⟨-, hwa⟩ := p2Prod_spec (X := X) (g := g) hp st.isLt a'
      have : a' = a := Fin.ext (by omega)
      subst this
      exact hgt ha
    have hP2 : (X.tr z).countP (isP2 L z) ≤ r := by
      rw [isP2_winner h8 hwin, soft_obj_eq hin 112]
      exact harr
    refine blk z hzt hzc (fun k pc hx => ?_)
      (soft_early2 hp hX hFw hub hzt h8 (hcta hzc) hT' (by omega) hP2)
    obtain ⟨h1, h3⟩ := soft_exit_rounds hp hX hFw h8 (hcta hzc) hx
    have h1 := h1.unique hT'
    have h2 : ((X.tr z).take k).countP (isP2 L z) ≤ (X.tr z).countP (isP2 L z) :=
      (List.take_sublist _ _).countP_le
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
