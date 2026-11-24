-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Channels
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.PollLag
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Lag
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Pick
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitLag
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Winner
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Target
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Blk
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Protocol.S.Notify
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Progress at the softmax polls: a blocked poll has an earlier blocker

* `s_lag`: S full, the MMA warp's committing lane short of the round's commit, in the slot's first
  band;
* `credit_lag`, `wend_lag`: the credit, a correction lane short of the credit arrival. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The MMA warp's rounds of a CTA whose softmax lanes have `T` rounds. -/
theorem soft_mma {T y : Nat} (hT : SoftRounds p L g T) (hy : y / L.block = g / L.block) :
    ∃ R, MmaRounds p L y R ∧ T = R + 1 := by
  obtain ⟨r, bal, hP, -⟩ := id hT
  have h : MmaRounds p L y _ := ⟨r, bal, picked_cta hy.symm hP, rfl⟩
  exact ⟨_, h, hT.mma hy.symm h⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X) (hg : g < L.threads)
  {d : Softmax.Control.D} {n : Cls → Nat}
  (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.softmax, d⟩, n)))
include hp hX hFw hff hub hg hσ

omit hp hX hFw hff hub hg in
private theorem soft_ne : X.tr g ≠ [] := by
  intro h0
  rw [show (X.tr g).length = 0 by rw [h0]; rfl, Frame.stateAt_zero] at hσ
  simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ

omit hp hFw hff in
private theorem soft_blk {y : Nat} (hyt : y < L.threads) (hy : y / L.block = g / L.block)
    (hx : ∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩)
    (ht : Sched.threadTime (Progress.timed p L) X y <
      Progress.time p L g (.inr ⟨.softmax, d⟩, n)) :
    Sched.Blk (Progress.timed p L) X g :=
  Sched.blk_of_lags hX hub hg (soft_ne hσ) hσ hyt (by rw [hy]) fun _ =>
    ⟨hx, ht⟩

/-- **S full.** -/
theorem s_lag {r : Softmax.Rd} (hs : d.scheduler.site = .ws r) {f : MBarrier.State}
    (hst : Final X (sobj L g 80) f)
    (hpar : f.phase % 2 = okPolls (sobj L g 80) (X.tr g) % 2) :
    Sched.Blk (Progress.timed p L) X g := by
  obtain ⟨hw, -⟩ := soft_end hp hX hFw hub hg hσ
  obtain ⟨T, u, hT, hu, hok, hn⟩ := soft_poll_at hp hX hFw hub hg hσ
    (show midPoll d.scheduler.site = some (0, 0) by rw [hs]; rfl)
  have hok' : okPolls (sobj L g 80) (X.tr g) = u := by
    rw [hs] at hok; exact hok
  have hst2 : Prologue.warpIndex L g / 4 < 2 := by omega
  have hob : sobj L g 80 = obj L g (80 + 8 * (⟨_, hst2⟩ : Fin 2).val) := by
    simp only [sobj]; congr 1; omega
  rw [hob] at hst hpar hok'
  generalize hst' : (⟨Prologue.warpIndex L g / 4, hst2⟩ : Fin 2) = st at *
  have hin : SoftIn L g st.val g := ⟨hg, rfl, hw, by rw [← hst']⟩
  obtain ⟨c, O, hcl⟩ := sNotify_lane hp hX hFw g st
  have hph : f.phase = u := by
    obtain ⟨c', h⟩ := s_blocked hp hX hFw hff g st
    rw [(h hin hst hpar).1, hok']
  rcases commit_short hp hX hff O hst with h | h
  swap
  · exact .inl ⟨.commit, .inl rfl, h⟩
  obtain ⟨z, hzt, hzc, hzw, hwin⟩ := warp_winner hp hX hg (w := 12) (by omega)
  obtain ⟨R, hR, hTR⟩ := soft_mma hT hzc
  have hzo : obj L z (80 + 8 * st.val) = obj L g (80 + 8 * st.val) := obj_cta hzc _
  have hcnt : (X.tr z).countP (commitsTo (obj L z (80 + 8 * st.val))) ≤ u := by
    rw [hzo]
    by_contra hgt
    have hc : z = c := by
      obtain ⟨e, he, hea⟩ := List.countP_pos_iff.mp
        (show 0 < (X.tr z).countP (commitsTo (obj L g (80 + 8 * st.val))) by omega)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
      have hget : X.get (z, j) = some ((X.tr z)[j]) := List.getElem?_eq_getElem hj
      generalize (X.tr z)[j] = e at hget hea
      obtain ⟨pc, kd⟩ := e
      unfold commitsTo at hea
      split at hea
      · rename_i sp hk
        obtain rfl : kd = .tc (.commit sp) := hk
        obtain ⟨rank, ht⟩ := commit_self hp hX hget
        rw [of_decide_eq_true hea] at ht
        exact hcl _ _ _ _ hget ht
      · cases hea
    rw [← hc] at h
    omega
  have hbm := mma_rounds_bmax hp hzt hR
  refine soft_blk hX hub hg hσ hzt hzc (fun k pc hx => ?_)
    ((s_commit_early hp hX hFw hub hzt hzw hwin hR st (by omega) hcnt).trans_le ?_)
  · have := mma_exit_commits hp hX hFw hub hzt hzw hwin hR hx (80 + 8 * st.val)
    rw [commitAt_s] at this
    omega
  · have hsl : Progress.slotOf p u = u := Progress.slotOf_eq (by omega)
    simp only [Progress.time, Progress.roleTime, Progress.Sm.time, hs, Progress.Sm.place, hn,
      Bool.false_eq_true, ite_false, Nat.sub_zero, Nat.add_zero, hsl]
    unfold Progress.clk Progress.bandS
    omega

/-- A credit barrier short of the final phase: a correction lane short of its arrival. -/
private theorem credit_core {T v : Nat} (hT : SoftRounds p L g T) (hv : v ≤ T) (st : Fin 2)
    (hok : okPolls (obj L g (192 + 8 * st.val)) (X.tr g) = v + 1)
    (hin : SoftIn L g st.val g) {f : MBarrier.State}
    (hst : Final X (obj L g (192 + 8 * st.val)) f)
    (hpar : f.phase % 2 = (okPolls (obj L g (192 + 8 * st.val)) (X.tr g) + 1) % 2)
    (htime : Progress.clk p (v + st.val) (if st.val = 0 then Progress.bandP 0
      else Progress.bandS 1) ≤
      Progress.time p L g (.inr ⟨.softmax, d⟩, n)) :
    Sched.Blk (Progress.timed p L) X g := by
  obtain ⟨hph, a, ha⟩ := credit_blocked hp hX hFw hff g st hin hst hpar
  obtain ⟨hyc, hyw⟩ := corrLane_facts hp (g / L.block) a
  generalize corrLane L (g / L.block) a = y at ha hyc hyw
  have ha4 := a.isLt
  have hyt := p_cta_lt hp hg hyc
  obtain ⟨R, hR, hTR⟩ := soft_mma hT rfl
  have hC := corr_rounds hp hg hR hyc
  have hq : ∀ st : Fin 2, ∃ q : Fin 4, corrO q = 192 + 8 * st.val ∧ corrE q = st.val ∧
      tileB q = if st.val = 0 then Progress.bandP 0 else Progress.bandS 1 := by decide
  obtain ⟨q, hqo, hqe, hqb⟩ := hq st
  rw [← obj_cta hyc, ← hqo] at ha
  have hTy : ∃ R bal, Epilogue.Picked p L y R bal := by
    obtain ⟨r, bal, hP, -⟩ := hT
    exact ⟨r, bal, picked_cta hyc.symm hP⟩
  refine soft_blk hX hub hg hσ hyt hyc (fun k pc hx => ?_)
    ((corr_early hp hX hFw hub hyt (by omega) (by omega) hTy q hC (v := v) (by omega)
      (by omega)).trans_le ?_)
  · obtain ⟨R', hR', h1⟩ := corr_exit_rounds hp hX hFw (by omega) (by omega) hTy q hx
    have := hR'.unique hC
    have h2 : arrivals (obj L y (corrO q)) ((X.tr y).take k) ≤
        arrivals (obj L y (corrO q)) (X.tr y) := (List.take_sublist _ _).countP_le
    omega
  · rw [hqe, hqb]; exact htime

/-- **The credit.** -/
theorem credit_lag (hs : Softmax.pollOff d.scheduler.site = 192) {f : MBarrier.State}
    (hst : Final X (sobj L g 192) f)
    (hpar : f.phase % 2 = (okPolls (sobj L g 192) (X.tr g) + 1) % 2) :
    Sched.Blk (Progress.timed p L) X g := by
  obtain ⟨hw, -⟩ := soft_end hp hX hFw hub hg hσ
  have hst2 : Prologue.warpIndex L g / 4 < 2 := by omega
  have hob : sobj L g 192 = obj L g (192 + 8 * (⟨_, hst2⟩ : Fin 2).val) := by
    simp only [sobj]; congr 1; omega
  have hin : SoftIn L g (⟨_, hst2⟩ : Fin 2).val g := ⟨hg, rfl, hw, rfl⟩
  have hstage : Progress.Sm.stage L g = (⟨_, hst2⟩ : Fin 2).val := by
    unfold Progress.Sm.stage; split <;> simp only <;> omega
  have hno : okPolls (sobj L g 192) (X.tr g) = 0 → Sched.Blk (Progress.timed p L) X g := by
    intro h0
    rw [hob] at hst hpar h0
    have := (credit_blocked hp hX hFw hff g _ hin hst hpar).1
    omega
  have hmain : ∀ {T v}, SoftRounds p L g T → v ≤ T → okPolls (sobj L g 192) (X.tr g) = v + 1 →
      Progress.clk p (v + Prologue.warpIndex L g / 4) (if Prologue.warpIndex L g / 4 = 0 then
        Progress.bandP 0 else Progress.bandS 1) ≤ Progress.time p L g (.inr ⟨.softmax, d⟩, n) →
      Sched.Blk (Progress.timed p L) X g := by
    intro T v hT hv hok ht
    rw [hob] at hst hpar hok
    refine credit_core hp hX hFw hff hub hg hσ hT hv _ hok hin hst hpar ?_
    exact ht
  cases hsite : d.scheduler.site <;> rw [hsite] at hs <;>
    simp only [Softmax.pollOff, reduceCtorEq, Nat.reduceEqDiff] at hs
  case wq => exact hno (soft_first_poll hp hX hFw hub hg hσ (.inl hsite))
  case pwend r =>
    obtain ⟨T, u, hT, hu, hok, hn⟩ := soft_poll_at hp hX hFw hub hg hσ
      (show midPoll d.scheduler.site = some (1, 1) by rw [hsite]; rfl)
    rw [hsite] at hok
    obtain ⟨R, hR, hTR⟩ := soft_mma hT rfl
    have hbm := mma_rounds_bmax hp hg hR
    refine hmain hT hu.le hok ?_
    simp only [Progress.time, Progress.roleTime, Progress.Sm.time, hsite, Progress.Sm.place, hn,
      hstage]
    rcases Nat.lt_or_ge (Prologue.warpIndex L g / 4) 1 with h | h
    · have h0 : Prologue.warpIndex L g / 4 = 0 := by omega
      have hsl : Progress.slotOf p u = u := Progress.slotOf_eq (by omega)
      simp only [h0, ite_true, Nat.add_sub_cancel, hsl, Nat.add_zero]
      unfold Progress.clk
      omega
    · have h1 : Prologue.warpIndex L g / 4 = 1 := by omega
      have hsl : Progress.slotOf p (u + 1) = u + 1 := Progress.slotOf_eq (by omega)
      simp only [h1, one_ne_zero, ite_false, Bool.false_eq_true, Nat.sub_zero,
        hsl]
      unfold Progress.clk
      omega
  case wend l =>
    cases l with
    | false => exact hno (soft_first_poll hp hX hFw hub hg hσ (.inr hsite))
    | true =>
      obtain ⟨T, hT, hok⟩ := soft_last_poll hp hX hFw hub hg hσ hsite
      obtain ⟨R, hR, hTR⟩ := soft_mma hT rfl
      have hbm := mma_rounds_bmax hp hg hR
      refine hmain hT le_rfl hok ?_
      simp only [Progress.time, Progress.roleTime, Progress.Sm.time, hsite, Progress.Sm.place,
        Progress.Sm.pre, Progress.Sm.endOff, Progress.endT, ite_true]
      refine le_trans (le_of_lt (Progress.drain_order p (s := T + Prologue.warpIndex L g / 4)
        ?_ ?_)) (Nat.le_add_right _ _)
      · omega
      · split <;> decide

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
