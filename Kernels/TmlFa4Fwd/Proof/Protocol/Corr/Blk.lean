-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.PollLag
public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Channels
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Out
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Pick
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitLag
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Final
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.O
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Target
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Winner
import Kernels.TmlFa4Fwd.Proof.Protocol.Free.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Blk
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Progress at the correction polls: a blocked poll has an earlier blocker

* `o_lag`: O, the MMA warp's committing lane without its commit;
* `free_first`: a lane that has not made its ready arrival finds the free barrier at phase 0;
* `free_last`: the last free poll, an output lane that has not freed the stage. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X) (hg : g < L.threads)
  {d : Correction.Control.D} {n : Cls → Nat}
  (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.correction, d⟩, n)))
include hp hX hFw hff hub hg hσ

omit hp hX hFw hff hub hg in
private theorem corr_ne : X.tr g ≠ [] := by
  intro h0
  rw [show (X.tr g).length = 0 by rw [h0]; rfl, Frame.stateAt_zero] at hσ
  simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ

omit hp hFw hff in
private theorem corr_blk {y : Nat} (hyt : y < L.threads) (hy : y / L.block = g / L.block)
    (hx : ∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩)
    (ht : Sched.threadTime (Progress.timed p L) X y <
      Progress.time p L g (.inr ⟨.correction, d⟩, n)) :
    Sched.Blk (Progress.timed p L) X g :=
  Sched.blk_of_lags hX hub hg (corr_ne hσ) hσ hyt (by rw [hy]) fun _ => ⟨hx, ht⟩

omit hff in
/-- **O.** -/
theorem o_lag {st : Fin 2} (hs : d.scheduler.site = .fw st 0) {f : MBarrier.State}
    (hst : Final X (obj L g (144 + 8 * st.val)) f) (hpar : f.phase % 2 = 0) :
    Sched.Blk (Progress.timed p L) X g := by
  obtain ⟨R, hC, hn, -, -⟩ := corr_fw_at hp hX hFw hub hg hσ hs
  have hR := hC.mma hp hg
  rcases o_blocked hp hX hFw g st hst hpar with h | h
  swap
  · exact .inl ⟨.commit, .inl rfl, h⟩
  obtain ⟨z, hzt, hzc, hzw, hwin⟩ := warp_winner hp hX hg (w := 12) (by omega)
  have hRz := hR.cta hzc.symm
  have hcnt : (X.tr z).countP (commitsTo (obj L z (144 + 8 * st.val))) ≤ 0 := by
    rw [obj_cta hzc]
    by_contra hgt
    obtain ⟨e, he, hea⟩ := List.countP_pos_iff.mp
      (show 0 < (X.tr z).countP (commitsTo (obj L g (144 + 8 * st.val))) by omega)
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
      exact h _ _ _ _ hget ht
    · cases hea
  have hbm := mma_rounds_bmax hp hg hR
  refine corr_blk hX hub hg hσ hzt hzc (fun k pc hx => ?_)
    ((o_commit_early hp hX hFw hub hzt hzw hwin hRz st hcnt).trans_le ?_)
  · have := mma_exit_commits hp hX hFw hub hzt hzw hwin hRz hx (144 + 8 * st.val)
    rw [commitAt_o] at this
    omega
  · have hsl : Progress.slotOf p (R + 1) = R + 1 := Progress.slotOf_eq (by omega)
    simp only [Progress.time, Progress.roleTime, Progress.Cr.time, hs, Progress.Cr.part,
      Progress.Cr.slot, hn, ite_true, show R + 2 - 1 = R + 1 by omega, hsl]
    unfold Progress.clk Progress.bandC
    omega

omit hff hub in
/-- **A lane that has not made its ready arrival finds the free barrier at phase 0.** -/
theorem free_first (hE : d.scheduler.site ≠ .setmax) (st : Fin 2)
    (hw : 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11)
    (h0 : arrivals (obj L g (208 + 8 * st.val)) (X.tr g) = 0) {f : MBarrier.State}
    (hst : Final X (obj L g (224 + 8 * st.val)) f) : f.phase = 0 := by
  by_contra hne
  have O := freeObj hp hX hFw g st
  -- an output lane's free arrival, and its ready poll before it
  obtain ⟨_, r, i, -, hr, -, ha, hid, -, -⟩ := O.phase_all hX (q := 0) le_rfl hst (by omega)
    (fun p' _ r a i c tx hr _ ha hid _ => by
      obtain ⟨pc, sc, he⟩ := O.arrive_of_id hr ha hid
      rcases free_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨-, -, h⟩⟩
      · cases hk
      · exact h) 0
  obtain ⟨pc, sc, he⟩ := O.arrive_of_id hr ha hid
  have hc := outLane_cta (L := L) hp (g / L.block) 0
  have hw13 : Prologue.warpIndex L (outLane L (g / L.block) 0) = 13 := by
    rcases free_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨-, h, -⟩⟩
    · cases hk
    · exact h
  generalize outLane L (g / L.block) 0 = y at he hc hw13
  rw [← obj_cta hc] at he
  have hp1 := out_free_polled hp hX hFw hw13 he
  rw [obj_cta hc] at hp1
  -- the ready barrier's final phase is past it
  obtain ⟨hloc, ho⟩ := readyLoc_off L g st
  have P := readyObj hp hX hFw g st
  have hin := P.init
  rw [hloc] at hin
  obtain ⟨f', hf'⟩ := final_exists hp hX hFw hg hσ (i := .correction)
    (by simpa [IsEntry, Correction.Control.D.scheduler] using hE)
    ho hin
  have hle : okPolls (obj L g (208 + 8 * st.val)) (X.tr y) ≤ f'.phase + 0 := by
    rw [← hloc] at hf' ⊢
    exact MbarRing.okPolls_le_phase hX (Nat.zero_le 1)
      (PairTmaRing.poll_clean hX P.init P.noInval) P.noInval
      (fun k pc q acq sc he => P.parity he) hf'
  have h2 : okPolls (obj L g (208 + 8 * st.val)) ((X.tr y).take i) ≤
      okPolls (obj L g (208 + 8 * st.val)) (X.tr y) := (List.take_sublist _ _).countP_le
  -- so every correction lane has arrived
  obtain ⟨a, ha'⟩ := corrLane_of hp (h := g) rfl hw
  rw [← hloc] at hf'
  obtain ⟨_, r', i', -, hr', -, hact, hid', -, -⟩ := P.phase_all hX (q := 0) le_rfl hf' (by omega)
    (fun p' _ r a i c tx hr _ ha hid _ => by
      obtain ⟨pc, sc, he⟩ := P.arrive_of_id hr ha hid
      exact ready_arr_zero hp hX hFw he (by simp [arrivesOn, sourceArrive])) a
  obtain ⟨pc', sc', he'⟩ := P.arrive_of_id hr' hact hid'
  rw [← ha', hloc] at he'
  have : 0 < arrivals (obj L g (208 + 8 * st.val)) (X.tr g) :=
    List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? he', by simp [arrivesOn, sourceArrive]⟩
  omega

/-- **The last free poll.** -/
theorem free_last (hs : d.scheduler.site = .wend true) {f : MBarrier.State}
    (hst : Final X (obj L g 232) f) (hpar : f.phase % 2 = 0) :
    Sched.Blk (Progress.timed p L) X g := by
  obtain ⟨hok, -, hRR⟩ := corr_wend_at hp hX hFw hub hg hσ hs
  simp only [ite_true] at hok
  obtain ⟨hph, a, ha⟩ := free_blocked hp hX hFw hff g 1 hst hok.ge (by
    rw [show okPolls (obj L g (224 + 8 * (1 : Fin 2).val)) (X.tr g) = 1 from hok, hpar])
  have hc := outLane_cta (L := L) hp (g / L.block) a
  have hw13 : Prologue.warpIndex L (outLane L (g / L.block) a) = 13 := by
    have hb := hp.block
    have := a.isLt
    unfold Prologue.warpIndex outLane
    rw [hb]; omega
  generalize outLane L (g / L.block) a = y at ha hc hw13
  have hyt := p_cta_lt hp hg hc
  rw [← obj_cta hc] at ha
  have ha0 : arrivals (obj L y (224 + 8 * (1 : Fin 2).val)) (X.tr y) ≤ 0 := by
    refine ha.trans ?_
    have : okPolls (obj L g (224 + 8 * (1 : Fin 2).val)) (X.tr g) = 1 := hok
    omega
  have hT : ∃ R bal, Epilogue.Picked p L g R bal := by
    obtain ⟨R, r, bal, hP, -⟩ := hRR rfl
    exact ⟨r, bal, hP⟩
  refine corr_blk hX hub hg hσ hyt hc (fun k pc hx => ?_)
    ((out_early hp hX hFw hyt hw13 1 ha0).trans_le ?_)
  · obtain ⟨R, bal, hP⟩ := hT
    have h1 := out_exit hp hX hFw hyt hw13 1 ⟨R, bal, picked_cta hc.symm hP⟩ hx
    have h2 : arrivals (obj L y (224 + 8 * (1 : Fin 2).val)) ((X.tr y).take k) ≤
        arrivals (obj L y (224 + 8 * (1 : Fin 2).val)) (X.tr y) := (List.take_sublist _ _).countP_le
    omega
  · simp only [Progress.time, Progress.roleTime, Progress.Cr.time, hs, Progress.Cr.part,
      Progress.Cr.endOff, Progress.endT, ite_true, Progress.doneBase]
    omega

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
