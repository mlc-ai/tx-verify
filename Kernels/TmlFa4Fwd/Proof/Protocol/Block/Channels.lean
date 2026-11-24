-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.Free.Obj
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.P.Reach
public import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Handoff
public import Lemmas.Kernel.Progress.HandoffBlockers
public import Lemmas.Protocol.TmaUnitsBlock
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Target
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Who blocks a poll, channel by channel

When no object's record faults and a barrier's final phase has the parity of a poller's next poll,
the phase is the poller's uses (its successful polls, less one on an empty or credit barrier), and
an asynchronous obligation is open or a producer is short: it has made no more of its arrivals,
commits or copies than that. No time occurs; a lag needs only the producer's time below the
waiter's. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The final state of object `l`. -/
abbrev Final (X : Execution) (l : Loc) (st : MBarrier.State) : Prop :=
  MBarrier.stateBefore (X.objects l) (X.objects l).length = some st

/-- A commit's notification of a target is undelivered. -/
abbrev CommitOpen (X : Execution) : Prop :=
  ¬ ∀ i s rank m', X.Commit i s → TcCommit.target s rank = some m' → rank ∈ X.tcNotified i

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none)

include hp hX hff in
/-- A commit object's committing lane is short of the final phase, or a commit is open. -/
theorem commit_short {l : Loc} {c δ : Nat} (O : Notify.Obj X l c l δ) {st : MBarrier.State}
    (hst : Final X l st) : (X.tr c).countP (commitsTo l) ≤ st.phase ∨ CommitOpen X := by
  by_cases hall : ∀ i s rank m', X.Commit i s → TcCommit.target s rank = some m' →
      rank ∈ X.tcNotified i
  · exact .inl (Notify.Obj.phase_ge_of_records hX O hst le_rfl fun _ ht =>
      Notify.Obj.notified_rec hX (hff l) (fun he hm => by
        have h := commit_self hp hX he
        rwa [hm] at h) hall ht)
  · exact .inr hall

include hp hX hff
include hFw

/-- **S-full**: a softmax lane of the stage. -/
theorem s_blocked (g : Nat) (st : Fin 2) : ∃ c, ∀ {h : Nat} {f : MBarrier.State},
    SoftIn L g st.val h → Final X (obj L g (80 + 8 * st.val)) f →
    f.phase % 2 = okPolls (obj L g (80 + 8 * st.val)) (X.tr h) % 2 →
    f.phase = okPolls (obj L g (80 + 8 * st.val)) (X.tr h) ∧
      ((X.tr c).countP (commitsTo (obj L g (80 + 8 * st.val))) ≤ f.phase ∨ CommitOpen X) := by
  obtain ⟨c, O⟩ := sNotify hp hX hFw g st
  refine ⟨c, fun {h f} hh hst hpar => ⟨?_, commit_short hp hX hff O hst⟩⟩
  have h1 := O.phase_le hX (sReach hp hX hFw O hh) hst
  have h2 := okPolls_le_phase (g := h) hX (Nat.zero_le 1)
    (PairTmaRing.poll_clean hX O.init O.noInval) O.noInval
    (fun k pc q acq sc he => O.parity he) hst
  omega

/-- **P-full**: an MMA lane. -/
theorem p_blocked (g : Nat) (st : Fin 2) {h : Nat} (hh : MmaIn L g h) {f : MBarrier.State}
    (hst : Final X (obj L g (96 + 8 * st.val)) f)
    (hpar : f.phase % 2 = okPolls (obj L g (96 + 8 * st.val)) (X.tr h) % 2) :
    f.phase = okPolls (obj L g (96 + 8 * st.val)) (X.tr h) ∧
      ∃ a, arrivals (obj L g (96 + 8 * st.val)) (X.tr (pLane L (g / L.block) st.val a)) ≤
        f.phase :=
  (pObj hp hX hFw g st).reach_short hX (pReach hp hX hFw g st hh) (hff _) hst (Nat.zero_le _) hpar

/-- **Second P**: an MMA lane. -/
theorem p2_blocked (g : Nat) (st : Fin 2) {h : Nat} (hh : MmaIn L g h) {f : MBarrier.State}
    (hst : Final X (obj L g (112 + 8 * st.val)) f)
    (hpar : f.phase % 2 = okPolls (obj L g (112 + 8 * st.val)) (X.tr h) % 2) :
    f.phase = okPolls (obj L g (112 + 8 * st.val)) (X.tr h) ∧
      ∃ a, arrivals (obj L g (112 + 8 * st.val)) (X.tr (p2Prod L X g st.val a)) ≤ f.phase :=
  (p2Obj hp hX hFw g st).reach_short hX (p2Reach hp hX hFw g st hh) (hff _) hst (Nat.zero_le _)
    hpar

/-- **Credit**: a softmax lane of the stage. -/
theorem credit_blocked (g : Nat) (st : Fin 2) {h : Nat} (hh : SoftIn L g st.val h)
    {f : MBarrier.State} (hst : Final X (obj L g (192 + 8 * st.val)) f)
    (hpar : f.phase % 2 = (okPolls (obj L g (192 + 8 * st.val)) (X.tr h) + 1) % 2) :
    f.phase + 1 = okPolls (obj L g (192 + 8 * st.val)) (X.tr h) ∧
      ∃ a, arrivals (obj L g (192 + 8 * st.val)) (X.tr (corrLane L (g / L.block) a)) ≤
        f.phase := by
  obtain ⟨h1, -⟩ := (creditGate hp hX hFw g st).blocked hX hh hst hpar
  obtain ⟨a, ha⟩ := (creditGate hp hX hFw g st).toObj.blocked hX hst
  exact ⟨h1, a, (Unit.arrivals_le_unitRec hX (hff _) _).trans ha⟩

/-- **Free**: any lane whose poll is not its first. -/
theorem free_blocked (g : Nat) (st : Fin 2) {h : Nat} {f : MBarrier.State}
    (hst : Final X (obj L g (224 + 8 * st.val)) f)
    (h1 : 1 ≤ okPolls (obj L g (224 + 8 * st.val)) (X.tr h))
    (hpar : f.phase % 2 = (okPolls (obj L g (224 + 8 * st.val)) (X.tr h) + 1) % 2) :
    f.phase + 1 = okPolls (obj L g (224 + 8 * st.val)) (X.tr h) ∧
      ∃ a, arrivals (obj L g (224 + 8 * st.val)) (X.tr (outLane L (g / L.block) a)) ≤ f.phase :=
  (freeObj hp hX hFw g st).reach_short hX (freeReach hp hX hFw g st h) (hff _) hst h1 hpar

/-- **K/V empty**: a loader lane. -/
theorem kvE_blocked (g : Nat) (hg : g < L.threads) (s : Fin 3) {h : Nat} (hh : LdLane L g h)
    {f : MBarrier.State} (hst : Final X (kvE L g s) f)
    (hpar : f.phase % 2 = (okPolls (kvE L g s) (X.tr h) + 1) % 2) :
    f.phase + 1 = okPolls (kvE L g s) (X.tr h) ∧
      ((X.tr (commitLane L X g (56 + 8 * s.val))).countP (commitsTo (kvE L g s)) ≤ f.phase ∨
        CommitOpen X) := by
  obtain ⟨a, rfl⟩ := ldLane_prod hh
  have N := kvNotify hp hX hFw g s
  refine ⟨(kvRing hp hX hFw g hg s).E_phase hX a hst ?_ hpar, commit_short hp hX hff N hst⟩
  refine (kvRing hp hX hFw g hg s).E_phase_le hX (by decide) N.init
    (fun r hr ha => ?_) (fun hr _ ha => (N.arrive_rec hr ha).1) (fun hr hf ha => ?_) a hst
  · cases N.src r hr with
    | init ha' | poll _ _ ha' | commit _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  · obtain ⟨x, hx, hid⟩ := N.rec_S hr hf ha
    exact ⟨x, hx, hid⟩

/-- **Q empty**: the lane of warp 14 that feeds the stage. -/
theorem qE_blocked (hB : TmaBytes X) (g : Nat) (hg : g < L.threads) (s : Fin 2)
    {f : MBarrier.State} (hst : Final X (qE L g s) f)
    (hpar : f.phase % 2 = (okPolls (qE L g s) (X.tr (tmaLane L X g)) + 1) % 2) :
    f.phase + 1 = okPolls (qE L g s) (X.tr (tmaLane L X g)) ∧
      ((X.tr (qCons L X g s)).countP (commitsTo (qE L g s)) ≤ f.phase ∨ CommitOpen X) := by
  have N := qNotify hp hX hFw g s
  refine ⟨(qRing hp hX hFw hB g hg s).E_phase hX 0 hst ?_ hpar, commit_short hp hX hff N hst⟩
  refine (qRing hp hX hFw hB g hg s).E_phase_le hX (by decide) N.init
    (fun r hr ha => ?_) (fun hr _ ha => (N.arrive_rec hr ha).1) (fun hr hf ha => ?_) 0 hst
  · cases N.src r hr with
    | init ha' | poll _ _ ha' | commit _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  · obtain ⟨x, hx, hid⟩ := N.rec_S hr hf ha
    exact ⟨x, hx, hid⟩

/-- **Bias empty**: the lane of warp 14 that feeds the stage. -/
theorem bE_blocked (hB : TmaBytes X) (g : Nat) (st : Fin 2) {f : MBarrier.State}
    (hst : Final X (bE L g st) f)
    (hpar : f.phase % 2 = (okPolls (bE L g st) (X.tr (tmaLane L X g)) + 1) % 2) :
    f.phase + 1 = okPolls (bE L g st) (X.tr (tmaLane L X g)) ∧
      ∃ b, arrivals (bE L g st) (X.tr (biasLane L (g / L.block) st.val b)) ≤ f.phase := by
  have N := biasFreeHist hp hX hFw g st
  have O : Unit.Obj X (bE L g st) 4 (biasLane L (g / L.block) st.val) 1 :=
    { pos := N.pos, inj := N.inj, src := N.src, init := N.init, noInval := N.noInval
      parity := fun {h k pc par acq sc} he => by
        rcases biasFree_use hp hX hFw st he rfl (fun _ h => by cases h) with
          ⟨⟨hc, hw⟩, _⟩ | ⟨hk, _⟩
        · rw [← bE_eq] at he ⊢
          rw [← obj_cta hc] at he ⊢
          exact (ld_tma_empty_par hp hX hFw hw (b_tmaOff st) he).2
        · cases hk
      δ_le := le_rfl }
  refine ⟨(biasRing hp hX hFw hB g st).E_phase hX 0 hst ?_ hpar, ?_⟩
  · refine (biasRing hp hX hFw hB g st).E_phase_le hX (by decide) N.init
      (fun r hr ha => ?_) (fun hr _ ha => (N.arrive_rec hr ha).1) (fun hr hf ha => ?_) 0 hst
    · cases N.src r hr with
      | init ha' | poll _ _ ha' | arrive _ _ _ ha' => rw [ha] at ha'; cases ha'
    · obtain ⟨x, hx, hid⟩ := N.rec_S hr hf ha
      exact ⟨x, hx, hid⟩
  · obtain ⟨b, hb⟩ := O.blocked hX hst
    exact ⟨b, (Unit.arrivals_le_unitRec hX (hff _) _).trans hb⟩

/-- **K/V full**: the committing lane of the slot. -/
theorem kvF_blocked (g : Nat) (hg : g < L.threads) (s : Fin 3) {f : MBarrier.State}
    (hst : Final X (kvF L g s) f)
    (hpar : f.phase % 2 =
      okPolls (kvF L g s) (X.tr (commitLane L X g (56 + 8 * s.val))) % 2) :
    f.phase = okPolls (kvF L g s) (X.tr (commitLane L X g (56 + 8 * s.val))) ∧
      (Descent.Obl L X .arriveOn ∨
        ∃ a, (X.tr (ldProd L g a)).countP (arriveOnTo (kvF L g s)) ≤ f.phase) := by
  have hs := s.isLt
  have hoF : KvOff (32 + 8 * s.val) := by unfold KvOff; omega
  have o : NoIncObject X (kvF L g s) 64 := kvObj hp hX hFw hoF g
  have hsrc := kv_src (g := g) hp hX hFw hoF
  refine ⟨(kvRing hp hX hFw g hg s).F_phase hX 0 hst ?_ hpar, ?_⟩
  · refine (kvRing hp hX hFw g hg s).F_phase_le hX (κ := Finset.univ) (by simp)
      (by rw [Finset.card_univ, Fintype.card_fin]; exact o.init) (fun r hr ha => ?_)
      (fun hr _ ha => (o.arrive_source hr ha).1) (fun hr hf ha => ?_) 0 hst
    · cases o.source r hr with
      | init h | poll h | arriveOn _ _ _ h => rw [ha] at h; cases h
    · obtain ⟨x, hx, hid⟩ := NoInc.rec_S o hsrc hr hf ha
      exact ⟨x, hx, Finset.mem_univ _, hid⟩
  · by_cases hob : Descent.Obl L X .arriveOn
    · exact .inl hob
    · obtain ⟨a, ha⟩ := o.blocked hX (ldProd_inj L g) hst
      exact .inr ⟨a, (arr_recorded hX hob (hff _) _).trans ha⟩

/-- **Q full**: the committing lane of the stage. -/
theorem qF_blocked (hB : TmaBytes X) (g : Nat) (hg : g < L.threads) (s : Fin 2)
    {f : MBarrier.State} (hst : Final X (qF L g s) f)
    (hpar : f.phase % 2 = okPolls (qF L g s) (X.tr (qCons L X g s)) % 2) :
    f.phase = okPolls (qF L g s) (X.tr (qCons L X g s)) ∧
      (Descent.Obl L X .tensor ∨ arrivals (qF L g s) (X.tr (tmaLane L X g)) ≤ f.phase ∨
        (X.tr (tmaLane L X g)).countP (issuesTo (qF L g s)) < 2 * (f.phase + 1)) := by
  have o := tmaFull hp hX hFw hB g (q_tmaOff s)
  have hph : f.phase = okPolls (qF L g s) (X.tr (qCons L X g s)) := by
    refine (qRing hp hX hFw hB g hg s).F_phase hX 0 hst ?_ hpar
    exact (qRing hp hX hFw hB g hg s).F_phase_le hX (κ := {0}) (by simp)
      (by rw [Finset.card_singleton]; exact o.init) o.incr o.one (o.rec_zero (by decide)) 0 hst
  refine ⟨hph, ?_⟩
  by_cases hob : Descent.Obl L X .tensor
  · exact .inl hob
  · exact .inr (o.short hX (by decide) (hff _) hob hst fun x hx => by
      rw [hph]; exact (qRing hp hX hFw hB g hg s).F_use hX hx 0)

/-- **Bias full**: lane 0 of a softmax warp of the stage. -/
theorem bF_blocked (hB : TmaBytes X) (g : Nat) (st : Fin 2) (b : Fin 4) {f : MBarrier.State}
    (hst : Final X (bF L g st) f)
    (hpar : f.phase % 2 = okPolls (bF L g st) (X.tr (biasLane L (g / L.block) st.val b)) % 2) :
    f.phase = okPolls (bF L g st) (X.tr (biasLane L (g / L.block) st.val b)) ∧
      (Descent.Obl L X .tensor ∨ arrivals (bF L g st) (X.tr (tmaLane L X g)) ≤ f.phase ∨
        (X.tr (tmaLane L X g)).countP (issuesTo (bF L g st)) < 2 * (f.phase + 1)) := by
  have o := tmaFull hp hX hFw hB g (b_tmaOff st)
  have hph : f.phase = okPolls (bF L g st) (X.tr (biasLane L (g / L.block) st.val b)) := by
    refine (biasRing hp hX hFw hB g st).F_phase hX b hst ?_ hpar
    exact (biasRing hp hX hFw hB g st).F_phase_le hX (κ := {0}) (by simp)
      (by rw [Finset.card_singleton]; exact o.init) o.incr o.one (o.rec_zero (by decide)) b hst
  refine ⟨hph, ?_⟩
  by_cases hob : Descent.Obl L X .tensor
  · exact .inl hob
  · exact .inr (o.short hX (by decide) (hff _) hob hst fun x hx => by
      rw [hph]; exact (biasRing hp hX hFw hB g st).F_use hX hx b)

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
