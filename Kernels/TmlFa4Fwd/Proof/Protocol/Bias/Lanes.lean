-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Stage
import Lemmas.Protocol.MultiObs
import Lemmas.Protocol.ReachJoint
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every softmax lane's bias polls

A copy of round `s` follows every stage lane's polls of the rounds before `s` (`bias_reach`): the
loader's poll of the empty barrier observes lane 0's release, which follows the stage barrier. So
the lane's poll with `u` earlier ones observes the copies of round `u` (`bias_observes`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- Lane 0's release of round `j`, observed by the loader's poll of the next round, and the
stage-barrier event of any stage lane it follows. -/
theorem bias_release (hB : TmaBytes X) {st : Fin 2} {h : Nat} (hh : SoftIn L g st.val h) {j : Nat}
    (hj : j + 1 < okPolls (bE L g st) (X.tr (tmaLane L X g))) :
    ∃ y z pcz i pci a pca sca, y / L.block = g / L.block ∧
      X.get (y, z) = some ⟨pcz, .bar (stageId st.val) (some 128) .sync⟩ ∧ z < a ∧
      X.get (y, a) = some ⟨pca, .arrive (bE L g st) 0 1 true sca⟩ ∧
      arrivals (bE L g st) ((X.tr y).take a) = j ∧
      X.get (h, i) = some ⟨pci, .bar (stageId st.val) (some 128) .sync⟩ ∧
      barOrd X h i (stageId st.val) = j ∧ barOrd X y z (stageId st.val) = j ∧
      Witness L X (.thread (h, i)) (y, z) ∧
      Witness L X (.thread (y, a)) (tmaLane L X g, Poll.nth X (bE L g st) (tmaLane L X g) (j + 1)) ∧
      MBarrier.UpdateBeforeWait (X.objects (bE L g st)) (.thread (y, a))
        (.thread (tmaLane L X g, Poll.nth X (bE L g st) (tmaLane L X g) (j + 1))) := by
  have hst := st.isLt
  have N := biasFreeHist hp hX hFw g st
  set R := biasRing hp hX hFw hB g st with hR
  obtain ⟨hS, hph⟩ := ((R.ring hX).content_empty hX.depAcyclic (a := 0) (n := j)
    (Poll.nth_present.mpr hj)).2 0
  have hwit := R.cE.observed hX le_rfl (R.altE hX 0) (show 1 ≤ j + 1 by omega) hj hS hph
  have hubw := R.cE.ubw hX le_rfl (R.altE hX 0) (show 1 ≤ j + 1 by omega) hj hS hph
  obtain ⟨-, ⟨pca, sca, hget⟩, hcnt⟩ := N.S_rec hS
  change Witness L X (.thread (Unit.it X (bE L g st) (biasLane L (g / L.block) st.val) 0 j))
    (tmaLane L X g, Poll.nth X (bE L g st) (tmaLane L X g) (j + 1)) at hwit
  change MBarrier.UpdateBeforeWait _
    (Ref.thread (Unit.it X (bE L g st) (biasLane L (g / L.block) st.val) 0 j))
    (Ref.thread (tmaLane L X g, Poll.nth X (bE L g st) (tmaLane L X g) (j + 1))) at hubw
  set y := biasLane L (g / L.block) st.val 0 with hy
  obtain ⟨a, ha⟩ : ∃ a, Unit.it X (bE L g st) (biasLane L (g / L.block) st.val) 0 j = (y, a) :=
    ⟨_, rfl⟩
  change X.get (Unit.it X (bE L g st) (biasLane L (g / L.block) st.val) 0 j) = _ at hget
  change arrivals _ ((X.tr y).take
    (Unit.it X (bE L g st) (biasLane L (g / L.block) st.val) 0 j).2) = j at hcnt
  rw [ha] at hget hcnt hwit hubw
  have hb := hp.block
  have hyc : y / L.block = g / L.block := by
    simp only [hy, biasLane, hb]
    have : ((0 : Fin 4) : Nat) = 0 := rfl
    omega
  have hyw : Prologue.warpIndex L y = 4 * st.val := by
    simp only [hy, biasLane, Prologue.warpIndex, hb]
    have : ((0 : Fin 4) : Nat) = 0 := rfl
    omega
  have hso : ∀ b, sobj L y b = obj L g (b + 8 * st.val) := fun b => by
    rw [sobj, obj_cta hyc]; congr 1; omega
  have hget' : X.get (y, a) = some ⟨pca, .arrive (sobj L y 336) 0 1 true sca⟩ := by
    rw [hso]; exact hget
  have hstg := soft_free_stage hp hX hFw (by omega) hget'
  rw [show Prologue.warpIndex L y / 4 = st.val by omega, hso, hcnt] at hstg
  obtain ⟨z, pcz, cntz, mz, hza, hz, hzo⟩ := exists_bar (X := X) (g := y) (x := a)
    (c := j) (id := stageId st.val) (show _ ≤ barOrd X y a _ from hstg.ge)
  obtain ⟨-, -, rfl, rfl, -⟩ := stage_of_bar hp hX hFw hst hz
  have hpass : z + 1 < (X.tr y).length := by
    have := len_of_get hget
    simp only at this
    omega
  obtain ⟨i, pci, hi, hord, hw⟩ := stage_rendezvous hp hX hFw hz hpass hh hyc.symm
  exact ⟨y, z, pcz, i, pci, a, pca, sca, hyc, hz, hza, hget, hcnt, hi, hord.trans hzo, hzo, hw,
    hwit, hubw⟩

/-- A stage lane's poll `j` precedes its stage-barrier event `j`. -/
theorem bias_poll_before {st : Fin 2} {h i pci j : Nat} (hh : SoftIn L g st.val h)
    (hi : X.get (h, i) = some ⟨pci, .bar (stageId st.val) (some 128) .sync⟩)
    (ho : barOrd X h i (stageId st.val) = j) :
    okPolls (bF L g st) ((X.tr h).take i) = j + 1 := by
  obtain ⟨-, hcta, -, hstage⟩ := hh
  obtain ⟨-, -, -, -, h1, -⟩ := stage_of_bar hp hX hFw st.isLt hi
  have hso : sobj L h 320 = bF L g st := by
    rw [sobj, obj_cta hcta, hstage]
    simp only [bF]
    congr 1
    omega
  rw [hso, ho] at h1
  exact h1

/-- **A copy of round `s` follows every stage lane's polls of the earlier rounds.** -/
theorem bias_reach (hB : TmaBytes X) {st : Fin 2} {h : Nat} (hh : SoftIn L g st.val h)
    {x : Fin 3 × Nat} (hx : x ∈ (biasRing hp hX hFw hB g st).SF) {j : Nat} (hj : j < x.2) :
    Relation.TransGen (DepStep L kernel X) (.thread (h, Poll.nth X (bF L g st) h j), true)
      ((biasRing hp hX hFw hB g st).itF x.1 x.2, false) := by
  have hiss := (biasRing hp hX hFw hB g st).issueF x hx
  obtain ⟨k, hop, hk, hpol⟩ := (biasRing hp hX hFw hB g st).polF x hx
  change k < (X.tr (tmaLane L X g)).length at hk
  change x.2 + 1 ≤ okPolls (bE L g st) ((X.tr (tmaLane L X g)).take k) at hpol
  change (biasRing hp hX hFw hB g st).opF x.1 x.2 = (tmaLane L X g, k) at hop
  rw [hop] at hiss
  have hlt : j + 1 < okPolls (bE L g st) (X.tr (tmaLane L X g)) := by
    have := Poll.okPolls_mono (bE L g st) (X.tr (tmaLane L X g)) hk.le
    rw [List.take_of_length_le le_rfl] at this
    omega
  obtain ⟨y, z, pcz, i, pci, a, pca, sca, -, hz, hza, ha, -, hi, hio, -, hw1, hw2, -⟩ :=
    bias_release hp hX hFw hB hh hlt
  have hpb := bias_poll_before hp hX hFw hh hi hio
  have g1 := Poll.guard (K := kernel) (m := bF L g st) (poll_spin hX) (g := h) (k := i)
    (len_of_get hi) (n := j) (by omega)
  have g2 : Resumes kernel X (y, z) (y, a) :=
    Resumes.of_blocking hz (b := false) rfl ⟨rfl, hza, len_of_get ha⟩
  have g3 := Poll.guard (K := kernel) (m := bE L g st) (poll_spin hX) hk (n := j + 1) (by omega)
  exact ((((((Relation.TransGen.single (DepStep.of_resumes L g1)).tail
    (DepStep.of_witness L hw1)).tail (DepStep.of_resumes L g2)).tail
    (DepStep.of_witness L hw2)).tail (DepStep.of_resumes L g3))).trans_left hiss

/-- **Every stage lane's bias poll observes its round's items.** -/
theorem bias_content (hB : TmaBytes X) {st : Fin 2} {h : Nat} (hh : SoftIn L g st.val h) {u : Nat}
    (hu : u < okPolls (bF L g st) (X.tr h)) (k : Fin 3) :
    (k, u) ∈ (biasRing hp hX hFw hB g st).SF ∧
      MBarrier.UpdateBeforeWait (X.objects (bF L g st)) ((biasRing hp hX hFw hB g st).itF k u)
        (.thread (h, Poll.nth X (bF L g st) h u)) := by
  classical
  have o := tmaFull hp hX hFw hB g (b_tmaOff st)
  have hpar : ∀ {k pc par : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait (bF L g st) par true acq sc⟩ →
      par % 2 = (okPolls (bF L g st) ((X.tr h).take k) + 0) % 2 := by
    intro k pc par acq sc he
    obtain ⟨-, hu⟩ := bias_use hp hX hFw st he rfl (fun _ h => by cases h)
    rcases hu with ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, _, hk, _⟩
    · simp only [Kind.wait.injEq] at hk
      simp only [bF]
      omega
    · cases hk
    · cases hk
  have hAlt := o.counted.alt hX (g := h) (δ := 0) hpar
  have hlt' : ∀ {n}, n ≤ u → n < okPolls (bF L g st) (X.tr h) := fun hn => by omega
  have key := Items.content (TmaUnits.S X (bF L g st) (tmaLane L X g) 2 16384)
    (Counted.ph X (bF L g st) (TmaUnits.it X (bF L g st) (tmaLane L X g) 2))
    (Unit.obsOf X (bF L g st) h) u
    (fun j j' hjj hj' => o.counted.lt hX (Nat.zero_le 1) hAlt (Nat.zero_le _) hjj (hlt' hj'))
    (fun j hj => by
      rw [Fintype.card_fin]
      exact o.card_phase hX (by decide) (by decide) (Nat.zero_le 1) hAlt (Nat.zero_le _) (hlt' hj))
    (fun j hj x hx hph => by
      by_contra hgt
      have hr := bias_reach hp hX hFw hB hh (x := x) hx (j := j) (by omega)
      have hw := o.counted.observed (L := L) hX (Nat.zero_le 1) hAlt (Nat.zero_le _) (hlt' hj) hx
        hph
      exact hX.depAcyclic _ (hr.tail (DepStep.of_witness L hw))) u le_rfl
  obtain ⟨hS, hph⟩ := key.2 k
  exact ⟨hS, o.counted.ubw hX (Nat.zero_le 1) hAlt (Nat.zero_le _) hu hS hph⟩

/-- **The bias hand-off of every stage lane**: its poll of the full barrier with `u` earlier ones
observes the copies `2 u`, `2 u + 1` on it. -/
theorem bias_observes (hB : TmaBytes X) {st : Fin 2} {h : Nat} (hh : SoftIn L g st.val h)
    {j pc par u : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (bF L g st) par true acq sc⟩)
    (hu : okPolls (bF L g st) ((X.tr h).take j) = u) (a : Fin 2) :
    ∃ i pci al sp, X.get (tmaLane L X g, i) = some ⟨pci, .tensorIssue al sp⟩ ∧
      sp.mbar = bF L g st ∧
      ((X.tr (tmaLane L X g)).take i).countP (issuesTo (bF L g st)) = 2 * u + a.val ∧
      u + 1 ≤ okPolls (bE L g st) ((X.tr (tmaLane L X g)).take i) ∧
      WaitObserves X (.async (tmaLane L X g, i) (.notify .load)) (h, j) (bF L g st) acq sc := by
  have o := tmaFull hp hX hFw hB g (b_tmaOff st)
  have hlt : u < okPolls (bF L g st) (X.tr h) := by
    rw [← hu]; exact PairTmaRing.okPolls_lt_of_get he
  obtain ⟨hS, hub⟩ := bias_content hp hX hFw hB hh hlt a.succ
  obtain ⟨-, -, h1⟩ := o.source hS
  obtain ⟨⟨pci, al, sp, hget, hm⟩, hcnt⟩ := h1 (by simp)
  obtain ⟨i, hi, -, hpol⟩ := tmaFull_pol hp hX hFw hB g (b_tmaOff st) hS
  rw [hi] at hget hcnt
  rw [bE_eq] at hpol
  change MBarrier.UpdateBeforeWait _ (TmaUnits.it X (bF L g st) (tmaLane L X g) 2 a.succ u)
    (Ref.thread (h, Poll.nth X (bF L g st) h u)) at hub
  rw [show Poll.nth X (bF L g st) h u = j by
    rw [← hu]; exact Poll.nth_eq he,
    show TmaUnits.it X (bF L g st) (tmaLane L X g) 2 a.succ u =
      .async (tmaLane L X g, i) (.notify .load) by
    simp only [TmaUnits.it, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ↓reduceIte]
    rw [← hi]] at hub
  exact ⟨i, pci, al, sp, hget, hm, by simpa using hcnt, hpol, ⟨⟨pc, par, he⟩, hub⟩⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
