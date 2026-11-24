-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.P.Obj
public import Kernels.TmlFa4Fwd.Proof.Protocol.S.Notify
public import Lemmas.Protocol.ReachJoint
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Observed
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The reuse paths of the S-full and P barriers

One stage's S-full, P-full and second P barriers of a CTA wait on each other, so their reuse paths
are proved together along the dependency order (`MbarRing.Reach.joint`):

* **S-full** (`stepS`): the notification of commit `t` follows each softmax lane's poll `j < t`: the
  commit follows its lane's P-full polls of phases below `t` (`mma_s_commit`), which observe the
  softmax lane's P-full arrival `j`, which follows its S-full poll `j` (`soft_p_arr`).
* **From an MMA lane's poll to a softmax event** (`soft_reach`): a softmax event after `j + 2`
  S-full polls follows every MMA lane's polls `j` of both P barriers: the softmax poll `j + 1`
  observes commit `j + 1`, which follows an election at which every lane of warp 12 has those
  polls (`lane_to_commit`).
* **P-full** (`stepP`): a softmax arrival `t` follows `t + 1` S-full polls. A correction arrival
  `t ≥ 1` is a rescale round's, after its named-barrier wait whose softmax arrival follows `t + 1`
  S-full polls (`stat_rendezvous`), or the last, after its final O poll, whose commit follows an
  election at which every MMA lane has made all its P-full polls (`mma_o_commit`).
* **second P** (`stepP2`): a softmax arrival `t` follows `t + 1` S-full polls (`soft_p2_arr`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The goals at a node**: the reuse paths of stage `st`'s P-full, second P and S-full barriers of
lane `g`'s CTA that end there (`c`: the lane that commits to S-full). -/
structure ReachAt (L : Launch) (X : Execution) (g c : Nat) (st : Fin 2) (n : Ref × Bool) :
    Prop where
  p : ∀ h, MmaIn L g h → Reach.UnitAt L kernel X (obj L g (96 + 8 * st.val)) 256
    (pLane L (g / L.block) st.val) 0 h n
  p2 : ∀ h, MmaIn L g h → Reach.UnitAt L kernel X (obj L g (112 + 8 * st.val)) 4
    (p2Prod L X g st.val) 0 h n
  s : ∀ h, SoftIn L g st.val h → Reach.NotifyAt L kernel X (obj L g (80 + 8 * st.val)) c
    (obj L g (80 + 8 * st.val)) 0 h n

/-- The goals at the earlier nodes. -/
def ReachIH (L : Launch) (X : Execution) (g c : Nat) (st : Fin 2) (n : Ref × Bool) : Prop :=
  ∀ n' ∈ Reach.nodes L X, Relation.TransGen (DepStep L kernel X) n' n → ReachAt L X g c st n'

theorem poll_lt {g k n : Nat} {m : Loc} (hk : k < (X.tr g).length)
    (h : n + 1 ≤ okPolls m ((X.tr g).take k)) : n < okPolls m (X.tr g) := by
  have := MbarRing.Poll.okPolls_mono m (X.tr g) hk.le
  rw [List.take_of_length_le (le_refl _)] at this
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

omit hp hFw in
/-- **Lane to commit**: an MMA lane has an election of the same ordinal as the committing lane's,
before every later event of the committing lane. -/
theorem lane_to_commit {Y k j h pc mask inst ld : Nat} (hY : MmaIn L g Y) (hh : MmaIn L g h)
    (hel : X.get (Y, j) = some ⟨pc, .elect mask inst ld⟩) (hjk : j < k)
    (hk : k < (X.tr Y).length) :
    SameWarp L Y h ∧ ∃ e pce maske inste lde, X.get (h, e) = some ⟨pce, .elect maske inste lde⟩ ∧
      ((X.tr h).take e).countP isElectEv = ((X.tr Y).take j).countP isElectEv ∧
      Relation.TransGen (DepStep L kernel X) (.thread (h, e), false) (.thread (Y, k), false) := by
  have hw : SameWarp L Y h := ⟨⟨hY.1, hh.1, hY.2.1.trans hh.2.1.symm⟩, by
    have h1 := hY.2.2
    have h2 := hh.2.2
    simp only [Prologue.warpIndex] at h1 h2
    omega⟩
  refine ⟨hw, ?_⟩
  have hel' : X.Elect (Y, j) pc mask inst ld := hel
  have hmask := elect_full hX hel'
  subst hmask
  obtain ⟨e, pc0, pc', mask0, mask', inst', l0, l', hel0, hel1⟩ :=
    ElectOrd.partner hX hw hel' (electMember_full (Nat.mod_lt _ (by decide)))
  have hinst : inst = inst' := by
    have h0 : X.get (Y, j) = some ⟨pc0, .elect mask0 inst' l0⟩ := hel0
    rw [hel] at h0
    simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at h0
    exact h0.2.2.1
  subst hinst
  exact ⟨e, pc', mask', inst, l', hel1, (elect_ordinal hX hw hel' hel1).symm,
    elect_depStep hX (sameWarp_symm hw) hel1 hel' hjk hk⟩

/-- **The content of a softmax lane's S-full poll** that precedes `n`. -/
theorem s_content {c : Nat} {st : Fin 2}
    (O : Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0)
    {n : Ref × Bool} (ih : ReachIH L X g c st n) {h J : Nat} (hh : SoftIn L g st.val h)
    (hJ : J < okPolls (obj L g (80 + 8 * st.val)) (X.tr h))
    (hpath : Relation.TransGen (DepStep L kernel X)
      (.thread (h, Poll.nth X (obj L g (80 + 8 * st.val)) h J), true) n) :
    MmaIn L g c ∧ ∃ i pc s rank, X.get (c, i) = some ⟨pc, .tc (.commit s)⟩ ∧
      s.mbar = obj L g (80 + 8 * st.val) ∧
      ((X.tr c).take i).countP (commitsTo (obj L g (80 + 8 * st.val))) = J ∧
      rank ∈ X.tcNotified (c, i) ∧
      Witness L X (.async (c, i) (.tcNotify rank))
        (h, Poll.nth X (obj L g (80 + 8 * st.val)) h J) := by
  obtain ⟨hS, hobs⟩ := Reach.notify_content hX O (poll_spin hX) (h := h) (J := J) (by omega)
    hpath (fun n' hn' hlt => (ih n' hn' hlt).s h hh)
  obtain ⟨⟨kr, r, hk, hid, -, -⟩, pc, s, hget, hb, ht, hc⟩ := O.S_rec hS
  obtain ⟨-, -, -, -, hr⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
  obtain ⟨hl, hcta, hw, -, -⟩ := mma_commit_of hp hX hFw hget ht
  exact ⟨⟨hl, hcta, hw⟩, _, pc, s, _, hget, hb, hc, hr, hobs⟩

/-- **The elections before an S-full commit**, at the lanes of the warp. -/
theorem s_commit_lane {Y k j h pc : Nat} {s : TcCommit.Spec} {st : Fin 2} (hY : MmaIn L g Y)
    (hh : MmaIn L g h) (he : X.get (Y, k) = some ⟨pc, .tc (.commit s)⟩)
    (hb : s.mbar = obj L g (80 + 8 * st.val))
    (hj : j < ((X.tr Y).take k).countP (commitsTo (obj L g (80 + 8 * st.val)))) :
    Relation.TransGen (DepStep L kernel X)
        (.thread (h, Poll.nth X (obj L g (96 + 8 * st.val)) h j), true) (.thread (Y, k), false) ∧
      Relation.TransGen (DepStep L kernel X)
        (.thread (h, Poll.nth X (obj L g (112 + 8 * st.val)) h j), true)
        (.thread (Y, k), false) := by
  have ho := fun o => obj_cta (L := L) hY.2.1 o
  rw [← ho] at hb hj
  obtain ⟨j', pce, mask, inst, ld, hj', hel, hall⟩ := mma_s_commit hp hX hFw st hY.2.2 he hb
  obtain ⟨hw, e, pe, me, ie, le, hle, hcnt, hpath⟩ :=
    lane_to_commit hX hY hh hel hj' (len_of_get he)
  obtain ⟨h1, h2⟩ := hall h hw e pe me ie le hle hcnt
  have ho' := fun o => obj_cta (L := L) hh.2.1 o
  rw [ho'] at h1 h2
  have hl : e < (X.tr h).length := len_of_get hle
  exact ⟨.head (Reach.poll_guard (poll_spin hX) hl (by omega)) hpath,
    .head (Reach.poll_guard (poll_spin hX) hl (by omega)) hpath⟩

/-- **From an MMA lane's poll to a softmax event.** -/
theorem soft_reach {c : Nat} {st : Fin 2}
    (O : Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0)
    {n : Ref × Bool} (ih : ReachIH L X g c st n) {h0 h e j : Nat} (h0c : MmaIn L g h0)
    (hh : SoftIn L g st.val h) (he : e < (X.tr h).length)
    (hs : j + 2 ≤ okPolls (obj L g (80 + 8 * st.val)) ((X.tr h).take e))
    (hn : Relation.ReflTransGen (DepStep L kernel X) (.thread (h, e), false) n) :
    Relation.TransGen (DepStep L kernel X)
        (.thread (h0, Poll.nth X (obj L g (96 + 8 * st.val)) h0 j), true) n ∧
      Relation.TransGen (DepStep L kernel X)
        (.thread (h0, Poll.nth X (obj L g (112 + 8 * st.val)) h0 j), true) n := by
  have hpoll := (Relation.TransGen.single
    (Reach.poll_guard (K := kernel) (n := j + 1) (poll_spin hX) he hs)).trans_left hn
  obtain ⟨hc, i, pc, s, rank, hget, hb, hcnt, hr, hobs⟩ :=
    s_content hp hX hFw O ih hh (poll_lt he hs) hpoll
  obtain ⟨h1, h2⟩ := s_commit_lane hp hX hFw (st := st) (j := j) hc h0c hget hb (by omega)
  have htail := ((Relation.TransGen.single
    (Reach.commit_notify (K := kernel) (L := L) hget hr)).tail
    (DepStep.of_witness L hobs)).trans hpoll
  exact ⟨h1.trans htail, h2.trans htail⟩

omit hp hX hFw in
/-- A softmax lane of the stage has the stage's barriers. -/
theorem soft_obj_eq {st : Fin 2} {h : Nat} (hh : SoftIn L g st.val h) (a : Nat) :
    sobj L h a = obj L g (a + 8 * st.val) := by
  rw [sobj, hh.2.2.2, obj_cta hh.2.1, Nat.add_comm]

set_option maxRecDepth 20000 in
/-- **The S-full step.** -/
theorem stepS {c : Nat} {st : Fin 2}
    (O : Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0)
    {n : Ref × Bool} (ih : ReachIH L X g c st n) (h : Nat) (hh : SoftIn L g st.val h) :
    Reach.NotifyAt L kernel X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0 h n := by
  intro x hx hn j hj
  subst hn
  obtain ⟨⟨kr, r, hk, hid, -, -⟩, pc, s, hget, hb, ht, hcnt⟩ := O.S_rec hx
  obtain ⟨-, -, -, -, hr⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
  obtain ⟨hl, hcta, hw, -, -⟩ := mma_commit_of hp hX hFw hget ht
  have hc : MmaIn L g c := ⟨hl, hcta, hw⟩
  have hpath := ((s_commit_lane hp hX hFw (st := st) (j := j) hc hc hget hb
    (by omega)).1).tail (Reach.commit_notify (K := kernel) (L := L) hget hr)
  have hJ : j < okPolls (obj L g (96 + 8 * st.val)) (X.tr c) := by
    obtain ⟨z, hz, -⟩ := Relation.TransGen.head'_iff.mp hpath
    have := hz.present_of_return
    exact Poll.nth_present.mp this
  obtain ⟨a, ha⟩ := pLane_of (st := st.val) hp hh.2.1 (.inl hh.2.2)
  have OP := pObj hp hX hFw g st
  obtain ⟨hSP, hobs⟩ := Reach.unit_content hX OP (poll_spin hX) (g := c) (J := j) (by omega)
    hpath (fun n' hn' hlt => (ih n' hn' hlt).p c hc) a
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := OP.S_rec hSP
  have e1 : Unit.it X (obj L g (96 + 8 * st.val)) (pLane L (g / L.block) st.val) a j =
      (h, nthEv X (arrivesOn (obj L g (96 + 8 * st.val))) h j) := by rw [ha]; rfl
  change arrivals _ ((X.tr (pLane L (g / L.block) st.val a)).take
    (Unit.it X (obj L g (96 + 8 * st.val)) (pLane L (g / L.block) st.val) a j).2) = j at harr
  rw [e1] at harr hobs
  change X.get (Unit.it X (obj L g (96 + 8 * st.val)) (pLane L (g / L.block) st.val) a j) = _
    at hga
  rw [e1] at hga
  rw [← ha] at harr
  have hso := soft_obj_eq hh
  rw [← hso] at hga harr
  have hsp := soft_p_arr hp hX hFw hh.2.2.1 hga
  rw [harr, hso] at hsp
  rw [hso] at hga hsp
  exact .head (Reach.poll_guard (poll_spin hX) (len_of_get hga) hsp.ge)
    ((Relation.TransGen.single (DepStep.of_witness L hobs)).trans hpath)

/-- **The P-full step**, at any arrival of a producer. -/
theorem p_arrive_reach {c : Nat} {st : Fin 2}
    (O : Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0)
    {y i pc j h0 : Nat} {sc : MbarScope}
    (ih : ReachIH L X g c st (.thread (y, i), false)) (hh0 : MmaIn L g h0)
    (hga : X.get (y, i) = some ⟨pc, .arrive (obj L g (96 + 8 * st.val)) 0 1 true sc⟩)
    (hj : j < arrivals (obj L g (96 + 8 * st.val)) ((X.tr y).take i)) :
    Relation.TransGen (DepStep L kernel X)
      (.thread (h0, Poll.nth X (obj L g (96 + 8 * st.val)) h0 j), true)
      (.thread (y, i), false) := by
  have hst := st.isLt
  have hylt := Frame.lt_of_get hX hga
  have hlen := len_of_get hga
  simp only at hlen
  obtain ⟨hcy, hw⟩ : y / L.block = g / L.block ∧
      ((Prologue.warpIndex L y < 8 ∧ Prologue.warpIndex L y / 4 = st.val) ∨
        (8 ≤ Prologue.warpIndex L y ∧ Prologue.warpIndex L y ≤ 11)) := by
    rcases p_use hp hX hFw st hga rfl (fun _ h => by cases h) with ⟨hc, ⟨_, _, hk⟩ | ⟨-, hw⟩⟩
    · cases hk
    · exact ⟨hc, hw⟩
  rcases hw with ⟨hw8, hws⟩ | ⟨h8, h11⟩
  · -- a softmax arrival
    have hh : SoftIn L g st.val y := ⟨hylt, hcy, hw8, hws⟩
    have hso := soft_obj_eq hh
    have hga' := hga
    rw [← hso] at hga'
    have hsp := soft_p_arr hp hX hFw hw8 hga'
    rw [hso, hso] at hsp
    exact (soft_reach hp hX hFw O ih hh0 hh hlen (by omega) .refl).1
  · -- a correction arrival
    have hob := fun o => obj_cta (L := L) hcy o
    have hga' := hga
    rw [← hob] at hga'
    rcases corr_p_arr hp hX hFw h8 h11 st hga' with h0 | ⟨hnb, R, hR, hlast⟩
    · rw [hob] at h0
      omega
    rw [hob] at hnb hlast
    set t := arrivals (obj L g (96 + 8 * st.val)) ((X.tr y).take i) with htdef
    rcases hlast with hle | ⟨heq, hopoll⟩
    · -- a rescale round: its named-barrier wait, and the softmax arrival it meets
      have hid : Prologue.warpIndex L y - 5 + 4 * st.val =
          statId st.val (Prologue.warpIndex L y - 8) := by unfold statId; omega
      rw [hid] at hnb
      have hk4 : Prologue.warpIndex L y - 8 < 4 := by omega
      obtain ⟨z, pcz, cntz, mz, hzi, hzget, hzo⟩ := exists_bar (X := X) (g := y) (x := i)
        (id := statId st.val (Prologue.warpIndex L y - 8)) (c := t) hnb.ge
      obtain ⟨rfl, hmz⟩ := stat_of_bar hp hX hFw hk4 hst hzget
      have hmz' : mz = .sync := by
        rcases hmz with ⟨h1, -⟩ | ⟨-, h2⟩
        · omega
        · exact h2
      subst hmz'
      have hb := hp.block
      obtain ⟨h, hch, hwh⟩ : ∃ h, h / L.block = y / L.block ∧
          Prologue.warpIndex L h = Prologue.warpIndex L y - 8 + 4 * st.val := by
        refine ⟨y / L.block * L.block + 32 * (Prologue.warpIndex L y - 8 + 4 * st.val), ?_, ?_⟩ <;>
          simp only [Prologue.warpIndex, hb] at h8 h11 ⊢ <;> omega
      obtain ⟨i', pc', hhget, hord, hwit⟩ := stat_rendezvous hp hX hFw hst hk4 hzget (by omega)
        hch hwh
      have hh : SoftIn L g st.val h := ⟨thread_lt_of_cta hylt hch, hch.trans hcy, by omega,
        by omega⟩
      have hso := soft_obj_eq hh
      have hsp : t + 1 ≤ okPolls (obj L g (80 + 8 * st.val)) ((X.tr h).take i') := by
        rcases soft_bar hp hX hFw hh.2.2.1 hhget with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
          ⟨-, -, -, -, h1⟩
        · unfold statId at h0; omega
        · unfold statId at h0; omega
        · unfold statId at h0; omega
        · have ho : ((X.tr h).take i').countP (Execution.isBarId
              (statId st.val (Prologue.warpIndex L y - 8))) = t := hord.trans hzo
          rw [ho, hso] at h1
          rcases h1 with h1 | ⟨-, hT⟩
          · exact h1.ge
          · have := hT.corr hp hylt hch hR
            omega
      have hl : i' < (X.tr h).length := len_of_get hhget
      refine (soft_reach hp hX hFw O ih hh0 hh hl (by omega) ?_).1
      have g2 : Resumes kernel X (y, z) (y, i) :=
        Resumes.of_blocking hzget (b := false) rfl ⟨rfl, hzi, hlen⟩
      exact ((Relation.TransGen.single (DepStep.of_witness L hwit)).tail
        (DepStep.of_resumes L g2)).to_reflTransGen
    · -- the last arrival: the final O poll
      rw [hob] at hopoll
      obtain ⟨jo, pco, par, acq, sco, hjo, hoget, -⟩ := MbarRing.Poll.exists_nth (X := X)
        (m := obj L g (144 + 8 * st.val)) (g := y) (k := i) (n := 0) (by omega)
      have hzero : okPolls (obj L g (144 + 8 * st.val)) ((X.tr y).take jo) = 0 := by
        have h1 := MbarRing.Poll.okPoll_get hoget
        have h2 := MbarRing.Poll.okPolls_mono (obj L g (144 + 8 * st.val)) (X.tr y)
          (show jo + 1 ≤ i from hjo)
        omega
      have hpar : par = 0 := by
        obtain ⟨-, hu⟩ := bar_use (o := 144 + 8 * st.val) hp hX hFw hoget rfl
          (fun _ h => by cases h)
        cases hu with
        | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
        | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
        | corrPoll ok' _ _ hk =>
          simp only [Kind.wait.injEq] at hk
          have hΔ : corrΔ (144 + 8 * st.val) = 0 := by unfold corrΔ; split <;> omega
          rw [hk.2.1, hzero, hΔ]
        | epiPoll _ _ hw' | softPoll _ _ hw' | mmaPoll _ hw' | ldPoll _ _ hw' => omega
      subst hpar
      obtain ⟨Y, k, pcc, s, rank, hget, hY, hYc, hYw, hYb, hr, -, hwit⟩ :=
        o_handoff hp hX hFw st hoget
      have hYin : MmaIn L g Y := ⟨hY, hYc, hYw⟩
      rw [← obj_cta (L := L) hYc] at hYb
      obtain ⟨-, R', hR', j', pce, mask, inst, ld, hj', hel, hall⟩ :=
        mma_o_commit hp hX hFw st hYw hget hYb
      have hRR : R' = R := ((hR'.cta hYc).cta hcy.symm).unique (hR.mma hp hylt)
      subst hRR
      obtain ⟨hsw, e, pe, me, ie, le, hle, hcnt, hpath⟩ :=
        lane_to_commit hX hYin hh0 hel hj' (len_of_get hget)
      have hP := hall h0 hsw e pe me ie le hle hcnt
      rw [obj_cta hh0.2.1] at hP
      have hl : e < (X.tr h0).length := len_of_get hle
      refine .head (Reach.poll_guard (poll_spin hX) hl (by omega)) ?_
      refine hpath.trans (((Relation.TransGen.single (Reach.commit_notify (K := kernel) (L := L)
        hget hr)).tail (DepStep.of_witness L hwit)).trans (.single ?_))
      have hg1 := Reach.poll_guard (L := L) (K := kernel) (m := obj L g (144 + 8 * st.val)) (n := 0)
        (poll_spin hX) hlen (by omega)
      rwa [show Poll.nth X (obj L g (144 + 8 * st.val)) y 0 = jo by
        rw [← hzero]; exact Poll.nth_eq hoget] at hg1

/-- **The second P step**, at any arrival. -/
theorem p2_arrive_reach {c : Nat} {st : Fin 2}
    (O : Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0)
    {y i pc j h0 : Nat} {sc : MbarScope}
    (ih : ReachIH L X g c st (.thread (y, i), false)) (hh0 : MmaIn L g h0)
    (hga : X.get (y, i) = some ⟨pc, .arrive (obj L g (112 + 8 * st.val)) 0 1 true sc⟩)
    (hj : j < arrivals (obj L g (112 + 8 * st.val)) ((X.tr y).take i)) :
    Relation.TransGen (DepStep L kernel X)
      (.thread (h0, Poll.nth X (obj L g (112 + 8 * st.val)) h0 j), true)
      (.thread (y, i), false) := by
  obtain ⟨hc, hw, hs, ho⟩ := p2_arr hp hX hFw st.isLt hga
  have hh : SoftIn L g st.val y := ⟨Frame.lt_of_get hX hga, hc, hw, hs⟩
  have hga' := hga
  rw [← ho] at hga'
  have h1 := (soft_p2_arr hp hX hFw hw hga').1
  rw [ho, ho] at h1
  have hl : i < (X.tr y).length := len_of_get hga
  exact (soft_reach hp hX hFw O ih hh0 hh hl (by omega) .refl).2

set_option maxRecDepth 20000 in
/-- **The reuse paths of the three barriers at every node.** -/
theorem reach_all {c : Nat} {st : Fin 2}
    (O : Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0) :
    ∀ n ∈ Reach.nodes L X, ReachAt L X g c st n := fun n hn =>
  Reach.joint hX (ι := PUnit) (fun _ n => ReachAt L X g c st n) (fun n _ ih _ => by
    have ih' : ReachIH L X g c st n := fun n' hn' hlt => ih n' hn' hlt ⟨⟩
    refine ⟨fun h hh x hx hxn j hj => ?_, fun h hh x hx hxn j hj => ?_,
      fun h hh => stepS hp hX hFw O ih' h hh⟩
    · obtain ⟨-, ⟨pc, sc, hget⟩, harr⟩ := (pObj hp hX hFw g st).S_rec hx
      subst hxn
      exact p_arrive_reach hp hX hFw (y := pLane L (g / L.block) st.val x.1)
        (i := (Unit.it X (obj L g (96 + 8 * st.val)) (pLane L (g / L.block) st.val) x.1 x.2).2)
        O ih' hh hget (lt_of_lt_of_eq hj harr.symm)
    · obtain ⟨-, ⟨pc, sc, hget⟩, harr⟩ := (p2Obj hp hX hFw g st).S_rec hx
      subst hxn
      exact p2_arrive_reach hp hX hFw (y := p2Prod L X g st.val x.1)
        (i := (Unit.it X (obj L g (112 + 8 * st.val)) (p2Prod L X g st.val) x.1 x.2).2)
        O ih' hh hget (lt_of_lt_of_eq hj harr.symm)) ⟨⟩ n hn

/-- **P-full reuse.** -/
theorem pReach (g : Nat) (st : Fin 2) {h : Nat} (hh : MmaIn L g h) :
    Unit.Reach L kernel Assumptions.all X (obj L g (96 + 8 * st.val)) 256
      (pLane L (g / L.block) st.val) 0 h := by
  obtain ⟨c, O⟩ := sNotify hp hX hFw g st
  exact Reach.unit_reach hX (pObj hp hX hFw g st)
    fun n hn => (reach_all hp hX hFw O n hn).p h hh

/-- **Second P reuse.** -/
theorem p2Reach (g : Nat) (st : Fin 2) {h : Nat} (hh : MmaIn L g h) :
    Unit.Reach L kernel Assumptions.all X (obj L g (112 + 8 * st.val)) 4
      (p2Prod L X g st.val) 0 h := by
  obtain ⟨c, O⟩ := sNotify hp hX hFw g st
  exact Reach.unit_reach hX (p2Obj hp hX hFw g st)
    fun n hn => (reach_all hp hX hFw O n hn).p2 h hh

/-- **S-full reuse.** -/
theorem sReach {g c : Nat} {st : Fin 2}
    (O : Notify.Obj X (obj L g (80 + 8 * st.val)) c (obj L g (80 + 8 * st.val)) 0) {h : Nat}
    (hh : SoftIn L g st.val h) :
    Notify.Reach L kernel Assumptions.all X (obj L g (80 + 8 * st.val)) c
      (obj L g (80 + 8 * st.val)) 0 h :=
  Reach.notify_reach hX O fun n hn => (reach_all hp hX hFw O n hn).s h hh

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
