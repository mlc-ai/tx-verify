-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
public import Kernels.TmlFa4Fwd.Proof.Protocol.O.Obj
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Count
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Free.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Reach
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.S.Notify
import Kernels.TmlFa4Fwd.Proof.Top.NoTma
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.KindRingGate
import Lemmas.Protocol.MbarOneShot
import Lemmas.Protocol.TmaUnitsFault

@[expose] public section

/-! # No record of an mbarrier object faults

Per family of the startup's objects: the unit objects (P-full, the second P barriers, credit, ready,
free, bias empty) and the commit objects (S-full, Q and K/V empty) by the gate of each arrival (the
reuse paths, `Unit.Obj.fault_free`, `Notify.Obj.fault_free`), the K/V full barriers
(`NoInc.fault_free`), the one-shot final O barriers; the objects nothing names have only their
initialization. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy PTX.MbarRing
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem offset_cases : ∀ q : Fin 34, (∃ s : Fin 2, initOff q = 8 * s.val) ∨
    (∃ s : Fin 2, initOff q = 8 * s.val + 16) ∨ (∃ s : Fin 3, initOff q = 32 + 8 * s.val) ∨
    (∃ s : Fin 3, initOff q = 56 + 8 * s.val) ∨ (∃ s : Fin 2, initOff q = 80 + 8 * s.val) ∨
    (∃ s : Fin 2, initOff q = 96 + 8 * s.val) ∨ (∃ s : Fin 2, initOff q = 112 + 8 * s.val) ∨
    (∃ s : Fin 2, initOff q = oOff s) ∨ (∃ s : Fin 2, initOff q = 192 + 8 * s.val) ∨
    (∃ s : Fin 2, initOff q = 208 + 8 * s.val) ∨ (∃ s : Fin 2, initOff q = 224 + 8 * s.val) ∨
    (∃ s : Fin 2, initOff q = 320 + 8 * s.val) ∨ (∃ s : Fin 2, initOff q = 336 + 8 * s.val) ∨
    (initOff q = 128 ∨ initOff q = 136 ∨ initOff q = 160 ∨ initOff q = 168 ∨ initOff q = 176 ∨
      initOff q = 184) := by
  decide

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

theorem p_fault (g : Nat) (st : Fin 2) : ∀ r ∈ X.objects (obj L g (96 + 8 * st.val)),
    r.fault = none := by
  obtain ⟨c, O⟩ := sNotify hp hX hFw g st
  refine (pObj hp hX hFw g st).fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {a i pc sc} he hpos => ?_)
  have hlt := Frame.lt_of_get hX he
  obtain ⟨hcy, -⟩ := bar_use (o := 96 + 8 * st.val) hp hX hFw he rfl (fun _ h => by cases h)
  have hin : MmaIn L g (g / L.block * L.block + 384) := by
    have hb := hp.block
    have hcta : (g / L.block * L.block + 384) / L.block = g / L.block := by rw [hb]; omega
    have hgt : g / L.block * L.block + 384 < L.threads :=
      thread_lt_of_cta hlt (hcta.trans hcy.symm)
    refine ⟨hgt, hcta, ?_⟩
    simp only [Prologue.warpIndex, hb]
    omega
  exact ⟨_, p_arrive_reach hp hX hFw O (fun n' hn' _ => reach_all hp hX hFw O n' hn') hin he
    (by omega)⟩

theorem p2_fault (g : Nat) (st : Fin 2) : ∀ r ∈ X.objects (obj L g (112 + 8 * st.val)),
    r.fault = none := by
  obtain ⟨c, O⟩ := sNotify hp hX hFw g st
  refine (p2Obj hp hX hFw g st).fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {a i pc sc} he hpos => ?_)
  have hlt := Frame.lt_of_get hX he
  obtain ⟨hcy, -⟩ := bar_use (o := 112 + 8 * st.val) hp hX hFw he rfl (fun _ h => by cases h)
  have hin : MmaIn L g (g / L.block * L.block + 384) := by
    have hb := hp.block
    have hcta : (g / L.block * L.block + 384) / L.block = g / L.block := by rw [hb]; omega
    refine ⟨thread_lt_of_cta hlt (hcta.trans hcy.symm), hcta, ?_⟩
    simp only [Prologue.warpIndex, hb]
    omega
  exact ⟨_, p2_arrive_reach hp hX hFw O (fun n' hn' _ => reach_all hp hX hFw O n' hn') hin he
    (by omega)⟩

theorem credit_fault (g : Nat) (st : Fin 2) : ∀ r ∈ X.objects (obj L g (192 + 8 * st.val)),
    r.fault = none :=
  (creditObj hp hX hFw g st).fault_free hX (creditGate hp hX hFw g st).gated

theorem ready_fault (g : Nat) (st : Fin 2) : ∀ r ∈ X.objects (obj L g (208 + 8 * st.val)),
    r.fault = none := by
  have h := (readyObj hp hX hFw g st).fault_free (K := kernel) (A := Assumptions.all) hX
    (fun {a i pc sc} he hpos => by
      have := ready_arr_zero (g := g) (st := st) hp hX hFw he
        (by simp [Flow.arrivesOn, sourceArrive])
      omega)
  exact h

theorem free_fault (g : Nat) (st : Fin 2) : ∀ r ∈ X.objects (obj L g (224 + 8 * st.val)),
    r.fault = none := by
  refine (freeObj hp hX hFw g st).fault_free (K := kernel) (A := Assumptions.all) hX
    (fun {a i pc sc} he hpos => ?_)
  rcases free_use hp hX hFw st (h := outLane L (g / L.block) a) he rfl
    (fun _ h => by cases h) with ⟨-, ⟨_, hk⟩ | ⟨-, -, h0⟩⟩
  · cases hk
  · omega

theorem s_fault (g : Nat) (st : Fin 2) : ∀ r ∈ X.objects (obj L g (80 + 8 * st.val)),
    r.fault = none := by
  obtain ⟨c, O⟩ := sNotify hp hX hFw g st
  refine O.fault_free (K := kernel) (A := Assumptions.all) hX
    (Notify.gated_of_paths (K := kernel) (A := Assumptions.all) fun {i pc s rank}
      hget hb ht hrec hpos => ?_)
  obtain ⟨r, hr, hid⟩ := hrec
  obtain ⟨-, -, -, -, hn⟩ := Reach.notify_rec hX hr hid
  obtain ⟨hl, hcta, hw, -, -⟩ := mma_commit_of hp hX hFw hget ht
  have hc : MmaIn L g c := ⟨hl, hcta, hw⟩
  set t := ((X.tr c).take i).countP (commitsTo (obj L g (80 + 8 * st.val))) with htd
  have hpath := ((s_commit_lane hp hX hFw (st := st) (j := t - 1) hc hc hget hb
    (by omega)).1).tail (Reach.commit_notify (K := kernel) (L := L) hget hn)
  have hb512 := hp.block
  have hst := st.isLt
  have hh : SoftIn L g st.val (g / L.block * L.block + 128 * st.val) := by
    have hcta' : (g / L.block * L.block + 128 * st.val) / L.block = g / L.block := by
      rw [hb512]; omega
    refine ⟨thread_lt_of_cta hl (hcta'.trans hcta.symm), hcta', ?_, ?_⟩ <;>
      simp only [Prologue.warpIndex, hb512] <;> omega
  set h := g / L.block * L.block + 128 * st.val with hhd
  have hJ : t - 1 < okPolls (obj L g (96 + 8 * st.val)) (X.tr c) := by
    obtain ⟨z, hz, -⟩ := Relation.TransGen.head'_iff.mp hpath
    exact Poll.nth_present.mp hz.present_of_return
  obtain ⟨a, ha⟩ := pLane_of (st := st.val) hp hh.2.1 (.inl hh.2.2)
  have OP := pObj hp hX hFw g st
  obtain ⟨hSP, hobs⟩ := Reach.unit_content hX OP (poll_spin hX) (g := c) (J := t - 1) (by omega)
    hpath (fun n' hn' _ => (reach_all hp hX hFw O n' hn').p c hc) a
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := OP.S_rec hSP
  have e1 : Unit.it X (obj L g (96 + 8 * st.val)) (pLane L (g / L.block) st.val) a (t - 1) =
      (h, nthEv X (arrivesOn (obj L g (96 + 8 * st.val))) h (t - 1)) := by rw [ha]; rfl
  change arrivals _ ((X.tr (pLane L (g / L.block) st.val a)).take
    (Unit.it X (obj L g (96 + 8 * st.val)) (pLane L (g / L.block) st.val) a (t - 1)).2) = t - 1
    at harr
  rw [e1] at harr hobs
  change X.get (Unit.it X (obj L g (96 + 8 * st.val)) (pLane L (g / L.block) st.val) a (t - 1)) = _
    at hga
  rw [e1] at hga
  rw [← ha] at harr
  have hso := soft_obj_eq hh
  rw [← hso] at hga harr
  have hsp := soft_p_arr hp hX hFw hh.2.2.1 hga
  rw [harr, hso] at hsp
  rw [hso] at hga hsp
  exact ⟨h, .head (Reach.poll_guard (poll_spin hX) (len_of_get hga) hsp.ge)
    ((Relation.TransGen.single (DepStep.of_witness L hobs)).trans hpath)⟩

theorem qE_fault (g : Nat) (hg : g < L.threads) (s : Fin 2) :
    ∀ r ∈ X.objects (obj L g (8 * s.val + 16)), r.fault = none := by
  have hB := tmaBytes hp hX hFw
  have O := qNotify hp hX hFw g s
  have hcin := commitLane_in hp hX hFw hg (8 * s.val + 16)
  refine O.fault_free (K := kernel) (A := Assumptions.all) hX
    (Notify.gated_of_paths (K := kernel) (A := Assumptions.all) fun {i pc sp rank}
      hget hb ht hrec hpos => ?_)
  obtain ⟨r, hr, hid⟩ := hrec
  obtain ⟨-, -, -, -, hn⟩ := Reach.notify_rec hX hr hid
  have hob := fun o => obj_cta (L := L) hcin.2.1 o
  have hb' : sp.mbar = obj L (qCons L X g s) (16 + 8 * s.val) := by
    rw [hob, hb, Nat.add_comm]
  have hq := mma_q_commit hp hX hFw s hcin.2.2 hget hb'
  rw [hob, hob, Nat.add_comm 16] at hq
  exact ⟨_, ((qRing hp hX hFw hB g hg s).gateE hX (b := 0) (len_of_get hget)
    (t := ((X.tr (qCons L X g s)).take i).countP (commitsTo (obj L g (8 * s.val + 16))) - 1 + 1)
    (by rw [Nat.sub_add_cancel hpos]; exact hq) (by omega) 0).tail
    (Reach.commit_notify (K := kernel) (L := L) hget hn)⟩

theorem kvE_fault (g : Nat) (hg : g < L.threads) (s : Fin 3) :
    ∀ r ∈ X.objects (obj L g (56 + 8 * s.val)), r.fault = none := by
  have O := kvNotify hp hX hFw g s
  have hcin := commitLane_in hp hX hFw hg (56 + 8 * s.val)
  refine O.fault_free (K := kernel) (A := Assumptions.all) hX
    (Notify.gated_of_paths (K := kernel) (A := Assumptions.all) fun {i pc sp rank}
      hget hb ht hrec hpos => ?_)
  obtain ⟨r, hr, hid⟩ := hrec
  obtain ⟨-, -, -, -, hn⟩ := Reach.notify_rec hX hr hid
  have hob := fun o => obj_cta (L := L) hcin.2.1 o
  have hb' : sp.mbar = obj L (commitLane L X g (56 + 8 * s.val)) (56 + 8 * s.val) := by
    rw [hob]; exact hb
  have hq := mma_kv_commit hp hX hFw s hcin.2.2 hget hb'
  rw [hob, hob] at hq
  exact ⟨_, ((kvRing hp hX hFw g hg s).gateE hX (b := 0) (len_of_get hget)
    (t := ((X.tr (commitLane L X g (56 + 8 * s.val))).take i).countP
      (commitsTo (obj L g (56 + 8 * s.val))) - 1 + 1)
    (by rw [Nat.sub_add_cancel hpos]; exact hq) (by omega) 0).tail
    (Reach.commit_notify (K := kernel) (L := L) hget hn)⟩

theorem kvF_fault (g : Nat) (hg : g < L.threads) (s : Fin 3) :
    ∀ r ∈ X.objects (obj L g (32 + 8 * s.val)), r.fault = none := by
  have hs := s.isLt
  have hoF : KvOff (32 + 8 * s.val) := by unfold KvOff; omega
  have hcin := commitLane_in hp hX hFw hg (56 + 8 * s.val)
  refine NoInc.fault_free hX (δ := 0) (Nat.zero_le _) (ldProd_inj L g) (kvObj hp hX hFw hoF g)
    (kv_src hp hX hFw hoF) (selected := fun h => h = commitLane L X g (56 + 8 * s.val))
    (fun {h k pc par acq sc} _ he => ?_) (fun {a i pc} he harr hpos => ⟨_, rfl, ?_⟩)
  · obtain ⟨-, hu⟩ := bar_use (o := 32 + 8 * s.val) hp hX hFw he rfl (fun _ h => by cases h)
    cases hu with
    | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
    | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
    | epiPoll _ _ _ ho | corrPoll _ _ ho | softPoll _ _ _ _ ho => omega
    | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
    | mmaPoll _ _ _ hk =>
      simp only [Kind.wait.injEq] at hk
      omega
  · obtain ⟨-, -, -, hArr⟩ := hX.tma
    have hb := hp.block
    have ha := a.isLt
    have hcy : ldProd L g a / L.block = g / L.block := by simp only [ldProd, hb]; omega
    have hwy : Prologue.warpIndex L (ldProd L g a) = 14 ∨
        Prologue.warpIndex L (ldProd L g a) = 15 := by
      simp only [Prologue.warpIndex, ldProd, hb]
      have : (g / 512 * 512 + 448 + a.val) % 512 = 448 + a.val := by omega
      rw [this]; omega
    have he' : X.get (ldProd L g a, i) =
        some ⟨pc, .asyncArrive (obj L (ldProd L g a) (32 + 8 * s.val)) true⟩ := by
      rw [obj_cta hcy]; exact he
    obtain ⟨-, jc, pcj, sp, hj, hget, hgrp, hpoll⟩ := ld_async_arr hp hX hFw hwy s he'
    rw [obj_cta hcy, obj_cta hcy] at hpoll
    set t := ((X.tr (ldProd L g a)).take i).countP (arriveOnTo (obj L g (32 + 8 * s.val))) with ht
    have hgate := (kvRing hp hX hFw g hg s).gateF hX (a := a) (u := t - 1) (len_of_get hget)
      (by rw [Nat.sub_add_cancel hpos]; exact hpoll) 0
    have htr : TracksCpAsync X (ldProd L g a, jc) (ldProd L g a, i) :=
      ⟨rfl, hj, ⟨sp, ⟨_, hget⟩, hgrp⟩, _, true, ⟨_, he⟩⟩
    have hw : X.AsyncPresent (ldProd L g a, jc) (.write .copy) := (hArr _ harr).2 _ htr
    exact ((hgate.tail (DepStep.issue (L := L) (K := kernel) (p := .write .copy) ⟨_, hget⟩ hw
      (fun _ h => by cases h) (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h))).tail (DepStep.node hw)).tail
      (DepStep.stage (c := (.async (ldProd L g a, i) .arriveOn, false))
        (.inr ⟨rfl, rfl, htr, hw, harr⟩))

theorem bE_fault (g : Nat) (st : Fin 2) : ∀ r ∈ X.objects (obj L g (336 + 8 * st.val)),
    r.fault = none := by
  have hB := tmaBytes hp hX hFw
  have N := biasFreeHist hp hX hFw g st
  have O : Unit.Obj X (obj L g (336 + 8 * st.val)) 4 (biasLane L (g / L.block) st.val) 1 :=
    { pos := N.pos, inj := N.inj, src := N.src, init := N.init, noInval := N.noInval
      δ_le := le_rfl
      parity := fun {h k pc par acq sc} he => by
        rcases biasFree_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨⟨hc, hw⟩, _⟩ | ⟨hk, _⟩
        · have e := bE_eq L g st
          simp only [bE] at e
          rw [← e] at he ⊢
          rw [← obj_cta hc] at he ⊢
          exact (ld_tma_empty_par hp hX hFw hw (b_tmaOff st) he).2
        · cases hk }
  refine O.fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {b i pc sc} he hpos => ?_)
  have h1 : okPolls (bF L g st) ((X.tr (biasLane L (g / L.block) st.val b)).take i) =
      arrivals (obj L g (336 + 8 * st.val))
        ((X.tr (biasLane L (g / L.block) st.val b)).take i) + 1 := by
    rcases biasFree_use hp hX hFw st (h := biasLane L (g / L.block) st.val b) he rfl
      (fun _ h => by cases h) with ⟨_, _, _, hk⟩ | ⟨-, -, h1⟩
    · cases hk
    · exact h1
  exact ⟨tmaLane L X g, (biasRing hp hX hFw hB g st).gateE hX (b := b) (len_of_get he)
    (t := arrivals (obj L g (336 + 8 * st.val))
      ((X.tr (biasLane L (g / L.block) st.val b)).take i) - 1 + 1)
    (by rw [Nat.sub_add_cancel hpos]; exact h1.ge) (by omega) 0⟩

/-- A TMA full barrier in its ring of kinds. -/
private theorem tma_fault {g o nc : Nat} (ho : LdTmaOff o) (R : KRing L kernel X 1 (nc + 1) 3)
    (hF : R.F = obj L g o) (hE : R.E = obj L g (o + 16)) (hP : R.prod 0 = tmaLane L X g)
    (hS : R.SF = TmaUnits.S X (obj L g o) (tmaLane L X g) 2 16384) :
    ∀ r ∈ X.objects (obj L g o), r.fault = none := by
  have hB := tmaBytes hp hX hFw
  have O := tmaFull hp hX hFw hB g ho
  -- an event after `t + 1` polls of the empty barrier, `1 ≤ t`, whose path reaches the record
  have key : ∀ {k i t : Nat} {r : MBarrier.Record Ref}, (X.objects (obj L g o))[k]? = some r →
      ((∃ c tx, r.action = .arrive c tx) ∨ ∃ b, r.action = .completeTx b) →
      i < (X.tr (tmaLane L X g)).length → 1 ≤ t →
      t + 1 ≤ okPolls (obj L g (o + 16)) ((X.tr (tmaLane L X g)).take i) →
      Relation.ReflTransGen (DepStep L kernel X) (.thread (tmaLane L X g, i), false)
        (r.id, false) →
      ∃ kw w sw, kw < k ∧ (X.objects (obj L g o))[kw]? = some w ∧ w.reply.waited = some true ∧
        MBarrier.stateBefore (X.objects (obj L g o)) kw = some sw ∧ t ≤ sw.phase := by
    intro k i t r hk hact hi ht hpoll hpath
    have hg' := R.gateF hX (a := 0) (i := i) (u := t - 1) (by rw [hP]; exact hi)
      (by rw [hE, hP, Nat.sub_add_cancel ht]; exact hpoll) 0
    rw [hP, hF] at hg'
    obtain ⟨pc, par, acq, sc, hw, hcnt⟩ := poll_of_path hg'
    obtain ⟨kw, w, sw, hkw, hwid, ⟨p', hwa⟩, hww, hsw, hge⟩ := poll_phase_ge_for_thread hX
      (Nat.zero_le 1) O.noInval (PairTmaRing.poll_clean hX O.init O.noInval)
      (fun he => by have := R.parF 0 (hF ▸ he); rw [hF] at this; exact this) hw
    refine ⟨kw, w, sw, ?_, hkw, hww, hsw, by omega⟩
    exact Unit.Gate.poll_before hX (hg'.trans_left hpath) hk rfl hkw hwid (by
      rcases hact with ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h, hwa] <;> simp)
  refine O.fault_free hX (by decide) (by decide) ?_ ?_
  · intro k r x hk hid hact hpos
    rcases id hact with ⟨c, tx, ha⟩ | ⟨b, ha⟩
    · obtain ⟨-, rfl, j, pc, rel, sc, hj, he⟩ := O.arrive hk ha
      have hx0 : x.1.val = 0 := by
        by_contra hne
        rw [hj] at hid
        simp [TmaUnits.it, hne] at hid
      have hj2 : j = nthEv X (arrivesOn (obj L g o)) (tmaLane L X g) x.2 := by
        rw [hj] at hid
        simp only [TmaUnits.it, hx0, ↓reduceIte, Ref.thread.injEq, TmaUnits.op, Prod.mk.injEq,
          true_and] at hid
        exact hid
      have hp' : arrivesOn (obj L g o) ⟨pc, .arrive (obj L g o) (2 * 16384) 1 rel sc⟩ = true := by
        simp [arrivesOn, sourceArrive]
      have hc : arrivals (obj L g o) ((X.tr (tmaLane L X g)).take j) = x.2 := by
        unfold arrivals
        rw [hj2]
        exact (nthEv_spec_of_get (hj2 ▸ he)).2
      obtain ⟨-, -, -, hb⟩ := tma_arr hp hX hFw ho he
      rw [hc] at hb
      exact key hk hact (len_of_get he) hpos hb (by rw [hj])
    · obtain ⟨-, j, pc, al, sp, hj, he, hm⟩ := O.copy hk ha
      have hx0 : x.1.val ≠ 0 := by
        intro h0
        rw [hj] at hid
        simp [TmaUnits.it, h0] at hid
      have hj2 : j = nthEv X (issuesTo (obj L g o)) (tmaLane L X g) (2 * x.2 + (x.1.val - 1)) := by
        rw [hj] at hid
        simp only [TmaUnits.it, hx0, ↓reduceIte, Ref.async.injEq, and_true, TmaUnits.op,
          Prod.mk.injEq, true_and] at hid
        exact hid
      have hc : ((X.tr (tmaLane L X g)).take j).countP (issuesTo (obj L g o)) =
          2 * x.2 + (x.1.val - 1) := by
        rw [hj2]
        exact (nthEv_spec_of_get (hj2 ▸ he)).2
      obtain ⟨-, hb⟩ := tma_copy hp hX hFw (h := tmaLane L X g) (k := j) ho he hm
      rw [hc] at hb
      have hb' : x.2 + 1 ≤ okPolls (obj L g (o + 16)) ((X.tr (tmaLane L X g)).take j) := by omega
      refine key hk hact (len_of_get he) hpos hb' ?_
      have hpr := object_record_present hX.tma (List.mem_of_getElem? hk)
      rw [hj] at hpr ⊢
      obtain ⟨ob, hob, hn⟩ := id hpr
      obtain ⟨x', y', k', hwp⟩ := tensor_write_present hX.effectValidity hob hn
      exact (((Relation.TransGen.single (DepStep.issue (L := L) (K := kernel)
        (p := .write (.load x' y' k')) ⟨_, he⟩ hwp (fun _ h => by cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h))).tail (DepStep.node hwp)).tail (DepStep.stage
          (c := (.async (tmaLane L X g, j) (.notify .load), false))
          (.inr ⟨rfl, rfl, rfl, rfl, hwp, hpr⟩))).to_reflTransGen
  · intro t hnot x hx
    by_contra hlt
    have hr := R.reachF hX (x := x) (by rw [hS]; exact hx) 0 (j := t) (by omega)
    have hu : t < okPolls R.F (X.tr (R.cons 0)) := Poll.nth_present.mp (present_of_path hr)
    have := (R.full_observes hX hu 0).1
    rw [hS] at this
    exact hnot this

theorem q_fault (g : Nat) (hg : g < L.threads) (s : Fin 2) :
    ∀ r ∈ X.objects (obj L g (8 * s.val)), r.fault = none :=
  tma_fault hp hX hFw (q_tmaOff s) (qRing hp hX hFw (tmaBytes hp hX hFw) g hg s) rfl rfl rfl rfl

theorem bF_fault (g : Nat) (st : Fin 2) :
    ∀ r ∈ X.objects (obj L g (320 + 8 * st.val)), r.fault = none :=
  tma_fault hp hX hFw (b_tmaOff st) (biasRing hp hX hFw (tmaBytes hp hX hFw) g st) rfl
    (bE_eq L g st).symm rfl rfl

/-- The objects nothing names. -/
theorem unused_fault (g : Nat) {o : Nat} (hq : ∃ q, initOff q = o)
    (ho : o = 128 ∨ o = 136 ∨ o = 160 ∨ o = 168 ∨ o = 176 ∨ o = 184) :
    ∀ r ∈ X.objects (obj L g o), r.fault = none := by
  obtain ⟨q, hq⟩ := hq
  have hinit := obj_initFirst hp hX hFw g q
  rw [hq] at hinit
  have hni := AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) (obj L g o)
  refine fault_free_of_polls hX hinit hni fun r hr hn => ?_
  exfalso
  obtain ⟨ev, hget, hm, hin⟩ := rec_issuer hX hr
  have hni' : ∀ c, ev.kind ≠ .mbInit (obj L g o) c := fun c hc => by
    obtain ⟨n, h⟩ := hin ⟨c, hc⟩
    exact hn n h
  obtain ⟨-, hu⟩ := bar_use (o := o) hp hX hFw (h := r.id.issuer.1) (k := r.id.issuer.2) hget
    hm hni'
  cases hu with
  | epiPoll st _ _ h => have := st.isLt; omega
  | epiArr st _ h => have := st.isLt; omega
  | corrArr _ h | corrPoll _ _ h | softArr _ _ _ h | softPoll _ _ _ _ h | ldAsync _ h => omega
  | mmaPoll _ _ h => unfold MmaPollOff at h; omega
  | mmaCommit _ _ h => unfold MmaCommitOff at h; omega
  | ldPoll _ _ _ h => unfold LdPollOff at h; omega
  | ldArr _ _ h | ldCopy _ _ _ h => unfold LdTmaOff at h; omega

theorem o_fault (g : Nat) (st : Fin 2) : ∀ r ∈ X.objects (obj L g (oOff st)), r.fault = none := by
  intro r hr
  by_cases hex : ∃ r ∈ X.objects (obj L g (oOff st)), ∃ c tx, r.action = .arrive c tx
  · obtain ⟨r', hr', c, tx, ha⟩ := hex
    have ho : oOff st = 144 ∨ oOff st = 152 := by fin_cases st <;> simp [oOff]
    have hno : ∀ {h k pc : Nat} {kd : Kind}, X.get (h, k) = some ⟨pc, kd⟩ →
        MbarOf ⟨pc, kd⟩ (obj L g (oOff st)) → (∃ tx c rel sc,
          kd = .arrive (obj L g (oOff st)) tx c rel sc) ∨
          (∃ noinc, kd = .asyncArrive (obj L g (oOff st)) noinc) → False := by
      intro h k pc kd he hm hk
      obtain ⟨-, hu⟩ := bar_use (o := oOff st) hp hX hFw he hm
        (fun c h => by rcases hk with ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ <;> cases h)
      cases hu with
      | corrArr _ ho' | softArr _ _ _ ho' | epiArr _ _ ho' | ldAsync _ ho' => omega
      | ldArr _ _ ho' => unfold LdTmaOff at ho'; omega
      | epiPoll _ _ _ _ hk' | corrPoll _ _ _ hk' | softPoll _ _ _ _ _ hk' | mmaPoll _ _ _ hk'
      | ldPoll _ _ _ _ hk' | mmaCommit _ _ _ hk' | ldCopy _ _ _ _ hk' =>
        simp only at hk'
        rcases hk with ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ <;> cases hk'
    cases AsyncCopy.record_source hX.tma.2.2.1 hr' with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | increment _ _ ha'
    | bulk _ _ _ _ ha' => rw [ha] at ha'; cases ha'
    | arrive hid he _ => exact (hno he rfl (.inl ⟨_, _, _, _, rfl⟩)).elim
    | arriveOn hid he hm _ _ => subst hm; exact (hno he rfl (.inr ⟨_, rfl⟩)).elim
    | clc hid he _ _ _ => exact (no_clc hp hX hFw _ _ _ _ _ he).elim
    | commit hid he ht _ =>
      obtain ⟨hl, hcta, -⟩ := mma_commit_of hp hX hFw he ht
      rw [← obj_cta hcta] at ht hr
      exact (o_hist hp hX hFw he ht).fault_free hX hr
  · exact (o_hist_none hp hX hFw (R := .async (0, 0) (.tcNotify 0)) ⟨_, _, rfl⟩
      (fun r hr c tx ha => hex ⟨r, hr, c, tx, ha⟩)).fault_free hX hr

/-- **No record of an object of the startup faults.** -/
theorem obj_fault {g : Nat} (hg : g < L.threads) (q : Fin 34) :
    ∀ r ∈ X.objects (obj L g (initOff q)), r.fault = none := by
  rcases offset_cases q with ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ |
    ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | h
  · rw [h]; exact q_fault hp hX hFw g hg s
  · rw [h]; exact qE_fault hp hX hFw g hg s
  · rw [h]; exact kvF_fault hp hX hFw g hg s
  · rw [h]; exact kvE_fault hp hX hFw g hg s
  · rw [h]; exact s_fault hp hX hFw g s
  · rw [h]; exact p_fault hp hX hFw g s
  · rw [h]; exact p2_fault hp hX hFw g s
  · rw [h]; exact o_fault hp hX hFw g s
  · rw [h]; exact credit_fault hp hX hFw g s
  · rw [h]; exact ready_fault hp hX hFw g s
  · rw [h]; exact free_fault hp hX hFw g s
  · rw [h]; exact bF_fault hp hX hFw g s
  · rw [h]; exact bE_fault hp hX hFw g s
  · exact unused_fault hp hX hFw g ⟨q, rfl⟩ h

/-- **No record of an mbarrier object faults.** -/
theorem no_fault : ∀ o r, r ∈ X.objects o → r.fault = none := by
  intro o r hr
  obtain ⟨⟨h, k⟩, c, pc, he⟩ := obj_of_rec hp hX hFw hr
  obtain ⟨-, q, -, -, -, -, rfl, -⟩ := init_event hp hX hFw (Frame.lt_of_get hX he) he
  exact obj_fault hp hX hFw (Frame.lt_of_get hX he) q r hr

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
