-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaBlockOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound
import Lemmas.Protocol.MbarOneShot

@[expose] public section

/-! # Completed Tensor Core reads before probability reuse -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy PTX.Flow PTX.MbarRing
open MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A PV acquire observing a completed phase observes an actual PV commit in the object's
checked history. An even-parity successful wait already certifies a completed phase. -/
theorem actual_pv_wait_observes_commit {cta issuer g j site parity : Nat} {slot : Fin 2}
    {scope : MbarScope} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hmma : MmaIssuer P L X cta issuer)
    (hw : X.get (g, j) = some ⟨site, .wait (Object.svDone.loc L cta slot) parity true true scope⟩)
    (hphase : parity % 2 = 0 ∨ ∃ r ∈ X.objects (Object.svDone.loc L cta slot),
      r.id = .thread (g, j) ∧ r.reply.completed.isSome) :
    ∃ c tag sp rank d, X.get (issuer, c) = some ⟨tag, .tc (.commit sp)⟩ ∧
      TcCommit.target sp rank = some (Object.svDone.loc L cta slot) ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      ctaOf L issuer = cta ∧ d.site = .pvCommit ∧ d.i % 2 = slot.val ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (g, j) := by
  classical
  let m := Object.svDone.loc L cta slot
  let log := X.objects m
  let O := reuse_obj (slot := slot) hpre hX (fun h hh => (hs h hh).machine) hmma
  have hact : objectAction X X.async m (.thread (g, j)) = some (.pollParity parity true) := by
    simp [objectAction, hw, m]
  obtain ⟨k, w, hget, hwid, hwa⟩ := MbarOneShot.Hist.record_of_action hX hact
  have hwf := PairTmaRing.poll_clean hX O.init O.noInval w
    (List.mem_of_getElem? hget) ⟨_, _, hwa⟩
  have hwait := ((hX.tma.2.2.1 m).2.1 w (List.mem_of_getElem? hget)).2 parity true hwa hwf
  have hchecked : CheckedLog log := X.objects_checked hX m
  obtain ⟨st, _, hst, hwp, hparity, hcompleted⟩ := hchecked.okPoll hget hwait
  obtain ⟨rfl, -⟩ := Action.pollParity.inj (hwp.symm.trans hwa)
  have hpos : 0 < st.phase := by
    rcases hphase with heven | ⟨record, hmem, hid, hdone⟩
    · omega
    · obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.mp hmem
      have hindex := ObjectInit.checked_record_index_eq hchecked hget hk' (hwid.trans hid.symm)
      subst k'
      rw [hget] at hk'
      obtain rfl := Option.some.inj hk'
      by_contra hn
      simp [hcompleted, hn] at hdone
  have ho : observedAt log k = some (st.phase - 1) := by
    simp only [log, observedAt, hget, Option.bind_some, hcompleted, ite_eq_left hpos]
  have hcard := hchecked.card_unit_arrivals_phase O.noInval (n := 1) (q := st.phase - 1)
    (fun _ _ _ _ hr _ ha => (O.arrive_rec hr ha).1)
    (fun _ _ _ hh => PairTmaRing.expected_of_init hX O.init O.noInval hh) O.noIncrement
    (List.getElem?_eq_some_iff.mp hget).1.le hst (by omega)
  have hex : 0 < ((Finset.range log.length).filter (UnitArrivalIn log (st.phase - 1))).card := by
    rw [hcard]
    decide
  obtain ⟨k', hk'⟩ := Finset.card_pos.mp hex
  obtain ⟨r, _, hr, ha, hrf, hphase⟩ := (Finset.mem_filter.mp hk').2
  obtain ⟨unit, hu, hid⟩ := O.rec_S hr hrf ha
  obtain ⟨_, tag, sp, hcommit, _, htarget, _⟩ := O.S_rec hu
  let c := Notify.cm X issuer m unit.2
  let rank := Notify.rank X m issuer m unit.2
  obtain ⟨_, hcta, d, hslot, hshape, hstate⟩ :=
    actual_notification hpre hX hs hcommit rfl htarget
  have hsite : d.site = .pvCommit := by
    rcases hshape with ⟨h, _⟩ | ⟨_, h⟩
    · cases h
    · exact h
  have hcu : CounterUpdate r.action := by rw [ha]; trivial
  have hobs := hX.observed_of_phase O.noInval hr hrf hcu hget hwait hphase ho
  rw [hid, hwid] at hobs
  exact ⟨c, tag, sp, rank, d, hcommit, htarget, hstate, hcta, hsite, hslot,
    Witness.of_mbarObserved hobs⟩

/-- A commit notification observed with matching scopes covers every prior asynchronous
operation of that issuer, including its shared operand reads. -/
theorem completed_read {L : Launch} {mem0 : Mem0} {X : Execution}
    {i commit w : EvId} {tag parity byte : Nat} {rank : Fin 16} {m : Loc}
    {sc : MbarScope} {sp : TcCommit.Spec} {isB : Bool}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hc : X.Commit commit sp) (hm : TcCommit.target sp rank = some m)
    (ht : TracksMma X i commit) (hscope : ScopesMeet L .cluster i.1 sc w.1)
    (hw : X.get w = some ⟨tag, .wait m parity true true sc⟩)
    (ho : Witness L X (.async commit (.tcNotify rank)) w) :
    X.AsyncPresent i .mmaDone ∧ AsyncFinished L X i (.mmaRead isB byte) w := by
  obtain ⟨hr, ha⟩ := ho.waitObserves_tcNotify hw
  refine ⟨(hX.tcCommit _ _ hr).2 _ ht, .inr ⟨sc, ?_, hscope⟩⟩
  exact ⟨_, m, ⟨commit, sp, rank, rfl, ht, hc, hm, hr⟩, ha⟩

/-- The acquire preceding a probability write observes the QK commit of that same block. -/
theorem actual_qk_commit_before_probability {cta issuer j : Nat} {lane : Fin 128} {p : Fin 4}
    {new : Wg0.D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hmma : MmaIssuer P L X cta issuer)
    (hNew : Frame.stateAt (Machine.code P L) X (softmax L cta lane) j = some (some (.wg0 new)))
    (hStore : new.site = .pStore p) (he : X.get (softmax L cta lane, j) = some e) :
    let h := softmax L cta lane
    let m := qk L cta (rawSlot new.block)
    ∃ w < j, ∃ tag parity scope c commitTag sp rank d,
      X.get (h, w) = some ⟨tag, .wait m parity true true scope⟩ ∧
      X.get (issuer, c) = some ⟨commitTag, .tc (.commit sp)⟩ ∧
      TcCommit.target sp rank = some m ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      ctaOf L issuer = cta ∧ d.site = .qkCommit ∧ d.i = new.block ∧
      ScopesMeet L .cluster issuer scope h ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (h, w) := by
  dsimp only
  let h := softmax L cta lane
  let slot := rawSlot new.block
  let u := new.block / 2
  have hCta' : ctaOf L h = cta := by
    have := lane.isLt
    simp only [h, softmax, ctaOf, hpre.block]
    omega
  have hh := Frame.lt_of_get hX he
  obtain ⟨_, hp⟩ := Wg0GemmTrace.composed_probability_counts hpre
    ((hs h hh).machine.produces (hX.thr h hh)) hNew ⟨p, hStore⟩
  rw [hCta'] at hp
  change PTX.Flow.okPolls (qk L cta slot) ((X.tr h).take j) = u + 1 at hp
  obtain ⟨w, tag, parity, acq, sc, hwj, hw, hwcount⟩ := Poll.exists_nth hp.ge
  obtain ⟨q, hQ⟩ := FollowedPrefix.state_at hNew hwj.le
  obtain ⟨_, rfl⟩ := poll_at_followed (obj := .qkDone) hpre hX (hs h hh).machine
    (by rw [hQ]; simp) hw rfl
  obtain ⟨c, src, sp, rank, d, hCommit, hTarget, hState, hCta'', hQk, hBlock, hWitness⟩ :=
    ScoreReadback.commit_of_counted_qk_wait hpre hX hs hmma hw hwcount
  have hi := Frame.lt_of_get hX hCommit
  have hSame : SameCta L issuer h := ⟨hi, hh, hCta''.trans hCta'.symm⟩
  have hSameRev : SameCta L h issuer := ⟨hh, hi, hCta'.trans hCta''.symm⟩
  have hScope : ScopesMeet L .cluster issuer sc h := by
    have hCluster : SameCluster L issuer h :=
      ⟨hi, hh, congrArg L.clusterOfCta hSame.2.2⟩
    refine ⟨hCluster, ?_⟩
    cases sc <;> first
      | exact hSameRev
      | exact ⟨hh, hi, hCluster.2.2.symm⟩
      | exact ⟨hh, hi⟩
  exact ⟨w, hwj, tag, parity, sc, c, src, sp, rank, d, hw, hCommit, hTarget,
    hState, hCta'', hQk, hBlock, hScope, hWitness⟩

theorem qk_commit_before_probability {cta issuer j : Nat} {lane : Fin 128} {p : Fin 4} {new : Wg0.D}
    {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (hmma : MmaIssuer P L X cta issuer)
    (hNew : Frame.stateAt (Machine.code P L) X (softmax L cta lane) j = some (some (.wg0 new)))
    (hStore : new.site = .pStore p) (he : X.get (softmax L cta lane, j) = some e) :
    let h := softmax L cta lane
    let m := qk L cta (rawSlot new.block)
    ∃ w < j, ∃ tag parity scope c commitTag sp rank d,
      X.get (h, w) = some ⟨tag, .wait m parity true true scope⟩ ∧
      X.get (issuer, c) = some ⟨commitTag, .tc (.commit sp)⟩ ∧
      TcCommit.target sp rank = some m ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      ctaOf L issuer = cta ∧ d.site = .qkCommit ∧ d.i = new.block ∧
      ScopesMeet L .cluster issuer scope h ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (h, w) :=
  actual_qk_commit_before_probability hpre hX (fun _ hg => Machine.code_sound hpre hg)
    hmma hNew hStore he

/-- The QK acquire preceding a probability store observes any earlier block's PV read
completion. The two events are ordered through the current block's QK commit. -/
theorem prior_pv_completion {cta issuer g i j byte : Nat} {lane : Fin 128} {p : Fin 4} {k : Fin 8}
    {old : Wg1Mma.D} {new : Wg0.D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : MmaIssuer P L X cta issuer) (hCta : ctaOf L g = cta) (hOp : X.TcAsync (g, i))
    (hOld : Frame.stateAt (Machine.code P L) X g i = some (some (.mma old)))
    (hPv : old.site = .pvMma k) (hBlocks : old.i < new.block)
    (hNew : Frame.stateAt (Machine.code P L) X (softmax L cta lane) j = some (some (.wg0 new)))
    (hStore : new.site = .pStore p) (he : X.get (softmax L cta lane, j) = some e) :
    X.AsyncPresent (g, i) .mmaDone ∧
      ∃ w < j, AsyncFinished L X (g, i) (.mmaRead false byte) (softmax L cta lane, w) := by
  have hg := hmma _ _ _ hCta hOld (by simp [hPv])
  subst g
  obtain ⟨w, hwj, tag, parity, sc, c, src, sp, rank, d, hw, hCommit, hTarget,
    hState, _, _, hBlock, hScope, hWitness⟩ :=
    qk_commit_before_probability hpre hX hs ht hmma hNew hStore he
  have hOrder : i < c := by
    by_contra hlt
    have hm := Wg1Mma.block_order (by omega : c ≤ i) hState hOld
    omega
  have hTrack : TracksMma X (issuer, i) (issuer, c) := ⟨rfl, hOrder, hOp, sp, ⟨src, hCommit⟩⟩
  obtain ⟨hDone, hFinished⟩ :=
    completed_read hX ⟨src, hCommit⟩ hTarget hTrack hScope hw hWitness
  exact ⟨hDone, w, hwj, hFinished⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
