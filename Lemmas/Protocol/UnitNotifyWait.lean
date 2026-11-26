-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitNotify
import Lemmas.Protocol.MbarOneShot

@[expose] public section

/-! # A wait of any thread on a commit object, with its own parity

`Notify.Obj.observes` serves the selected pollers, whose parity is that of their earlier polls plus
the offset. A thread polling once with a parity of its own (the epilogue's wait on `svDone`) is
read off its record directly (`Obj.wait_rec`): the phase before the record has the opposite
parity, and the poll observes the phase before it when there is one (`Obj.wait_witness`: it
observes every counted unit of that phase, `Obj.card_of_state`: the phase holds one). -/

namespace PTX.MbarRing.Notify

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m m0 : Loc} {g δ : Nat} {selected : Nat → Prop}

/-- A record of the object is the one its action names. -/
theorem record_action (hX : Consistent L K A mem0 X) {id : Ref} {act : Action} {k : Nat}
    {r : Record Ref} (hAct : objectAction X X.async m id = some act)
    (hr : (X.objects m)[k]? = some r) (hid : r.id = id) : r.action = act := by
  obtain ⟨j, q, hq, hqid, hqa⟩ := MbarOneShot.Hist.record_of_action hX hAct
  have hEq := ObjectInit.checked_record_index_eq (X.objects_checked hX m) hq hr
    (hqid.trans hid.symm)
  subst j
  rw [hr] at hq
  cases hq
  exact hqa

/-- **A successful wait's record**: the phase before it has the parity opposite to the wait's,
and the record's reply is the phase before it when there is one. -/
theorem Obj.wait_rec (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected)
    {h j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hw : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩) :
    ∃ (k : Nat) (r : Record Ref) (st : State), (X.objects m)[k]? = some r ∧
      r.id = .thread (h, j) ∧ r.fault = none ∧ r.reply.waited = some true ∧
      stateBefore (X.objects m) k = some st ∧
      st.phase % 2 ≠ p % 2 ∧ r.reply.completed = (if 0 < st.phase then some (st.phase - 1)
        else none) := by
  have hAct : objectAction X X.async m (.thread (h, j)) = some (.pollParity p true) := by
    simp [objectAction, hw]
  obtain ⟨k, r, hr, hid, ha⟩ := MbarOneShot.Hist.record_of_action hX hAct
  have hm := List.mem_of_getElem? hr
  have hClean := PairTmaRing.poll_clean hX O.init O.noInval r hm ⟨_, _, ha⟩
  have hWait := ((hX.tma.2.2.1 m).2.1 r hm).2 p true ha hClean
  obtain ⟨st, q, hs, hq, hPar, hComp⟩ := (X.objects_checked hX m).okPoll hr hWait
  have hq' := (Action.pollParity.inj (hq.symm.trans ha)).1
  subst hq'
  exact ⟨k, r, st, hr, hid, hClean, hWait, hs, hPar, hComp⟩

/-- **The phase a wait observed holds a counted unit.** -/
theorem Obj.card_of_state (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected) {k : Nat}
    {st : State} (hk : k ≤ (X.objects m).length) (hst : stateBefore (X.objects m) k = some st)
    (hpos : 0 < st.phase) :
    1 ≤ ((S X m g m0).filter (fun x => ph X m g m0 x = st.phase - 1)).card := by
  classical
  have hch := X.objects_checked hX m
  have hcard := hch.card_unit_arrivals_phase O.noInval (n := 1) (q := st.phase - 1)
    (fun _ r c tx hr _ ha => (O.arrive_rec hr ha).1)
    (fun _ st' _ hs => PairTmaRing.expected_of_init hX O.init O.noInval hs) O.noIncrement
    hk hst (by omega)
  refine le_trans (le_of_eq hcard.symm) ?_
  refine PairTmaRing.card_le_of_rel _ _
    (fun k x => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m g m0 x.2)
    (fun k hk => ?_) (fun k _ k' _ x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨-, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hk
  obtain ⟨x, hx, hid⟩ := O.rec_S hr hf ha
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, r, hr, hid⟩
  unfold ph
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hr hph]

/-- **A wait observes the counted units of the phase before its record.** -/
theorem Obj.wait_witness (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected)
    {h j k : Nat} {r : Record Ref} {st : State} {x : Fin 1 × Nat} (hx : x ∈ S X m g m0)
    (hr : (X.objects m)[k]? = some r) (hid : r.id = .thread (h, j))
    (hwait : r.reply.waited = some true)
    (hcomp : r.reply.completed = some (st.phase - 1))
    (hph : ph X m g m0 x = st.phase - 1) : Witness L X (it X m g m0 x.2) (h, j) := by
  obtain ⟨k', r', hk, hid', hf, ha, hp⟩ := O.S_phase hX hx
  rw [hph] at hp
  have hcu : CounterUpdate r'.action := by rw [ha]; trivial
  have ho : observedAt (X.objects m) k = some (st.phase - 1) := by
    simp [observedAt, hr, hcomp]
  have hob := Consistent.observed_of_phase hX O.noInval hk hf hcu hr hwait hp ho
  rw [hid', hid] at hob
  exact Witness.of_mbarObserved hob

/-- **`Obj.observes` with the witness**: the poll with `u + δ` earlier successful polls has the
notification of the commit with `u` earlier commits as a dependency witness. -/
theorem Obj.observes_witness (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ selected)
    {h j pc p u : Nat} {acq : Bool} {sc : MbarScope} (hR : Reach L K A X m g m0 δ h)
    (he : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩)
    (hq : okPolls m ((X.tr h).take j) = u + δ) (hh : selected h := by trivial) :
    ∃ i pc' sp rank, X.get (g, i) = some ⟨pc', .tc (.commit sp)⟩ ∧ sp.mbar = m0 ∧
      TcCommit.target sp rank = some m ∧ ((X.tr g).take i).countP (commitsTo m0) = u ∧
      Witness L X (.async (g, i) (.tcNotify rank)) (h, j) := by
  set U := O.units hX h hR hh
  have hjn : Poll.nth X m h (u + δ) = j := by
    rw [← hq]
    exact Poll.nth_eq he
  have hpw : X.RefPresent (.thread (U.w u)) := by
    show X.RefPresent (.thread (h, Poll.nth X m h (u + δ)))
    rw [hjn]
    exact ⟨_, he⟩
  obtain ⟨t, hS, ht, hobs⟩ := U.observes hX.depAcyclic hpw 0
  change t = u at ht
  subst ht
  change Witness L X (it X m g m0 t) (h, Poll.nth X m h (t + δ)) at hobs
  rw [hjn] at hobs
  obtain ⟨-, pc', sp, hget, hm, ht, hc⟩ := O.S_rec hS
  exact ⟨_, pc', sp, _, hget, hm, ht, hc, hobs⟩

end

end PTX.MbarRing.Notify
