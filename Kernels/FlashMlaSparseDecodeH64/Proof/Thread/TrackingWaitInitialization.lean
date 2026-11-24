-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Lemmas.Protocol.MbarInit

@[expose] public section

/-! # A followed actual poll uses its initialized table entry -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing

private theorem no_init_stays_none {log : List (Record Ref)} {s : Option State}
    (hRun : RecordedHistory none log s) (hn : ∀ r ∈ log, ∀ n, r.action ≠ .init n) :
    s = none := by
  generalize heq : (none : Option State) = start at hRun
  induction hRun with
  | nil => rfl
  | @cons initial r rest final hok _ ih =>
    have hinit (n : Nat) := hn r List.mem_cons_self n
    have hnone : r.reply.state = none := by
      unfold RecordOk at hok
      rw [← heq] at hok
      cases ha : r.action <;> simp [ha, perform, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at hok
      · rename_i n
        exact (hinit n ha).elim
      all_goals exact congrArg Reply.state hok.1
    exact (ih (fun r hr => hn r (List.mem_cons_of_mem _ hr)) hnone.symm).trans (hnone.trans heq)

/-- A table poll ordered after its initializer has a genuine, fault-free object response. -/
theorem wait_after_init_publication {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i tag parity : Nat} {acq ok : Bool} {scope : MbarScope} {init : EvId}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (j : Fin 23)
    (he : X.get (g, i) = some ⟨tag, .wait (initTable.loc L (ctaOf L g) j) parity ok acq scope⟩)
    (hInit : X.MbInit init (initTable.loc L (ctaOf L g) j) (initCount j))
    (hPub : baseCausality L X init (g, i)) :
    let m := initTable.loc L (ctaOf L g) j
    ∃ idx r before, (X.objects m)[idx]? = some r ∧ r.id = .thread (g, i) ∧
      stateBefore (X.objects m) idx = some before ∧ before.expected = initCount j ∧
      r.action = .pollParity parity ok ∧ r.fault = none ∧ r.reply.waited = some ok := by
  let m := initTable.loc L (ctaOf L g) j
  change X.MbInit init m (initCount j) at hInit
  obtain ⟨pos, z, hPos, hZid, hZA, hZOk, _⟩ := init_record_of_consistent hX hInit
  have hChecked := X.objects_checked hX m
  have hZBefore : stateBefore (X.objects m) pos = none := by
    apply no_init_stays_none (hChecked.prefix (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hPos).1))
    intro r hr n hn
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    have hklt : k < pos := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simp at this
      omega
    have hRecord : (X.objects m)[k]? = some r := by
      rwa [List.getElem?_take, ite_eq_left hklt] at hk
    have hrObj := List.mem_of_getElem? hRecord
    cases record_source hX.tma.2.2.1 hrObj with
    | @init a b _ _ hid hget ha =>
      obtain ⟨pc, hReal⟩ := hInit
      have hSame := init_table_event_unique hpre hX hs hget hReal rfl rfl
      have hIdx := hX.object_index_eq hRecord hPos (hid.trans ((congrArg Ref.thread hSame).trans
        hZid.symm))
      omega
    | inval _ _ ha | wait _ _ ha | arrive _ _ ha | tensor _ _ _ ha | commit _ _ _ ha
    | bulk _ _ _ _ ha | increment _ _ ha | arriveOn _ _ _ _ ha | clc _ _ _ _ ha =>
      rw [hn] at ha
      cases ha
  have hvalid : validCount (initCount j) := initTable.count_valid (b := j) trivial
  have hZClean := (init_record_success hZOk hZA hZBefore hvalid).1
  have haction : objectAction X X.async m (.thread (g, i)) = some (.pollParity parity ok) := by
    simp [objectAction, he, m]
  obtain ⟨r, hr, hrId⟩ := (hX.tma.2.2.1 m).2.2 _ _ haction
  have hrA : r.action = .pollParity parity ok := by
    have hc := ((hX.tma.2.2.1 m).2.1 r hr).1
    rw [hrId, haction] at hc
    exact (Option.some.inj hc).symm
  obtain ⟨idx, hIdx⟩ := List.mem_iff_getElem?.mp hr
  have hIdxLen := (List.getElem?_eq_some_iff.mp hIdx).1
  have hPast : pos < idx := by
    by_contra! hn
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · rw [hIdx] at hPos
      cases Option.some.inj hPos
      rw [hrA] at hZA
      cases hZA
    · exact object_not_before_of_baseCausality (id := .thread (g, i)) hX ⟨initCount j, hInit⟩ hPub
        ⟨idx, pos, r, z, hIdx, hrId, hPos, hZid, hlt⟩
  obtain ⟨before, hBefore, hEx⟩ := ObjectInit.checked_expected_after_init hChecked
    (objects_single_lifetime hX m) hPos hZA hZClean hPast hIdxLen.le
  have hrOk := hChecked.at hIdx
  have hClean : r.fault = none := by
    unfold RecordOk at hrOk
    rw [hBefore, hrA] at hrOk
    exact hrOk.2
  exact ⟨idx, r, before, hIdx, hrId, hBefore, hEx, hrA, hClean,
    ((hX.tma.2.2.1 m).2.1 r hr).2 parity ok hrA hClean⟩

/-- An issued table poll with a followed role state has a genuine, fault-free object response.
The initializer need only precede this operation; earlier fault records are allowed. -/
theorem wait_after_table_init {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i tag parity : Nat} {acq ok : Bool} {scope : MbarScope} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hRole : ∀ s, d ≠ .prologue s) (j : Fin 23)
    (he : X.get (g, i) = some ⟨tag, .wait (initTable.loc L (ctaOf L g) j) parity ok acq scope⟩) :
    let m := initTable.loc L (ctaOf L g) j
    ∃ idx r before, (X.objects m)[idx]? = some r ∧ r.id = .thread (g, i) ∧
      stateBefore (X.objects m) idx = some before ∧ before.expected = initCount j ∧
      r.action = .pollParity parity ok ∧ r.fault = none ∧ r.reply.waited = some ok := by
  obtain ⟨init, hInit, hPub⟩ := completed_init_before_followed_role hpre hX hs he hState hRole j
  exact wait_after_init_publication hpre hX hs j he hInit hPub

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
