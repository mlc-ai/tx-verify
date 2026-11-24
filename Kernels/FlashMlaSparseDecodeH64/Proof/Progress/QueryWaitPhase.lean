-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryWaitBlocker
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaCounts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaHistory
import Lemmas.Protocol.MbarRingBlocker
import Lemmas.Protocol.MbarUnitTx
import Lemmas.Protocol.PairTmaRing.ItemFacts

public section

/-! # The pending query TMA poll can return after its eight notifications -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.MBarrier PTX.AsyncCopy Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- One successful unit arrival is the only arrival in this checked object's history. -/
theorem one_unit_arrival {log : List (Record Ref)} {r : Record Ref} {bytes : Nat}
    (hNd : log.Nodup) (hr : r ∈ log) (ha : r.action = .arrive 1 bytes) (hf : r.fault = none)
    (hUnique : ∀ q ∈ log, ∀ n tx, q.action = .arrive n tx → q = r) :
    arrivalUnits log = 1 := by
  have zero : ∀ es : List (Record Ref), es.Sublist log → r ∉ es → arrivalUnits es = 0 := by
    intro es hSub hNot
    induction es with
    | nil => rfl
    | cons q tail ih =>
      have hQ : q ∈ log := hSub.subset List.mem_cons_self
      have hTail := (List.sublist_cons_self q tail).trans hSub
      rw [arrivalUnits, ih hTail (fun h => hNot (List.mem_cons_of_mem q h))]
      split
      · rename_i n tx hAct _
        exact (hNot (List.mem_cons.mpr (.inl (hUnique q hQ n tx hAct).symm))).elim
      · rfl
  obtain ⟨before, after, rfl⟩ := List.append_of_mem hr
  have h := (List.nodup_append'.mp hNd)
  have hAfter := (List.nodup_cons.mp h.2.1).1
  have hBefore : r ∉ before := fun hb => h.2.2 hb List.mem_cons_self
  have hZeroBefore := zero before (List.sublist_append_left ..) hBefore
  have hZeroAfter := zero after
    ((List.sublist_cons_self r after).trans (List.sublist_append_right ..)) hAfter
  rw [arrivalUnits_append, hZeroBefore, arrivalUnits, ha, hf, hZeroAfter]
  rfl

private theorem complete_count_ge (hX : Consistent L kernel Assumptions.all mem0 X)
    (hClean : ∀ r ∈ X.objects (QueryTmaRecords.object L (ctaOf L g)), r.fault = none)
    (hTiles : ∀ tile : Fin 8, ∃ j,
      X.TensorIssue (g, j) (P.param1Base + Wg1Mma.qMapOff) (MmaDataTrace.queryTmaSpec P L g tile) ∧
        (X.tensor (g, j)).any (fun o => o.effects.notified) = true) :
    8 ≤ completedTxCount (X.objects (QueryTmaRecords.object L (ctaOf L g))) := by
  classical
  let m := QueryTmaRecords.object L (ctaOf L g)
  let log := X.objects m
  let test (r : Record Ref) : Bool := match r.action, r.fault with
    | .completeTx _, none => true
    | _, _ => false
  let ids := ((log.filter test).map Record.id).toFinset
  let id (tile : Fin 8) := Ref.async (g, (hTiles tile).choose) (.notify .load)
  have hInj : Function.Injective id := by
    intro a b hEq
    have hj := congrArg (fun ref : Ref => ref.issuer.2) hEq
    change (hTiles a).choose = (hTiles b).choose at hj
    have ha := (hTiles a).choose_spec.1
    have hb := (hTiles b).choose_spec.1
    obtain ⟨_, hA⟩ := ha
    obtain ⟨_, hB⟩ := hb
    rw [hj] at hA
    have hSpec := (Kind.tensorIssue.inj (congrArg Event.kind
      (Option.some.inj (hA.symm.trans hB)))).2
    apply Fin.ext
    have hAddr := congrArg (fun sp : TensorCopy.Spec => sp.sharedBase.addr) hSpec
    simp only [MmaDataTrace.queryTmaSpec, Wg1Mma.qDstOff] at hAddr
    omega
  have hInto (tile : Fin 8) : id tile ∈ ids := by
    obtain ⟨hi, hNote⟩ := (hTiles tile).choose_spec
    obtain ⟨tag, hIssue⟩ := hi
    obtain ⟨o, ho, hNotified⟩ : ∃ o, X.tensor (g, (hTiles tile).choose) = some o ∧
        o.effects.notified = true := by
      cases h : X.tensor (g, (hTiles tile).choose) with
      | none => simp [h] at hNote
      | some o => exact ⟨o, rfl, by simpa [h] using hNote⟩
    let spec := MmaDataTrace.queryTmaSpec P L g tile
    have hMbar : spec.mbar = m := by
      simp [spec, MmaDataTrace.queryTmaSpec, Wg1Mma.qTmaAddr_eq, m]
    have hAct : objectAction X X.async m (id tile) =
        some (.completeTx (TensorTransfer.bytes spec.descriptor)) := by
      simp [objectAction, id, hIssue, ho, hMbar, hNotified, spec]
    obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 m).2.2 _ _ hAct
    have ha := ((hX.tma.2.2.1 m).2.1 r hr).1
    rw [hid, hAct] at ha
    have ht : test r = true := by
      simp [test, ← Option.some.inj ha, hClean r hr]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, ht⟩, hid⟩)
  have hLe := Finset.card_le_card_of_injOn (s := Finset.univ) id (fun a _ => hInto a)
    hInj.injOn
  have hNd := ((hX.tma.2.2.1 m).1.1).sublist ((List.filter_sublist (p := test) (l := log)).map _)
  change 8 ≤ log.countP test
  rw [List.countP_eq_length_filter, ← List.length_map Record.id, ← List.toFinset_card_of_nodup hNd]
  exact hLe

/-- In a clean maximal trace the pending query TMA wait's one expect-tx and eight notifications
have completed its phase, so its success event is a strict extension. -/
theorem no_pending_query_tensor_wait (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) {d : Wg1Mma.D} (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = .qWait)
    (hClean : ∀ r ∈ X.objects (QueryTmaRecords.object L (ctaOf L g)), r.fault = none) : False := by
  let m := QueryTmaRecords.object L (ctaOf L g)
  let log := X.objects m
  let hSound := fun w hw => (hs w hw).machine
  obtain ⟨j, _, tag, he⟩ :=
    QueryTmaHistory.arrival_before_pending_wait hpre hmax.1 (hSound g hp.1) hub hp hσ hd
  have hAct : objectAction X X.async m (.thread (g, j)) = some (.arrive 1 65536) := by
    simp [objectAction, he, m]
  obtain ⟨r, hr, hid⟩ := (hmax.1.tma.2.2.1 m).2.2 _ _ hAct
  have ha := ((hmax.1.tma.2.2.1 m).2.1 r hr).1
  rw [hid, hAct] at ha
  have ha := (Option.some.inj ha).symm
  have hChecked := (hmax.1.tma.2.2.1 m).1
  have hUnique q (hq : q ∈ log) n tx (hqA : q.action = .arrive n tx) : q = r :=
    QueryTmaRecords.arrival_record_eq hpre hmax.1 hSound ht hq hr hqA ha
  have hUnit := one_unit_arrival (List.Nodup.of_map _ hChecked.1) hr ha (hClean r hr) hUnique
  have hFirst := QueryTmaRecords.init_first (cta := ctaOf L g) hpre hmax.1 hSound ht
  obtain ⟨r0, h0, ha0, _, _⟩ := hFirst r hr
  have hNI := objects_single_lifetime hmax.1 m
  obtain ⟨s, hState⟩ := stateBefore_length_some hChecked hNI (List.mem_of_getElem? h0) ha0
    (by decide : validCount 1)
  have hExpected := PairTmaRing.expected_of_init hmax.1 hFirst hNI hState
  have hBytes : expectedTxBytes log = 8 * 8192 * arrivalUnits log := by
    apply expectedTxBytes_unit
    intro q hq _ n tx hqA
    obtain ⟨hn, htx, _⟩ := QueryTmaRecords.arrival_record hpre hmax.1 hSound ht hq hqA
    exact ⟨hn, htx⟩
  have hCompleted : UniformCompletedTx log 8192 :=
    fun q hq _ n hqA => (QueryTmaRecords.completion_source hpre hmax.1 hSound ht hq hqA).1
  have hUpper := QueryTmaRecords.completed_count_le (cta := ctaOf L g)
    hpre hmax.1 hSound ht log.length
  change completedTxCount (log.take log.length) ≤ 8 at hUpper
  rw [List.take_length] at hUpper
  have hLower : 8 ≤ completedTxCount log :=
    complete_count_ge hmax.1 hClean (fun tile => by
      obtain ⟨t, _, hi, hDone⟩ := query_wait_tiles_notified hpre hmax hs ht hub hp hσ hd tile
      exact ⟨t, hi, hDone⟩)
  have hCase := PTX.MbarRing.Blocker.tx_short hChecked hNI hState hExpected hBytes hCompleted
    (show completedTxCount log ≤ 8 * (s.phase + 1) by omega)
    (objects_no_pending_increment hmax.1 m)
  have hPhase : s.phase = 1 := by
    dsimp only [log] at hCase hUnit hLower
    rcases hCase with h | ⟨h, hCount⟩ <;> omega
  exact hmax.not_grows (query_poll_extension hpre hs hmax.1 hub hp hrel hσ
    (.tensor d rfl hd) hState (by rw [hPhase]; decide))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
