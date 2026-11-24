-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandOrder
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Async.AsyncOrigins
public import Lemmas.MBarrier.MBarrierHistory
import Lemmas.Tmem.AllocResult

@[expose] public section

namespace PTX

open AsyncCopy TcMma

variable {L : Launch} {X Y : Execution}

private theorem intent_of_get_eq {e : Ref} {a : Acc} {w : Bool}
    (h : Y.get e.issuer = X.get e.issuer) (intent : X.Intent e a w) : Y.Intent e a w := by
  cases e with
  | thread i =>
    change Y.get i = X.get i at h
    simpa only [Execution.Intent, Execution.Access, Execution.Reads, Execution.Writes,
      Execution.Rmw, h] using intent
  | async i p =>
    change Y.get i = X.get i at h
    cases p <;>
      simp only [Execution.Intent, Part.writes, Execution.AsyncFootprint, and_false,
        Execution.Copy, Execution.BulkPrefetch, Execution.MmaFootprint, Execution.MmaIssue,
        Execution.CpIssue, Execution.TensorIssue, Execution.TensorStoreIssue,
        Execution.TensorPrefetchIssue, Execution.ClcIssue, h] at intent ⊢ <;>
      exact intent

private theorem touches_of_get_eq {e : Ref} {a : Acc}
    (h : Y.get e.issuer = X.get e.issuer) (touch : X.MemTouches e a) : Y.MemTouches e a := by
  rcases touch with ⟨w, intent⟩ | ⟨i, bs, rfl, read⟩
  · exact .inl ⟨w, intent_of_get_eq h intent⟩
  · change Y.get i = X.get i at h
    exact .inr ⟨i, bs, rfl, by simpa only [Execution.NcReads, h] using read⟩

private theorem touches_issuer {e : Ref} {a : Acc} (touch : X.MemTouches e a) :
    e.issuer.2 < (X.tr e.issuer.1).length := by
  rcases touch with ⟨w, intent⟩ | ⟨i, bs, rfl, pc, read⟩
  · exact len_of_get (intent_issuer intent).choose_spec
  · exact len_of_get read

/-- A base byte path starts at an issued instruction or its effect. -/
theorem modelCausality_issuer_left {l : Loc} {e f : Ref}
    (h : modelCausality L X l e f) : e.issuer.2 < (X.tr e.issuer.1).length := by
  cases e with
  | thread e =>
    cases f with
    | thread f =>
      rcases h with h | ⟨_, _, _, _, hresult, _, _, _, _⟩
      · exact (baseCausality_events h).1
      · obtain ⟨_, _, hstore⟩ := hresult.writes
        exact len_of_get hstore
    | async i p =>
      rcases h.2 with ⟨_, _, _, _, _, _, _, hb, _⟩ | ⟨_, hb⟩ <;>
        exact (baseCausality_events hb).1
  | async i p =>
    cases f with
    | thread f => exact h.1.issuer_lt
    | async j q => exact h.2.left_cover.issuer_lt

private theorem mmaRead_of_get_eq {i : EvId} {b : Bool} {k : Nat} {l : Loc}
    {v : Option Byte} (h : Y.get i = X.get i) (ho : Y.async.mmaOperands i = X.async.mmaOperands i)
    (read : X.MmaRead i b k l v) : Y.MmaRead i b k l v := by
  simpa only [Execution.MmaRead, Execution.MmaFootprint, Execution.MmaIssue, Execution.CpIssue,
    h, ho] using read

private theorem mmaObserved_le (hle : X.le Y) {i w : EvId} {acq : Bool} {sc : MbarScope}
    (h : AsyncObserved X i .mmaDone w acq sc) : AsyncObserved Y i .mmaDone w acq sc := by
  obtain ⟨ref, m, notify, wait⟩ := h
  obtain ⟨c, s, rank, rfl, ⟨lane, before, tc, target, pc', hcommit'⟩, ⟨pc, hcommit⟩,
    hm, hrank⟩ := notify
  obtain ⟨⟨pcw, parity, hw⟩, hlog⟩ := wait
  have htc : Y.TcAsync i := by
    rcases tc with ⟨d, s, acc, mask, pc, h⟩ | ⟨c, pc, h⟩ | ⟨s, pc, h⟩
    · exact .inl ⟨d, s, acc, mask, pc, Execution.le_get hle h⟩
    · exact .inr (.inl ⟨c, pc, Execution.le_get hle h⟩)
    · exact .inr (.inr ⟨s, pc, Execution.le_get hle h⟩)
  exact ⟨_, m, ⟨c, s, rank, rfl, ⟨lane, before, htc, target, pc', Execution.le_get hle hcommit'⟩,
    ⟨pc, Execution.le_get hle hcommit⟩, hm, hle.2.2.2.2.2.2.2.2.2.2.2.2 c hrank⟩,
    ⟨pcw, parity, Execution.le_get hle hw⟩, hlog.extends (hle.2.2.2.1 m)⟩

/-- A checked extension can only append object records. A commit observed by an old wait
was already observed in the old log, as was the commit's notification. -/
theorem observesMma_of_prefix (hle : X.le Y) (hX : EffectValidity L X)
    (hY : ObjectsOk Y) {i w : EvId} {acq : Bool} {sc : MbarScope}
    (hw : w.2 < (X.tr w.1).length) (obs : AsyncObserved Y i .mmaDone w acq sc) :
    AsyncObserved X i .mmaDone w acq sc := by
  obtain ⟨ref, m, hnot, ⟨pcw, parity, hwait⟩, horder⟩ := obs
  have hwait' := (le_get_old hle hw).symm.trans hwait
  have haction : objectAction X X.async m (.thread w) = some (.pollParity parity true) := by
    simp [objectAction, hwait']
  obtain ⟨oldWait, hmem, hWaitId⟩ := (hX.tma.2.2.1 m).2.2 _ _ haction
  obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hmem
  have hj'lt := (List.getElem?_eq_some_iff.mp hj').1
  obtain ⟨suffix, hprefix⟩ := hle.2.2.2.1 m
  obtain ⟨a, j, counter, waiter, phase, ha, hid, hcf, hj, hwid, hwf, hreply, haj, hp, hq, hl⟩ :=
    horder
  have hsame : j = j' := by
    apply (List.Nodup.getElem?_inj (xs := (Y.objects m).map MBarrier.Record.id)
      (by simpa using (List.getElem?_eq_some_iff.mp hj).1) (hY m).1.1).mp
    rw [List.getElem?_map, List.getElem?_map, hj, ← hprefix,
      List.getElem?_append_left hj'lt, hj', Option.map_some, Option.map_some, hwid, hWaitId]
  have hjold : j < (X.objects m).length := hsame ▸ hj'lt
  have haold : a < (X.objects m).length := haj.trans hjold
  rw [← hprefix, List.getElem?_append_left haold] at ha
  rw [← hprefix, List.getElem?_append_left hjold] at hj
  rw [← hprefix, MBarrier.phaseAt_append _ _ haold.le] at hp
  rw [← hprefix, MBarrier.observedAt_append _ _ hjold] at hq
  rw [← hprefix, MBarrier.SameLifetime.append hjold.le] at hl
  obtain ⟨c, s, rank, rfl, ⟨lane, before, ht, spec, pcs, hcs⟩, ⟨pc, hc⟩, htarget, _⟩ := hnot
  have hcold : rank ∈ X.tcNotified c := by
    have h := object_record_present hX.tma (List.mem_of_getElem? ha)
    rw [hid] at h
    exact h
  obtain ⟨⟨_, _, ⟨pc', hc'⟩, _⟩, _⟩ := hX.tcCommit c rank hcold
  have hcl := len_of_get hc'
  have hil : i.2 < (X.tr i.1).length := by rw [lane]; omega
  have hci := le_get_old hle hcl
  have hti : X.TcAsync i := by
    simpa only [Execution.TcAsync, Execution.MmaIssue, Execution.CpIssue, Execution.ShiftIssue,
      le_get_old hle hil] using ht
  exact ⟨_, m, ⟨c, s, rank, rfl, ⟨lane, before, hti, spec, pcs, hci ▸ hcs⟩,
    ⟨pc, hci ▸ hc⟩, htarget, hcold⟩, ⟨pcw, parity, hwait'⟩,
    ⟨a, j, counter, waiter, phase, ha, hid, hcf, hj, hwid, hwf, hreply, haj, hp, hq, hl⟩⟩

/-- Every added operand edge is preserved by a growth step that preserves the base byte edges. -/
theorem ByteCausality.le_mono (hle : X.le Y)
    (hbase : ∀ {l e f}, modelCausality L X l e f → modelCausality L Y l e f)
    {l : Loc} {e f : Ref} (h : ByteCausality L X l e f) : ByteCausality L Y l e f := by
  refine h.map (retained := fun _ => True) trivial (fun _ => hbase)
    (fun _ intent _ => intent_of_get_eq (le_get_old hle
      (len_of_get (intent_issuer intent).choose_spec)) intent)
    (fun _ touch _ => touches_of_get_eq (le_get_old hle (touches_issuer touch)) touch) ?_
  intro f i w b k acq sc _ hpo issue ⟨v, read⟩ obs
  have hil : i.2 < (X.tr i.1).length := by
    rcases read.1 with ⟨_, _, _, _, ⟨pc, h⟩, _⟩ | ⟨_, _, _, ⟨pc, h⟩, _⟩
    · exact len_of_get h
    · exact len_of_get h
  have hget := le_get_old hle hil
  have hdst := le_get_old hle hpo.2.2.1
  obtain ⟨operands, hop, _⟩ := read.2
  have hop' := hle.2.2.1.2.2.2.1 i operands hop
  exact ⟨trivial, (le_po_old hle hpo.2.2.1).mpr hpo,
    (CommitOperandIssue.congr hget hdst).mpr issue,
    ⟨v, mmaRead_of_get_eq hget (hop'.trans hop.symm) read⟩, mmaObserved_le hle obs⟩

/-- An execution extension cannot introduce byte causality into an old issuing instruction when
its base paths and observations by old waits are unchanged. A tracked MMA had completed as soon
as the old wait could observe its commit, so its reported operand bytes are retained. -/
private theorem reflect_to_retained (hle : X.le Y) (htc : TcEffectsOk X) (hcommit : CommitOk X)
    {e : Ref}
    {retained : Ref → Prop}
    (hissuer : ∀ {f}, retained f → f.issuer.2 < (X.tr f.issuer.1).length)
    (hretain : ∀ {i b k l v}, X.MmaRead i b k l v → retained (.async i (.mmaRead b k)))
    (hbase : ∀ {l f}, retained f → modelCausality L Y l e f → modelCausality L X l e f)
    (hobs : ∀ {i w acq sc}, w.2 < (X.tr w.1).length →
      AsyncObserved Y i .mmaDone w acq sc → AsyncObserved X i .mmaDone w acq sc)
    {l : Loc} {f : Ref} (hf : retained f)
    (h : ByteCausality L Y l e f) : ByteCausality L X l e f := by
  refine h.map hf (fun hkeep => hbase hkeep)
    (fun ⟨_, first⟩ intent _ => intent_of_get_eq
      (le_get_old hle (modelCausality_issuer_left first)).symm intent)
    (fun hkeep touch _ => touches_of_get_eq (le_get_old hle (hissuer hkeep)).symm touch) ?_
  intro f i w b k acq sc hkeep hpo issue ⟨v, read⟩ obs
  have hdst := hissuer hkeep
  have obs' := hobs (po_lt_left hpo hdst) obs
  have done := (mma_done_waits (L := L) hcommit obs').1
  have old : ∃ ev operands, X.get i = some ev ∧ X.async.mmaOperands i = some operands := by
    rcases htc.1 i (htc.2 i done) with h | h | h
    · obtain ⟨_, _, _, _, ops, ⟨pc, h⟩, hop, _⟩ := h
      exact ⟨_, ops, h, hop⟩
    · obtain ⟨_, ops, ⟨pc, h⟩, hop, _⟩ := h
      exact ⟨_, ops, h, hop⟩
    · obtain ⟨_, ops, ⟨pc, h⟩, hop, _⟩ := h
      exact ⟨_, ops, h, hop⟩
  obtain ⟨ev, ops, hi, hop⟩ := old
  have hold := len_of_get hi
  have hget := le_get_old hle hold
  have hop' := hle.2.2.1.2.2.2.1 i ops hop
  have read' := mmaRead_of_get_eq hget.symm (hop.trans hop'.symm) read
  exact ⟨hretain read', (le_po_old hle hdst).mp hpo,
    (CommitOperandIssue.congr hget (le_get_old hle hdst)).mp issue,
    ⟨v, read'⟩, obs'⟩

/-- Reflect byte causality into effects whose issuing instruction is retained. -/
theorem ByteCausality.le_reflect (hle : X.le Y) (htc : TcEffectsOk X) (hcommit : CommitOk X)
    {e : Ref}
    (hbase : ∀ {l f}, f.issuer.2 < (X.tr f.issuer.1).length →
      modelCausality L Y l e f → modelCausality L X l e f)
    (hobs : ∀ {i w acq sc}, w.2 < (X.tr w.1).length →
      AsyncObserved Y i .mmaDone w acq sc → AsyncObserved X i .mmaDone w acq sc)
    {l : Loc} {f : Ref} (hf : f.issuer.2 < (X.tr f.issuer.1).length)
    (h : ByteCausality L Y l e f) : ByteCausality L X l e f :=
  reflect_to_retained hle htc hcommit (fun h => h) (fun read => by
    rcases read.1 with ⟨_, _, _, _, ⟨pc, h⟩, _⟩ | ⟨_, _, _, ⟨pc, h⟩, _⟩
    · exact len_of_get h
    · exact len_of_get h) hbase hobs hf h

/-- Reflect byte causality from one source into effects that are already present. -/
theorem ByteCausality.le_reflect_from_present (hle : X.le Y) (hv : EffectValidity L X)
    {e : Ref}
    (hbase : ∀ {l f}, X.RefPresent f → modelCausality L Y l e f → modelCausality L X l e f)
    (hobs : ∀ {i w acq sc}, w.2 < (X.tr w.1).length →
      AsyncObserved Y i .mmaDone w acq sc → AsyncObserved X i .mmaDone w acq sc)
    {l : Loc} {f : Ref} (hf : X.RefPresent f)
    (h : ByteCausality L Y l e f) : ByteCausality L X l e f :=
  reflect_to_retained hle hv.tma.2.1 hv.tcCommit
    (fun {f} h => by
      cases f with
      | thread i => exact len_of_get h.choose_spec
      | async i p => exact len_of_get (asyncPresent_issuer hv h).choose_spec)
    (fun read => ⟨_, _, read⟩) hbase hobs hf h

/-- Reflect byte causality into effects that are already present. -/
theorem ByteCausality.le_reflect_present (hle : X.le Y) (hv : EffectValidity L X)
    (hbase : ∀ {l e f}, X.RefPresent f → modelCausality L Y l e f → modelCausality L X l e f)
    (hobs : ∀ {i w acq sc}, w.2 < (X.tr w.1).length →
      AsyncObserved Y i .mmaDone w acq sc → AsyncObserved X i .mmaDone w acq sc)
    {l : Loc} {e f : Ref} (hf : X.RefPresent f)
    (h : ByteCausality L Y l e f) : ByteCausality L X l e f :=
  ByteCausality.le_reflect_from_present hle hv (fun h => hbase h) hobs hf h

/-- With unchanged traces, all handoff destinations are old instructions. -/
theorem ByteCausality.reflect_of_same_tr (hle : X.le Y) (htr : Y.tr = X.tr)
    (htc : TcEffectsOk X) (hcommit : CommitOk X)
    (hbase : ∀ {l e f}, modelCausality L Y l e f → modelCausality L X l e f)
    (hobs : ∀ {i w acq sc}, AsyncObserved Y i .mmaDone w acq sc →
      AsyncObserved X i .mmaDone w acq sc)
    {l : Loc} {e f : Ref} (h : ByteCausality L Y l e f) : ByteCausality L X l e f := by
  cases h with
  | direct h => exact .direct (hbase h)
  | commitOperand hshared hw hi hr prior ho hp hc =>
    have hf : f.issuer.2 < (X.tr f.issuer.1).length := by
      rw [← htr]
      exact hp.2.2.1
    exact ByteCausality.le_reflect hle htc hcommit (fun _ => hbase) (fun _ => hobs)
      hf (.commitOperand hshared hw hi hr prior ho hp hc)

/-- A frame that leaves the threads and MMA operands untouched and reflects commit observations
only has to reflect the base byte order. -/
theorem ByteCausality.of_same_context (htr : Y.tr = X.tr)
    (hmma : Y.async.mmaOperands = X.async.mmaOperands)
    (hbase : ∀ {l e f}, modelCausality L Y l e f → modelCausality L X l e f)
    (hobs : ∀ {i w acq sc}, AsyncObserved Y i .mmaDone w acq sc →
      AsyncObserved X i .mmaDone w acq sc)
    {l : Loc} {e f : Ref} (h : ByteCausality L Y l e f) : ByteCausality L X l e f := by
  have hget (i : EvId) : X.get i = Y.get i := by simp only [Execution.get, htr]
  refine h.map (retained := fun _ => True) trivial (fun _ => hbase)
    (fun _ intent _ => intent_of_get_eq (hget _) intent)
    (fun _ touch _ => touches_of_get_eq (hget _) touch) ?_
  intro dst i w b k acq sc _ hp issue ⟨v, read⟩ obs
  have hp' : po X w dst.issuer := by simpa only [po, SameAccess, Execution.get, htr] using hp
  exact ⟨trivial, hp', (CommitOperandIssue.congr (hget i) (hget dst.issuer)).mpr issue,
    ⟨v, mmaRead_of_get_eq (hget i) (congrFun hmma i).symm read⟩, hobs obs⟩

end PTX
