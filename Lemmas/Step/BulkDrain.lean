-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CopyFinishConsistent
public import Lemmas.Step.Object
public import Lemmas.Step.Drain
public import Lemmas.Tcgen05.MmaOperandObservations
public import Lemmas.Async.AsyncMBarrier

@[expose] public section

/-! # A maximal execution has completed every bulk copy whose source is fixed

A proof tool, the bulk-copy counterpart of `Lemmas/Step/TensorDrain`. A bulk copy
(`cp.async.bulk`, non-tensor, completing through an mbarrier) that has not notified its mbarrier
completes in one counted step: it reads the launch content of its source, writes it to its
destination, and its complete-tx is recorded on its mbarrier with the object's checked reply, or its
fault (`Step.checkedRecord`), so no readiness of the object is needed (`pending_copy_extends`). The
step needs the copy to write its destination whole from a memory source that is allocated, covered
by no write and as large as the destination (`BulkSources`), the assumptions to put no
well-formedness constraint on executions (`Assumption.WfFree`), and the
Tensor Core read obligation of the completed execution (`CopyReadOk`), which holds without Tensor
Core reads (`copyReadOk_of_noTcRead`). So a maximal execution has notified every copy that
completes through an mbarrier (`Maximal.bulk_notified`). -/

namespace PTX

open AsyncCopy MBarrier

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Each copy that completes through an mbarrier is a bulk copy from memory: it writes its
destination as one whole, from a memory source of the destination's size, whose bytes are allocated
and covered by no write. -/
def BulkSources (mem0 : Mem0) (X : Execution) : Prop :=
  ∀ i s m, X.Copy i s → s.completion = .mbarrier m →
    s.writes = .whole ∧ s.data = none ∧ s.src.size = s.dst.size ∧ ∀ k < s.src.size,
      mem0 (s.src.loc.at k) ≠ none ∧ ∀ w a bs, X.MemWrites w a bs → ¬ a.Covers (s.src.loc.at k)

/-- The Tensor Core read obligation holds of every completion of a copy of `X` that completes
through an mbarrier, from its launch source, with any record of its notification. -/
def CopyReadOk (L : Launch) (A : List Assumption) (mem0 : Mem0) (X : Execution) : Prop :=
  ∀ i (spec : Spec) m (rec : Record Ref), issuedBy X i = some spec →
    spec.completion = .mbarrier m →
    TcMma.ReadOk L A (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) m rec)

/-- Without MMA issues, Tensor Memory stores, Tensor Core copies and Tensor Core shifts, the
Tensor Core read obligation holds of every copy completion: completing a copy adds no event. -/
theorem copyReadOk_of_noTcRead (h : ∀ i d s accum mask, ¬ X.MmaIssue i d s accum mask)
    (hst : ∀ e a vals sh, ¬ X.TSt e a vals sh) (hcp : ∀ e c, ¬ X.CpIssue e c)
    (hsh : ∀ e s, ¬ X.ShiftIssue e s) : CopyReadOk L A mem0 X := fun _ _ _ _ _ _ =>
  TcMma.readOk_of_no_issue (fun i d s accum mask hi => h i d s accum mask hi)
    (fun e a vals sh hi => hst e a vals sh hi) (fun e c hi => hcp e c hi)
    (fun e s hi => hsh e s hi)

/-- Completing a copy keeps every arrive-on valid: it adds the write of the copy and no
arrive-on. -/
theorem finishCopyRecord_arriveOk {i : EvId} {bs : List Byte} {src : Nat → Option Ref} {m : Loc}
    {rec : Record Ref} (h : ArriveOk X) : ArriveOk (X.finishCopyRecord i bs src m rec) := by
  intro j hj
  refine ⟨(h j hj).1, fun c hc => ?_⟩
  by_cases hci : c = i
  · subst c
    simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy]
  · simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy, hci] using
      (h j hj).2 c hc

/-- **An unnotified copy that completes through an mbarrier extends the execution** by its
completion: a counted consistent extension. -/
theorem pending_copy_extends (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hbs : BulkSources mem0 X) (hrd : CopyReadOk L A mem0 X) {i : EvId} {spec : Spec} {m : Loc}
    (hi : issuedBy X i = some spec) (hm : spec.completion = .mbarrier m)
    (hn : (X.async.copies i).notified = false) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hb : X.Copy i spec := issuedBy_some.mp hi
  obtain ⟨hw, hd, hsize, hsrc⟩ := hbs i spec m hb hm
  obtain ⟨last, hh⟩ := (hX.tma.2.2.1 m).1.2
  let r := Step.checkedRecord (.async i (.notify .copy)) (.completeTx spec.dst.size) last
  have hid : r.id = .async i (.notify .copy) := Step.checkedRecord_id ..
  have hact : r.action = .completeTx spec.dst.size := Step.checkedRecord_action ..
  let bs := initialBytes mem0 X spec.src
  let Y := X.finishCopyRecord i bs (fun _ => none) m r
  have hle : X.le Y := Execution.le_trans
    (finishCopy_initial_extends hX hb hw hd hsize (fun k hk => (hsrc k hk).1)
      (fun k hk => (hsrc k hk).2))
    (Execution.le_appendObject _ _ _)
  have hchecked : CheckedLog (X.objects m ++ [r]) := by
    apply CheckedLog.snoc hh (hX.tma.2.2.1 m).1.1
    · intro hmem
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
      exact no_copy_notification_record hX.tma.2.2.1 hn hq (hqe.trans hid)
    · exact Step.checkedRecord_ok ..
  have htma : TmaOk Y :=
    ⟨finishCopy_wellFormed (src := fun _ => none) hX.tma.1 hi hw hd hm hsize
      (by simp [bs, initialBytes]),
      hX.tma.2.1, finishCopyRecord_objects hX.tma.2.2.1 hi hm hn hid hact hchecked,
      finishCopyRecord_arriveOk hX.tma.2.2.2⟩
  have hsource : ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k) := fun k hk => (hsrc k hk).2
  refine ⟨Y, consistent_finishCopyRecord_initial hX hi hm hw hn hid hsource hle htma
    (hrd i spec m r hi hm) (fun a ha => hA a ha Y), hle, ?_⟩
  obtain ⟨pc, he⟩ := hb
  obtain ⟨hg, hk⟩ := issuer_thread hX he
  exact finishCopy_size (bs := bs) (src := fun _ => none) hg hk hn

/-- **A maximal execution has notified every copy that completes through an mbarrier** whose
source is fixed. -/
theorem Maximal.bulk_notified (hA : Assumption.WfFree L mem0 A) (hmax : Maximal L K A mem0 X)
    (hbs : BulkSources mem0 X) (hrd : CopyReadOk L A mem0 X) {i : EvId} {s : Spec}
    {m : Loc} (hb : X.Copy i s) (hm : s.completion = .mbarrier m) :
    (X.async.copies i).notified = true := by
  cases hn : (X.async.copies i).notified with
  | true => rfl
  | false =>
    exact (hmax.not_grows (pending_copy_extends hA hmax.1 hbs hrd
      (issuedBy_some.mpr hb) hm hn)).elim

end

end PTX
