-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.Async.AsyncOrigins

@[expose] public section

/-! Completing an issued MMA preserves every existing observation. The caller supplies
operand values and read sources, and separately proves consistency; no kernel shape,
phase number or writer-count condition is imposed here. -/
namespace PTX
open AsyncCopy
noncomputable section

def Execution.finishMma (X : Execution) (i : EvId) (values : MmaOperands)
    (ra rb : Nat → Option Ref) : Execution :=
  { X with
    rf := fun e offset => match e with
      | .async j (.mmaRead isB k) =>
        if j = i ∧ offset = 0 then (if isB then rb k else ra k) else X.rf e offset
      | _ => X.rf e offset
    async := { X.async with
      mmaOperands := fun j => if j = i then some values else X.async.mmaOperands j
      mmaDone := fun j => if j = i then true else X.async.mmaDone j } }

theorem Execution.le_finishMma {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref}
    (hv : ∀ old, X.async.mmaOperands i = some old → old = values)
    (ha : ∀ k a bs, X.MemReads (.async i (.mmaRead false k)) a bs →
      ra k = X.rf (.async i (.mmaRead false k)) 0)
    (hb : ∀ k a bs, X.MemReads (.async i (.mmaRead true k)) a bs →
      rb k = X.rf (.async i (.mmaRead true k)) 0) :
    X.le (X.finishMma i values ra rb) := by
  refine ⟨fun _ => List.prefix_refl _, ?_, ?_, (Execution.le_refl X).2.2.2⟩
  · rintro e offset ⟨a, bs, hr⟩
    cases e with
    | thread j => rfl
    | async j p =>
      cases p <;> try rfl
      case mmaRead isB k =>
        simp only [finishMma]
        split_ifs with h hB
        · obtain ⟨rfl, rfl⟩ := h
          subst hB
          exact hb _ _ _ hr
        · obtain ⟨rfl, rfl⟩ := h
          simp only [Bool.not_eq_true] at hB
          subst hB
          exact ha _ _ _ hr
        · rfl
  · refine ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, ?_, ?_, fun _ h => h, fun _ _ _ h => h,
      fun _ _ _ h => h⟩
    · intro j old hj
      by_cases hi : j = i
      · subst j; simp [finishMma, hv old hj]
      · simpa [finishMma, hi] using hj
    · intro j hj
      by_cases hi : j = i
      · simp [finishMma, hi]
      · simpa [finishMma, hi] using hj

private theorem finishMma_tcEffectsOk_of_issue {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} (ht : TcEffectsOk X)
    (hi : (∃ d s accum mask, X.MmaIssue i d s accum mask ∧ TcMma.Valid s.descriptor ∧
      values.a.length = TcMma.Operand.a.bytes s.descriptor ∧
      values.b.length = TcMma.Operand.b.bytes s.descriptor) ∨
      (∃ c, X.CpIssue i c ∧ values.a.length = c.ctas.length * c.shape.sourceBytes ∧
        values.b = [])) :
    TcEffectsOk (X.finishMma i values ra rb) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    by_cases he : j = i
    · subst j
      rcases hi with ⟨d, s, accum, mask, hissue, hv, ha, hb⟩ | ⟨c, hissue, ha, hb⟩
      · exact .inl ⟨d, s, accum, mask, values, hissue, by simp [Execution.finishMma], hv, ha, hb⟩
      · exact .inr (.inl ⟨c, values, hissue, by simp [Execution.finishMma], ha, hb⟩)
    · have hs : X.async.mmaStarted j = true := by
        simpa only [Execution.finishMma, Snapshot.mmaStarted, ite_eq_right he] using hj
      rcases ht.1 j hs with ⟨d', s', accum', mask', operands, hi', hop, hvalid, ha', hb'⟩ |
        ⟨c, operands, hc, hop, ha', hb'⟩ | ⟨a, operands, hc, hop, ha', hb'⟩
      · exact .inl ⟨d', s', accum', mask', operands, hi',
          by simpa [Execution.finishMma, he] using hop, hvalid, ha', hb'⟩
      · exact .inr (.inl ⟨c, operands, hc,
          by simpa [Execution.finishMma, he] using hop, ha', hb'⟩)
      · exact .inr (.inr ⟨a, operands, hc,
          by simpa [Execution.finishMma, he] using hop, ha', hb'⟩)
  · intro j hj
    by_cases he : j = i
    · simp [Execution.finishMma, Snapshot.mmaStarted, he]
    · have hd : X.async.mmaDone j = true := by simpa [Execution.finishMma, he] using hj
      simpa only [Execution.finishMma, Snapshot.mmaStarted, ite_eq_right he] using ht.2 j hd

theorem finishMma_tcEffectsOk {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} {d : Nat} {s : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (ht : TcEffectsOk X) (hi : X.MmaIssue i d s accum mask)
    (hv : TcMma.Valid s.descriptor)
    (ha : values.a.length = TcMma.Operand.a.bytes s.descriptor)
    (hb : values.b.length = TcMma.Operand.b.bytes s.descriptor) :
    TcEffectsOk (X.finishMma i values ra rb) :=
  finishMma_tcEffectsOk_of_issue ht (.inl ⟨d, s, accum, mask, hi, hv, ha, hb⟩)

/-- A Tensor Memory copy captures just the bytes of its source operands. -/
theorem finishCp_tcEffectsOk {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} {c : TcCopy.Spec}
    (ht : TcEffectsOk X) (hi : X.CpIssue i c)
    (ha : values.a.length = c.ctas.length * c.shape.sourceBytes) (hb : values.b = []) :
    TcEffectsOk (X.finishMma i values ra rb) :=
  finishMma_tcEffectsOk_of_issue ht (.inr ⟨c, hi, ha, hb⟩)

/-- Completing an MMA does not perform any generic or bulk-copy write. -/
theorem finishMma_memWrites {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} {e : Ref} {a : Acc} {bs : List Byte} :
    (X.finishMma i values ra rb).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p => cases p <;> rfl

/-- Recording new operand reads cannot change an older visibility path when
this operation had not completed. A new interior vertex would need an outgoing
completion observation, which CommitOk excludes before completion. -/
theorem finishMma_modelCausality {L : Launch} {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} (hc : CommitOk X) (hn : X.async.mmaDone i=false)
    {l : Loc} {e f : Ref} :
    modelCausality L (X.finishMma i values ra rb) l e f ↔ modelCausality L X l e f := by
  have hs : ∀ j k, ∀ q ∈ GroupWaitStages X j k,
      ((X.finishMma i values ra rb).AsyncPresent j q ↔ X.AsyncPresent j q) := by
    intro j k q hq
    unfold GroupWaitStages at hq
    split at hq <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq <;>
      rcases hq with rfl | rfl <;> exact Iff.rfl
  have hf : ∀ j p w, AsyncFinished L (X.finishMma i values ra rb) j p w ↔
      AsyncFinished L X j p w := by
    intro j p w
    unfold AsyncFinished
    refine or_congr (exists_congr fun k => and_congr Iff.rfl (and_congr Iff.rfl ?_)) Iff.rfl
    exact ⟨fun h q hq => (hs j k q hq).mp (h q hq), fun h q hq => (hs j k q hq).mpr (h q hq)⟩
  have ho : ∀ j p w, AsyncOnlyFinished (X.finishMma i values ra rb) j p w ↔
      AsyncOnlyFinished X j p w := by
    intro j p w
    unfold AsyncOnlyFinished
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    exact ⟨fun h q hq => (hs j _ q hq).mp (h q hq), fun h q hq => (hs j _ q hq).mpr (h q hq)⟩
  have hd : ∀ a b, AsyncBefore L (X.finishMma i values ra rb) l a b ↔
      AsyncBefore L X l a b := fun a b => by
    unfold AsyncBefore
    simp only [hf, ho]
    exact Iff.rfl
  have hp : ∀ a b, AsyncBefore L (X.finishMma i values ra rb) l a b →
      ((X.finishMma i values ra rb).AsyncPresent a.1 a.2 ↔ X.AsyncPresent a.1 a.2) := by
    rintro ⟨j,p⟩ b edge
    by_cases hj : j=i
    · subst j
      cases p <;> first
        | rfl
        | (solve | obtain ⟨acc,w,hi,_⟩ := edge.1; cases hi.2)
        | (have edge' := (hd _ _).mp edge
           rcases edge'.2.2 with ⟨w,⟨k,hv,-⟩ | ⟨ws,obs,-⟩,_⟩ | ⟨w,honly,_⟩
           · cases k <;> first | cases hv | (rename_i m; cases m <;> cases hv)
           · have hdone := (mma_done_waits (L := L) hc
               (obs : AsyncObserved X i .mmaDone w true ws)).1
             rw [hn] at hdone
             cases hdone
           · cases honly.1)
    · cases p <;> simp only [Execution.AsyncPresent,Execution.MmaRead,Execution.finishMma,
        ite_eq_right hj]
      all_goals rfl
  cases e with
  | thread e => cases f <;> rfl
  | async e p =>
    cases f with
    | thread f =>
      exact and_congr Iff.rfl (exists_congr fun w => and_congr (hf _ _ _) (by
        cases p <;> rfl))
    | async f q => exact and_congr_right fun _ => AsyncChain.congr_on_edges hd hp

end
end PTX
