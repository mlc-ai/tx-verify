-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.MmaDrainTmemA
public import Lemmas.Quiet.Base

@[expose] public section

/-! # MMA completion under quiet extensions

`Lemmas/Step/MmaDrainTmemA.lean` under `Assumption.WfQuiet`. -/

namespace PTX
open AsyncCopy MmaSources
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

/-- An MMA with its operands read and its predecessors complete completes. -/
theorem started_mma_inOrderQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hX : Consistent L K A mem0 X) {i : EvId}
    (hs : X.async.mmaStarted i = true) (hn : X.async.mmaDone i = false)
    (hready : TcMma.CompletionReady L X i) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨values, hv⟩ : ∃ values, X.async.mmaOperands i = some values := by
    cases hh : X.async.mmaOperands i with
    | none => simp [Snapshot.mmaStarted, hh] at hs
    | some values => exact ⟨values, rfl⟩
  obtain ⟨ev, hi⟩ : ∃ ev, X.get i = some ev := by
    rcases hX.tma.2.1.1 i hs with ⟨d, s, accum, mask, operands, ⟨pc, hi⟩, _⟩ |
      ⟨c, operands, ⟨pc, hi⟩, _⟩ | ⟨s, operands, ⟨pc, hi⟩, _⟩
    · exact ⟨_, hi⟩
    · exact ⟨_, hi⟩
    · exact ⟨_, hi⟩
  obtain ⟨hg, hlen⟩ := issuer_thread hX hi
  exact ⟨X.completeMma i,
    consistent_completeMma hX hs hn hready (hA.quiet hX (X.le_completeMma i) rfl
        (Execution.quietExt_of_tr rfl)),
    X.le_completeMma i, completeMma_size hv hg hlen hn⟩

/-- An unstarted MMA can use sources justified by base-model ordering. -/
theorem unstarted_mma_tmemAQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) (hnone : X.async.mmaOperands i = none)
    (hready : TcMma.CompletionReady L X i) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  unstarted_mma_tmemA_of_byte_sources (fun _ _ _ _ hle => hA.quiet hX hle rfl
    (Execution.quietExt_of_tr rfl))
    hX hsg hos.byteSources hap hinj hi hnone hready

/-- The base-model source condition is sufficient to complete an unfinished MMA. -/
theorem pending_mma_tmemAQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) (hn : X.async.mmaDone i = false) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  pending_mma_tmemA_of_byte_sources (fun _ _ _ _ hle => hA.quiet hX hle rfl
    (Execution.quietExt_of_tr rfl))
    (fun _ => started_mma_inOrderQ hA hX) hX hsg hos.byteSources hap hinj hi hn

/-- **A maximal execution has completed every MMA**, with A in shared or Tensor Memory, when the
shared operand bytes have sources (`OperandSourcesT`), each MMA's output layout is injective, and
no MMA's Tensor Memory A cell is written by an MMA with the same accumulator
(`TcMma.ATmemApart`). -/
theorem Maximal.mma_all_done_tmemAQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) : X.async.mmaDone i = true := by
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false => exact (hmax.not_grows (pending_mma_tmemAQ hA hmax.1 hsg hos hap hinj hi hn)).elim

/-- **A maximal execution has completed every MMA** when the shared operand bytes of each MMA
that has not read its operands have sources ordered by byte causality (`OperandByteSourcesT`). -/
theorem Maximal.mma_all_done_tmemA_of_byte_sourcesQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandByteSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) : X.async.mmaDone i = true := by
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false =>
    exact (hmax.not_grows (pending_mma_tmemA_of_byte_sources
      (fun _ _ _ _ hle => hA.quiet hmax.1 hle rfl (Execution.quietExt_of_tr rfl))
      (fun _ => started_mma_inOrderQ hA hmax.1) hmax.1 hsg hos hap hinj hi hn)).elim

end

end PTX
