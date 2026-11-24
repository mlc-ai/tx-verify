-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Core.Assembly.Execution
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotRmw
import Lemmas.Flow.OpPcsFast
import Lemmas.Kernel.Frame

@[expose] public section

/-! # Structural source exclusions for the dequantizer's raw reads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2

open PTX PTX.Flow PTX.AsyncCopy

private theorem event_in_run {L : Launch} {g : Nat} {t : TState} {es : List Event}
    {o : Option TState} {e : Event} (hr : Run kernel Assumptions.all L g t es o) (he : e ∈ es) :
    ∃ u v, EStep kernel Assumptions.all L g u e v := by
  induction hr with
  | nil => exact (List.not_mem_nil he).elim
  | step _ hf _ ih =>
    rcases List.mem_cons.mp he with rfl | hm
    · exact ⟨_, _, hf⟩
    · exact ih hm
  | last _ hf =>
    cases List.mem_singleton.mp he
    exact ⟨_, _, hf⟩

private theorem instruction_of_step {L : Launch} {g : Nat} {e : Event} {t : TState}
    {o : Option TState} (h : EStep kernel Assumptions.all L g t e o)
    (hn : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ ins, kernel.code[t.pc]? = some ins ∧
      Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨m, hm, hf⟩ := h
  unfold out at hm
  repeat' split at hm
  all_goals
    first
    | (cases hm; exact (hn _ _ hf.1).elim)
    | (cases hm; exact ⟨_, by assumption, hf⟩)
    | cases hm

set_option maxRecDepth 100000 in
private theorem no_other_write_ops :
    OpPcsFast kernel.code (fun op => atomicOp op || bulkOp op || clcOp op) [] = true := by
  decide +kernel

private theorem excluded_event {L : Launch} {mem0 : Mem0} {X : Execution} {i : EvId} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get i = some e) (hn : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hop : ∀ (t : TState) (ins : Instr) (o : Option TState),
      Fires t.pc (eventTmpl Assumptions.all L i.1 t ins.op) e o →
      (atomicOp ins.op || bulkOp ins.op || clcOp ins.op) = true) : False := by
  obtain ⟨_, run⟩ := hX.thr i.1 (Frame.lt_of_get hX he)
  obtain ⟨t, o, hf⟩ := event_in_run run (List.mem_of_getElem? he)
  obtain ⟨ins, hc, hv⟩ := instruction_of_step hf hn
  exact List.not_mem_nil (OpPcsFast.mem no_other_write_ops hc (hop t ins o hv))

/-- Independent of abstract tracking, a write covering a shared raw byte is an ordinary
store or a tensor-load write. -/
theorem raw_read_competing_kinds {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {w : Ref} {a : Acc} {data : List Byte} {l : Loc} (hw : X.MemWrites w a data)
    (hCover : a.Covers l) (hShared : l.space = .shared) :
    (∃ i, w = .thread i ∧ X.Writes i a data) ∨
      ∃ i x y k, w = .async i (.write (.load x y k)) := by
  cases w with
  | thread i =>
    rcases hw with hw | ⟨old, pc, hr⟩
    · exact .inl ⟨i, rfl, hw⟩
    · exact (excluded_event hX hr (by simp)
        (fun _ _ _ hf => by simp [fires_rmw_op hf rfl])).elim
  | async i p =>
    cases p
    case writeLoad x y b => exact .inr ⟨i, x, y, b, rfl⟩
    case writeStore x y b =>
      obtain ⟨o, _, _, _, _, hLoc, _⟩ := hw
      unfold TensorStore.writeLoc at hLoc
      obtain ⟨slot, _, hd⟩ := Option.bind_eq_some_iff.mp hLoc
      obtain ⟨addr, _, hl⟩ := Option.map_eq_some_iff.mp hd
      have hLocal : a.loc.space = .global := (congrArg Loc.space hl).symm
      exact Space.noConfusion (hShared.symm.trans (hCover.1.trans hLocal))
    case writeCopy =>
      obtain ⟨_, ⟨pc, he⟩, _⟩ := hw
      exact (excluded_event hX he (by simp)
        (fun _ _ _ hf => by simp [fires_bulk_op hf rfl])).elim
    case writeElem j =>
      obtain ⟨_, ⟨pc, he⟩, _⟩ := hw
      exact (excluded_event hX he (by simp)
        (fun _ _ _ hf => by simp [fires_bulk_op hf rfl])).elim
    case writeCta c =>
      obtain ⟨_, _, ⟨pc, he⟩, _⟩ := hw
      exact (excluded_event hX he (by simp)
        (fun _ _ _ hf => by simp [fires_clcIssue_op hf rfl])).elim
    all_goals exact hw.elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
