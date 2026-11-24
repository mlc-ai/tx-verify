-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.OffsetTransfers
public import Kernels.FlashKdaFwd.Packed.Producer.Coverage

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Flow

private theorem kinds {pc : Nat} {i : Instr} (site : kernel.code[pc]? = some i) :
    bulkOp i.op = false ∧ clcOp i.op = false ∧ atomicOp i.op = false ∧
    (writeOp i.op = true → 379 < pc) := by
  have h := (certified site).2
  simp only [memorySite,Bool.and_eq_true,Bool.not_eq_true',Bool.or_eq_false_iff,
    Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨bulk,clc⟩,atomic⟩,write⟩,_⟩ := h
  exact ⟨bulk,clc,atomic,fun yes => write.resolve_left (by simp [yes])⟩

variable {base : Nat → Nat → Nat} {L : Launch} {mem : Mem0} {X : Execution}

private theorem no_copy (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    {i : EvId} {s : AsyncCopy.Spec} (copy : X.Copy i s) : False := by
  obtain ⟨pc,ev⟩ := copy
  rcases get_source valid ev with ⟨_,h⟩ | ⟨_,ins,_,_,site,fire⟩
  · cases h
  · have h := fires_bulk_op fire rfl
    rw [(kinds site).1] at h
    contradiction

private theorem no_cancel (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    {i : EvId} {s : Clc.Spec} {targets : List Nat} (cancel : X.ClcIssue i s targets) : False := by
  obtain ⟨pc,ev⟩ := cancel
  rcases get_source valid ev with ⟨_,h⟩ | ⟨_,ins,_,_,site,fire⟩
  · cases h
  · have h := clcIssuesTo_of_op (m := s.mbar) (kinds site).2.1 fire
    simp [clcIssuesTo] at h

theorem offset_writer_site (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (maps : MapsAboveOffsets L) {w : AsyncCopy.Ref} {dst : Acc} {data : List Byte}
    (wrote : X.MemWrites w dst data) {last : Bool} {k : Nat} (inside : k < 8)
    (hit : dst.Covers ((offsetAccess last).loc.at k)) :
    ∃ e pc, w = .thread e ∧ X.get e = some ⟨pc,.wr dst data⟩ ∧ 379 < pc := by
  cases w with
  | thread e =>
    rcases wrote with ⟨pc,ev⟩ | ⟨old,pc,ev⟩
    · rcases get_source valid ev with ⟨_,h⟩ | ⟨_,ins,_,_,site,fire⟩
      · cases h
      · exact ⟨e,pc,rfl,ev,(kinds site).2.2.2 (fires_write_op fire rfl)⟩
    · rcases get_source valid ev with ⟨_,h⟩ | ⟨_,ins,_,_,site,fire⟩
      · cases h
      · have h := fires_rmw_op fire rfl
        rw [(kinds site).2.2.1] at h
        contradiction
  | async i part =>
    have nt := offset_writer_not_tensor valid maps wrote inside hit
    exfalso
    cases part <;> try exact wrote
    case writeLoad => exact nt trivial
    case writeStore => exact nt trivial
    case writeCopy => exact no_copy valid wrote.choose_spec.1
    case writeElem => exact no_copy valid wrote.choose_spec.1
    case writeCta =>
      obtain ⟨_,_,issue,_⟩ := wrote
      exact no_cancel valid issue

theorem changed_offset_unordered (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (maps : MapsAboveOffsets L) (changed : ChangedOffsetRead X) :
    ∃ last i bs k e pc dst data, X.get (129,i) = some ⟨loadPc last,.rd (offsetAccess last) bs⟩ ∧
      k < 8 ∧ X.rf (.thread (129,i)) k = some (.thread e) ∧
      X.get e = some ⟨pc,.wr dst data⟩ ∧ 379 < pc ∧ dst.Covers ((offsetAccess last).loc.at k) ∧
      ¬baseCausality L X (129,i) e := by
  obtain ⟨last,i,bs,k,w,dst,data,read,inside,source,wrote,hit,_⟩ := changed
  obtain ⟨e,pc,rfl,event,late⟩ := offset_writer_site valid maps wrote inside hit
  have actual : X.MemReads (.thread (129,i)) (offsetAccess last) bs := .inl ⟨_,read⟩
  refine ⟨last,i,bs,k,e,pc,dst,data,read,inside,source,event,late,hit,fun sync => ?_⟩
  exact valid.noFuture _ _ _ _ _ actual inside source (.direct (.inl sync))

end FlashKda.Packed.ProducerControl
