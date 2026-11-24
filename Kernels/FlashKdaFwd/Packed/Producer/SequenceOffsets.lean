-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.Preparation
public import Kernels.FlashKdaFwd.Packed.Producer.OffsetRegisters
public import Kernels.FlashKdaFwd.Packed.Prefix
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.ReturningPrefix

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof

theorem no_exit_from_offsets (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0) (X : Execution)
    (consistent : Consistent L kernel (Prologue.assumptions base) mem X)
    (firstElection : X.Elect (129,0) 32 0xffffffff 0 1)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩) {t : TState}
    (pc : t.pc = 301) (clear : t.fault = none) (startOffset : t.regs 2248 = some (.bits 64 0))
    (endOffset : t.regs 2249 = some (.bits 64 1)) (threadId : t.regs 307 = some (b32 129))
    (elected : t.regs 88 = some (.pred false)) {before es : List Event} {o : Option TState}
    (history : X.tr 129 = before ++ es) (trace : Run kernel (Prologue.assumptions base) L 129
      t es o) {j : Nat} {e : Event} (atIndex : es[j]? = some e) : e.kind ≠ .exit := by
  obtain ⟨s,steps,pos,good,mask,len,sameTid,flag⟩ :=
    offsets_to_election base L t pc clear startOffset endOffset
  have next : Next kernel (Prologue.assumptions base) L 129 t s
      (.elect 0xffffffff (secondResult L s)) :=
    ⟨run_rtg steps,second_election base L s pos good mask⟩
  cases es with
  | nil => simp at atIndex
  | cons elect rest =>
    have continues : ¬ Fires s.pc (.elect 0xffffffff (secondResult L s)) elect none := by
      rintro ⟨_,_,_,h⟩; cases h
    obtain ⟨u,⟨inst,leader,event,result⟩,tail⟩ := next.continuing_event continues trace
    have later : X.Elect (129,before.length) 312 0xffffffff inst leader := by
      simp [Execution.Elect,Execution.get,history,event,pos]
    have live := (consistent.elect.1 _ _ _ _ _ firstElection).1
    have same : 1 = leader := consistent.elect.2.2 _ _ _ _ _ _ _ _ _ firstElection later
      ⟨⟨live,live,rfl⟩,rfl⟩
    subst leader
    cases Option.some.inj result
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atIndex
      subst e
      simp [event]
    | succ j =>
      have recorded : rest[j]? = some e := atIndex
      obtain ⟨v,advance,at315,_,selected,carried,identifier,remember⟩ :=
        selected_after base L s block pos good
      have rest' := tail.after_local_nonempty (run_rtg advance) (fun h => by simp [h] at recorded)
      have tid : (L.tidOf 129).x = 129 := by rw [Launch.tidOf,block,threads]; rfl
      exact no_exit_after_producer_selection base L tid at315
        ⟨identifier.trans (sameTid.trans threadId),selected,carried.trans len,
          remember.trans (flag.trans elected)⟩ rest' recorded

theorem no_exit_after_offset_reads (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (X : Execution) (consistent : Consistent L kernel (Prologue.assumptions base) mem X)
    (firstElection : X.Elect (129,0) 32 0xffffffff 0 1)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩) {t : TState}
    (pc : t.pc = 117) (clear : t.fault = none) (sequence : t.regs 309 = some (b32 0))
    (startOffset : t.regs 2248 = some (.bits 64 0)) (endOffset : t.regs 2249 = some (.bits 64 1))
    (threadId : t.regs 307 = some (b32 129)) (elected : t.regs 88 = some (.pred false))
    {before es : List Event} {o : Option TState} (history : X.tr 129 = before ++ es)
    (trace : Run kernel (Prologue.assumptions base) L 129 t es o)
    {j : Nat} {e : Event} (atIndex : es[j]? = some e) : e.kind ≠ .exit := by
  obtain ⟨s,steps,at301,good,begins,ends,idReg,flag⟩ :=
    first_sequence_offsets base L t pc clear sequence
  have rest := trace.after_local_nonempty (run_rtg steps) (fun h => by simp [h] at atIndex)
  exact no_exit_from_offsets base L mem X consistent firstElection block threads at301 good
    (begins.trans startOffset) (ends.trans endOffset) (idReg.trans threadId) (flag.trans elected)
    history rest atIndex

theorem no_correct_extension_of_offset_reads (base : Nat → Nat → Nat) (L : Launch)
    (mem : Mem0) (Y : Execution) (consistent : Consistent L kernel (Prologue.assumptions base)
      mem Y) (firstElection : Y.Elect (129,0) 32 0xffffffff 0 1)
    (grid : L.clusterGridValid) (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩)
    {t : TState} (run : Run kernel (Prologue.assumptions base) L 129 {} (Y.tr 129) (some t))
    {read : Event} (lastRead : (Y.tr 129).getLast? = some read)
    (readKind : read.kind ≠ .exit) (pc : t.pc = 117) (clear : t.fault = none)
    (sequence : t.regs 309 = some (b32 0)) (startOffset : t.regs 2248 = some (.bits 64 0))
    (endOffset : t.regs 2249 = some (.bits 64 1)) (threadId : t.regs 307 = some (b32 129))
    (elected : t.regs 88 = some (.pred false)) (post : FinalMem → Prop) :
    ¬ Correct kernel (Prologue.assumptions base) L mem post := by
  intro correct
  obtain ⟨X,valid,extension,complete⟩ := correct.complete_extension (valid_launch L grid block)
    consistent
  have first : X.Elect (129,0) 32 0xffffffff 0 1 := Execution.le_get extension firstElection
  have live := (valid.elect.1 _ _ _ _ _ first).1
  obtain ⟨es,history⟩ := extension.1 129
  obtain ⟨o,full⟩ := valid.thr 129 live
  rw [← history] at full
  have tail := run.after_returned_prefix full
  rcases complete.1 129 live with cancelled | ⟨last,hLast⟩
  · have h := first
    simp [Execution.Elect,Execution.get,cancelled.1] at h
  · rw [← history,List.getLast?_append,lastRead] at hLast
    cases endOfTail : es.getLast? with
    | none =>
      simp only [endOfTail,Option.or] at hLast
      cases Option.some.inj hLast
      exact readKind rfl
    | some lastEvent =>
      simp only [endOfTail,Option.or,Option.some.injEq] at hLast
      subst lastEvent
      rw [List.getLast?_eq_getElem?] at endOfTail
      exact no_exit_after_offset_reads base L mem X valid first block threads pc clear sequence
        startOffset endOffset threadId elected history.symm tail endOfTail rfl

end FlashKda.Packed.ProducerControl
