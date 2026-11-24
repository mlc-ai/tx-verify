-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.Startup
public import Kernels.FlashKdaFwd.Packed.Producer.StartupAddress
public import Kernels.FlashKdaFwd.Packed.Producer.OffsetMemory
public import Kernels.FlashKdaFwd.Packed.Workspace
import all Kernels.FlashKdaFwd.Packed.Producer.Preparation

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof

theorem offset_memory_of_inputs {p : Problem} {b : Workspace.Bases} {mem : Mem0}
    (input : Workspace.Inputs p b mem) (present : 0 < p.sequences) (one : p.length 0 = 1)
    (address : b.sequenceOffsets = 65536) : OffsetMemory mem := by
  intro last k hk
  cases last with
  | false =>
    simpa [offsetAccess,offsetLoc,offsetValue,Loc.at,b64,Batches.firstToken,address]
      using input.2.1 0 (Nat.zero_le _) k hk
  | true =>
    have endToken : Batches.firstToken p.length 1 = 1 := by
      rw [show 1 = 0+1 by rfl,Batches.firstToken_succ]
      simp [Batches.firstToken,one]
    have h := input.2.1 1 present k hk
    rw [endToken] at h
    simpa [offsetAccess,offsetLoc,offsetValue,Loc.at,b64,address] using h

theorem changed_offset_of_exit (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0) (X : Execution)
    (consistent : Consistent L kernel (Prologue.assumptions base) mem X)
    (first : X.Elect (129,0) 32 0xffffffff 0 1) (init : OffsetMemory mem)
    (host : L.params (Prologue.param 15) = some 65536) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) (origin : L.ctaidOf (129/L.block) = ⟨0,0,0⟩) {p : Nat}
    (exited : (X.tr 129).getLast? = some ⟨p,.exit⟩) : ChangedOffsetRead X := by
  by_contra untouched
  obtain ⟨earlier,hist⟩ := List.getLast?_eq_some_iff.mp exited
  have firstEvent := first
  change (X.tr 129)[0]? = some _ at firstEvent
  cases earlier with
  | nil => simp [hist] at firstEvent
  | cons chosen xs =>
    simp only [hist,List.cons_append,List.getElem?_cons_zero,Option.some.injEq] at firstEvent
    subst chosen
    have live := (consistent.elect.1 _ _ _ _ _ first).1
    obtain ⟨o,full⟩ := consistent.thr 129 live
    rw [hist] at full
    obtain ⟨t,u,one,silent,pc,ready⟩ := elected_input_state base L block threads host
    have after : Run kernel (Prologue.assumptions base) L 129 t (xs ++ [⟨p,.exit⟩]) o :=
      one.after_returned_prefix full
    have trace := after.after_local_nonempty (run_rtg silent) (by simp)
    obtain ⟨s,q,path,fire⟩ := trace.before_event
      (show (xs ++ [(⟨p,.exit⟩ : Event)])[xs.length]? = some ⟨p,.exit⟩ by simp)
    simp only [List.take_left] at path
    obtain ⟨pre,tail,v,splitTrace,at111,facts,suffix⟩ :=
      cut_at_offsets ready (by omega) (by omega) path fire rfl
    obtain ⟨w,steps,pos,addr,seqNo,idReg,leader,scalar,fresh,clear⟩ :=
      find_offsets base L v at111 origin facts
    have run := (record suffix fire).after_local_nonempty steps (by simp)
    have history : X.tr 129 = (⟨32,.elect 0xffffffff 0 1⟩ :: pre) ++ (tail ++ [⟨p,.exit⟩]) := by
      simp [hist,splitTrace,List.append_assoc]
    exact no_exit_before_offset_reads base L mem X consistent first init untouched block threads
      pos clear scalar fresh addr seqNo idReg leader history run
      (show (tail ++ [(⟨p,.exit⟩ : Event)])[tail.length]? = some ⟨p,.exit⟩ by simp) rfl

theorem correctness_requires_changed_offset (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (post : FinalMem → Prop) (correct : Correct kernel (Prologue.assumptions base) L mem post)
    (init : OffsetMemory mem) (host : L.params (Prologue.param 15) = some 65536)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩) (origin : L.ctaidOf (129/L.block) =
      ⟨0,0,0⟩) (ctas : 0 < L.grid) (grid : L.clusterGridValid) :
    ∃ X, Consistent L kernel (Prologue.assumptions base) mem X ∧ Complete L X ∧
      X.Elect (129,0) 32 0xffffffff 0 1 ∧ ChangedOffsetRead X := by
  let lane : Fin 32 := ⟨1,by decide⟩
  obtain ⟨X,valid,finished,selected⟩ :=
    Entry.completion_with_leader base L mem post correct lane 65536 host block threads ctas grid
  have initial : X.Elect (129,0) 32 0xffffffff 0 1 := selected lane
  rcases finished.1 129 ((valid.elect.1 _ _ _ _ _ initial).1) with cancelled | ⟨p,last⟩
  · have h := initial
    simp [Execution.Elect,Execution.get,cancelled.1] at h
  · exact ⟨X,valid,finished,initial,changed_offset_of_exit base L mem X valid initial init
      host block threads origin last⟩

theorem no_correct_with_readonly_offsets (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (p : Problem) (b : Workspace.Bases) (input : Workspace.Inputs p b mem)
    (present : 0 < p.sequences) (one : p.length 0 = 1) (address : b.sequenceOffsets = 65536)
    (host : L.params (Prologue.param 15) = some 65536) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) (origin : L.ctaidOf (129/L.block) = ⟨0,0,0⟩)
    (ctas : 0 < L.grid) (grid : L.clusterGridValid)
    (readonly : ∀ X, Consistent L kernel (Prologue.assumptions base) mem X →
      Complete L X → ¬OffsetWrite X) : ¬Correct kernel (Prologue.assumptions base) L mem
      (Post p mem) := by
  intro correct
  obtain ⟨X,valid,finished,_,changed⟩ := correctness_requires_changed_offset base L mem _
    correct (offset_memory_of_inputs input present one address) host block threads origin ctas grid
  exact readonly X valid finished (changed_writes_input changed)

end FlashKda.Packed.ProducerControl
