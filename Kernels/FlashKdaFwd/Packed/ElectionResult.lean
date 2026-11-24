-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.OffsetWriters
public import Kernels.FlashKdaFwd.Packed.Producer.BarrierOrdering

@[expose] public section
namespace FlashKda.Packed
open PTX ProducerControl

private theorem startup_sites : StartupSites := by
  intro pc i site
  have h := (certified site).2
  simp only [memorySite,Bool.and_eq_true] at h
  exact h.2

private theorem no_arrive : kernel.NoBarArrive := by
  apply List.all_eq_true.mpr
  intro i member
  obtain ⟨pc,site⟩ := List.mem_iff_getElem?.mp member
  have h := (startup_sites pc i site).2
  simp only [barrierSite,Bool.and_eq_true] at h
  exact h.1

theorem no_completion_with_lane_one {base : Nat → Nat → Nat} {L : Launch} {mem : Mem0}
    {X : Execution} (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (first : X.Elect (129,0) 32 0xffffffff 0 1) (init : OffsetMemory mem)
    (maps : MapsAboveOffsets L) (host : L.params (Prologue.param 15) = some 65536)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩)
    (origin : L.ctaidOf (129/L.block) = ⟨0,0,0⟩) (ctas : L.grid = 1) : ¬Complete L X := by
  intro done
  have ex : ∃ p, (X.tr 129).getLast? = some ⟨p,.exit⟩ := by
    rcases done.1 129 ((valid.elect.1 _ _ _ _ _ first).1) with canceled | exit
    · simp [Execution.Elect,Execution.get,canceled.1] at first
    · exact exit
  obtain ⟨p,last⟩ := ex
  have changed := changed_offset_of_exit base L mem X valid first init host block threads
    origin last
  obtain ⟨last,i,bs,_,e,pc,dst,data,read,_,_,write,late,_,unordered⟩ :=
    changed_offset_unordered valid maps changed
  exact unordered (offset_before_write valid done startup_sites no_arrive block ctas
    read (by cases last <;> decide) write late)

theorem election_without_completion (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (init : OffsetMemory mem) (maps : MapsAboveOffsets L)
    (host : L.params (Prologue.param 15) = some 65536) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) (origin : L.ctaidOf (129/L.block) = ⟨0,0,0⟩)
    (ctas : L.grid = 1) (grid : L.clusterGridValid) :
    Consistent L kernel (Prologue.assumptions base) mem (Election.initialElection 1) ∧
    ∀ X, (Election.initialElection 1).le X →
      Consistent L kernel (Prologue.assumptions base) mem X → ¬Complete L X := by
  refine ⟨Entry.consistent_election base L mem 1 65536 host block threads (by omega) grid,?_⟩
  intro X extendsTrace valid
  have first : (Election.initialElection 1).Elect (129,0) 32 0xffffffff 0 1 := by
    simp [Execution.Elect,Execution.get,Election.initialElection,Election.warpTrace]
  exact no_completion_with_lane_one valid (Execution.le_get extendsTrace first) init maps host
    block threads origin ctas

theorem not_correct_one_block (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (post : FinalMem → Prop) (init : OffsetMemory mem) (maps : MapsAboveOffsets L)
    (host : L.params (Prologue.param 15) = some 65536) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) (origin : L.ctaidOf (129/L.block) = ⟨0,0,0⟩)
    (ctas : L.grid = 1) (grid : L.clusterGridValid) :
    ¬Correct kernel (Prologue.assumptions base) L mem post := by
  intro correct
  obtain ⟨reachable,stuck⟩ := election_without_completion base L mem init maps host block threads
    origin ctas grid
  obtain ⟨X,valid,ext,done⟩ :=
    correct.complete_extension (valid_launch L grid block) reachable
  exact stuck X ext valid done

theorem no_correct_single_token (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (p : Problem) (b : Workspace.Bases) (inputs : Workspace.Inputs p b mem)
    (present : 0 < p.sequences) (one : p.length 0 = 1) (address : b.sequenceOffsets = 65536)
    (maps : MapsAboveOffsets L) (host : L.params (Prologue.param 15) = some 65536)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩)
    (origin : L.ctaidOf (129/L.block) = ⟨0,0,0⟩) (ctas : L.grid = 1) (grid : L.clusterGridValid) :
    ¬Correct kernel (Prologue.assumptions base) L mem (Post p mem) :=
  not_correct_one_block base L mem _ (offset_memory_of_inputs inputs present one address)
    maps host block threads origin ctas grid

end FlashKda.Packed
