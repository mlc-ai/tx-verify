-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.LaunchOffsets

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX

private theorem final_requires_writer {L : Launch} {X : Execution} {mem : Mem0} {l : Loc}
    {v : Byte} (written : ∃ w a bs, X.MemWrites w a bs ∧ a.Covers l)
    (frame : ∀ m, IsFinal L mem X m → m l = some (some v)) :
    ∃ w a bs, X.MemWrites w a bs ∧ a.Covers l ∧ wbyte a bs l = some v := by
  classical
  obtain ⟨m,final⟩ := final_exists (L := L) (mem0 := mem) X
  obtain ⟨co,order,atLoc⟩ := final
  have expected := frame m ⟨co,order,atLoc⟩
  by_contra missing
  let other : FinalMem := fun u => if u = l then none else m u
  have altered : IsFinal L mem X other := by
    refine ⟨co,order,fun u => ?_⟩
    by_cases same : u = l
    · subst u
      obtain ⟨last,untouched,maximal⟩ := atLoc l
      refine ⟨fun w a bs h hit top => ?_,fun absent => ?_,fun b existsMax agree => ?_⟩
      · exact (missing ⟨w,a,bs,h,hit,Option.some.inj
          ((last w a bs h hit top).symm.trans expected)⟩).elim
      · obtain ⟨w,a,bs,h,hit⟩ := written
        exact (absent w a bs h hit).elim
      · have eq := Option.some.inj ((maximal b existsMax agree).symm.trans expected)
        obtain ⟨w,wm⟩ := existsMax
        obtain ⟨a,bs,h,hit⟩ := wm.1
        exact (missing ⟨w,a,bs,h,hit,(agree w a bs wm h).trans eq⟩).elim
    · simpa only [other,ite_eq_right same] using atLoc u
  simpa [other] using frame other altered

def OffsetRewritten (X : Execution) : Prop :=
  ∃ last i bs k w dst data restore dst' data',
    X.get (129,i) = some ⟨loadPc last,.rd (offsetAccess last) bs⟩ ∧ k < 8 ∧
    X.rf (.thread (129,i)) k = some w ∧
    X.MemWrites w dst data ∧ dst.Covers ((offsetAccess last).loc.at k) ∧
    wbyte dst data ((offsetAccess last).loc.at k) ≠ some ((offsetValue last).byteAt k) ∧
    X.MemWrites restore dst' data' ∧ dst'.Covers ((offsetAccess last).loc.at k) ∧
    wbyte dst' data' ((offsetAccess last).loc.at k) = some ((offsetValue last).byteAt k) ∧
    w ≠ restore

theorem correctness_requires_two_writes (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (p : Problem) (b : Workspace.Bases) (input : Workspace.Inputs p b mem)
    (present : 0 < p.sequences) (one : p.length 0 = 1) (address : b.sequenceOffsets = 65536)
    (host : L.params (Prologue.param 15) = some 65536) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) (origin : L.ctaidOf (129/L.block) = ⟨0,0,0⟩)
    (ctas : 0 < L.grid) (grid : L.clusterGridValid)
    (output : 65552 ≤ p.outputBase) (state : 65552 ≤ p.stateBase)
    (correct : Correct kernel (Prologue.assumptions base) L mem (Post p mem)) :
    ∃ X, Consistent L kernel (Prologue.assumptions base) mem X ∧ Complete L X ∧
      X.Elect (129,0) 32 0xffffffff 0 1 ∧ OffsetRewritten X := by
  have init := offset_memory_of_inputs input present one address
  obtain ⟨X,valid,done,first,last,i,bs,k,w,_,_,read,inside,source,_,_,diff⟩ :=
    correctness_requires_changed_offset base L mem _ correct init host block threads
      origin ctas grid
  have actual : X.MemReads (.thread (129,i)) (offsetAccess last) bs := .inl ⟨_,read⟩
  have value := (valid.rf _ _ _ actual).2 k inside
  rw [source] at value
  obtain ⟨dst,data,wrote,hit,got⟩ := value
  let l := (offsetAccess last).loc.at k
  have frame : ∀ m, IsFinal L mem X m → m l = some (some ((offsetValue last).byteAt k)) := by
    intro m h
    have post := correct.result (valid_launch L grid block) X m valid done h
    refine (post.2.2 l rfl ?_).trans (init last k inside)
    cases last <;> simp [l,offsetAccess,offsetLoc,Loc.at] <;> omega
  obtain ⟨restore,dst',data',restored,covers,expected⟩ :=
    final_requires_writer ⟨w,dst,data,wrote,hit⟩ frame
  have different : wbyte dst data l ≠ some ((offsetValue last).byteAt k) :=
    fun eq => diff (got.trans (congrArg some eq))
  refine ⟨X,valid,done,first,last,i,bs,k,w,dst,data,restore,dst',data',
    read,inside,source,wrote,hit,different,restored,covers,expected,?_⟩
  rintro rfl
  obtain ⟨⟨loc,_⟩,rfl⟩ := Execution.MemWrites.unique wrote restored
  exact different (by simpa only [wbyte,loc] using expected)

end FlashKda.Packed.ProducerControl
