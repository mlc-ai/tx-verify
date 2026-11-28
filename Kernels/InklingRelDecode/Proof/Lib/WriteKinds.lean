-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotRmw

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

private theorem noAtomic : kernel.code.all (fun ins => !atomicOp ins.op) = true := by decide +kernel

/-- Every memory writer in a consistent execution is a thread store or a byte of
a tensor load. This includes all asynchronous slots and read-modify-write events. -/
theorem write_kinds {L m X ref a bs} (hX : Consistent L kernel Assumptions.all m X)
    (hw : X.MemWrites ref a bs) :
    (∃ i pc, ref=.thread i ∧ X.get i=some ⟨pc,.wr a bs⟩) ∨
    ∃ i x y z addr sp, ref=.async i (.write (.load x y z)) ∧ X.TensorIssue i addr sp ∧
      TensorCopy.writeLoc sp x y z=some a.loc ∧ a.size=1 := by
  rcases ref with i|⟨i,part⟩
  · rcases hw with ⟨pc,get⟩|⟨old,pc,get⟩
    · exact .inl ⟨_,_,rfl,get⟩
    · exact (no_kind_of_code hX atomicOp (fun k => ∃ dst o n, k=.rmw dst o n)
        (fun _ ⟨_,_,_,eq⟩ => by cases eq) (fun hf ⟨_,_,_,eq⟩ => fires_rmw_op hf eq)
        noAtomic get ⟨_,_,_,rfl⟩).elim
  · rcases part with sl | sl | sl | _ | _ | _ | _ | _ | _ | _ | _
    all_goals try exact hw.elim

    cases sl with
    | load x y z =>
      obtain ⟨o,addr,_,_,issue,loc,_,size,_⟩ := hw
      exact .inr ⟨_,_,_,_,addr,o.spec,rfl,issue,loc,size⟩
    | copy | elem =>
      obtain ⟨_,⟨_,get⟩,_⟩ := hw
      exact (no_copy hX get).elim
    | store =>
      obtain ⟨_,_,_,_,⟨_,get⟩,_⟩ := hw
      exact (no_tensorStore hX get).elim
    | cta =>
      obtain ⟨_,_,⟨_,get⟩,_⟩ := hw
      exact (no_clc hX get).elim
    | prefetch => exact hw.elim

/-- Pending writes have the same possible sites as performed writes. A tensor
destination is fixed by the issue even before the asynchronous byte is present. -/
theorem write_intents {L m X ref a} (hX : Consistent L kernel Assumptions.all m X)
    (hw : X.Intent ref a true) :
    (∃ i pc bs, ref=.thread i ∧ X.get i=some ⟨pc,.wr a bs⟩) ∨
    ∃ i x y z addr sp, ref=.async i (.write (.load x y z)) ∧ X.TensorIssue i addr sp ∧
      TensorCopy.writeLoc sp x y z=some a.loc ∧ a.size=1 := by
  rcases ref with i|⟨i,part⟩
  · rcases hw with ⟨_,_,bad⟩|⟨bs,⟨pc,get⟩,_⟩|⟨old,new,pc,get⟩
    · cases bad
    · exact .inl ⟨_,_,_,rfl,get⟩
    · exact (no_kind_of_code hX atomicOp (fun k => ∃ dst o n, k=.rmw dst o n)
        (fun _ ⟨_,_,_,eq⟩ => by cases eq) (fun hf ⟨_,_,_,eq⟩ => fires_rmw_op hf eq)
        noAtomic get ⟨_,_,_,rfl⟩).elim
  · obtain ⟨direction,foot⟩ := hw
    rcases part with slot | slot | slot | _ | _ | _ | _ | _ | _ | _ | _
    all_goals try exact Bool.noConfusion direction

    cases slot with
    | copy | elem =>
      obtain ⟨_,⟨_,get⟩,_⟩ := foot
      exact (no_copy hX get).elim
    | store =>
      obtain ⟨_,_,⟨_,get⟩,_⟩ := foot
      exact (no_tensorStore hX get).elim
    | cta =>
      obtain ⟨_,_,⟨_,get⟩,_⟩ := foot
      exact (no_clc hX get).elim
    | prefetch => exact foot.elim
    | load x y z =>
      obtain ⟨sp,addr,he,loc,sz⟩ := foot
      exact .inr ⟨i,x,y,z,addr,sp,rfl,he,loc,sz⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
