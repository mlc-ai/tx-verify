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

/-- **Every read intent, pending or performed, is a thread load, an MMA operand read or a
byte of a tensor load's source.** The kernel has no read-modify-write, copy, tensor store,
tensor prefetch or bulk prefetch. -/
theorem read_intents {L m X ref a} (hX : Consistent L kernel Assumptions.all m X)
    (hr : X.Intent ref a false) :
    (∃ i pc bs, ref=.thread i ∧ X.get i=some ⟨pc,.rd a bs⟩) ∨
    (∃ i isB j, ref=.async i (.mmaRead isB j) ∧ X.MmaFootprint i isB j a.loc) ∨
    ∃ i x y z addr sp, ref=.async i (.read (.load x y z)) ∧ X.TensorIssue i addr sp ∧
      TensorCopy.readLoc sp x y z=some a.loc ∧ a.size=1 := by
  rcases ref with i|⟨i,part⟩
  · rcases hr with ⟨bs,⟨pc,get⟩,_⟩|⟨_,_,bad⟩|⟨old,new,pc,get⟩
    · exact .inl ⟨_,_,_,rfl,get⟩
    · cases bad
    · exact (no_kind_of_code hX atomicOp (fun k => ∃ dst o n, k=.rmw dst o n)
        (fun _ ⟨_,_,_,eq⟩ => by cases eq) (fun hf ⟨_,_,_,eq⟩ => fires_rmw_op hf eq)
        noAtomic get ⟨_,_,_,rfl⟩).elim
  · obtain ⟨direction,foot⟩ := hr
    rcases part with slot | slot | slot | _ | _ | _ | _ | _ | ⟨isB,j⟩ | _ | _
    · cases slot with
      | load x y z =>
        obtain ⟨sp,addr,he,loc,sz⟩ := foot
        exact .inr (.inr ⟨i,x,y,z,addr,sp,rfl,he,loc,sz⟩)
      | copy =>
        rcases foot with ⟨_,⟨_,get⟩,_⟩|⟨_,get⟩
        · exact (no_copy hX get).elim
        · exact (no_bulkPrefetch hX get).elim
      | elem => exact foot.elim
      | store =>
        obtain ⟨_,_,⟨_,get⟩,_⟩ := foot
        exact (no_tensorStore hX get).elim
      | cta => exact foot.elim
      | prefetch =>
        obtain ⟨_,_,⟨_,get⟩,_⟩ := foot
        exact (no_tensorPrefetch hX get).elim
    · exact Bool.noConfusion direction
    · cases slot with
      | store =>
        obtain ⟨_,_,⟨_,get⟩,_⟩ := foot
        exact (no_tensorStore hX get).elim
      | elem =>
        obtain ⟨_,_,⟨_,get⟩,_⟩ := foot
        exact (no_copy hX get).elim
      | _ => exact foot.elim
    all_goals try exact foot.elim
    exact .inr (.inl ⟨i,isB,j,rfl,foot.2⟩)

end PTX.Kernels.InklingRelDecode.Proof.Lib
