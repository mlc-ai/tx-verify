-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Lib.BarOne

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

private def signature (p : Nat) : Nat × Option Nat :=
  if p ∈ BarRow.fullZeroSites then (0,none)
  else if p ∈ BarRow.halfZeroSites then (0,some 128) else (1,none)

private theorem bar_signature {Q L m X i pc id cnt} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.IsBarrier i id cnt pc) :
    (id,cnt)=signature pc ∧ (kernel.alignedAt pc=false → (id,cnt)=(1,none)) := by
  have single : Lib.barOneSites.all (fun p => decide (signature p=(1,none)))=true := by decide
  have full : BarRow.fullZeroSites.all (fun p =>
      decide (signature p=(0,none)) && kernel.alignedAt p)=true := by decide +kernel
  have half : BarRow.halfZeroSites.all (fun p =>
      decide (signature p=(0,some 128)) && kernel.alignedAt p)=true := by decide +kernel
  rcases (Lib.recorded_bar hX hp.block he).2 with ⟨rfl,rfl,p⟩|⟨rfl,rfl,p⟩|⟨rfl,rfl,p⟩
  · exact ⟨(of_decide_eq_true (List.all_eq_true.mp single pc p)).symm,fun _ => rfl⟩
  · obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp full pc p)
    exact ⟨(of_decide_eq_true a).symm,fun no => by rw [no] at b; cases b⟩
  · obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp half pc p)
    rw [hp.block]
    exact ⟨(of_decide_eq_true a).symm,fun no => by rw [no] at b; cases b⟩

/-- Only barrier 1 can be unaligned. Different recorded operands therefore
imply distinct instruction positions with an aligned participant. -/
public theorem Safe.noBarMismatch {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (aligned : ¬ AlignedMismatch L kernel X) :
    ¬ BarMismatch L X := by
  rintro (⟨g,h,i,j,id,id',cnt,cnt',p,q,warp,left,right,ord,bad⟩|arr)
  · obtain ⟨a,ua⟩ := bar_signature hp hX left
    obtain ⟨b,ub⟩ := bar_signature hp hX right
    have ne : (id,cnt)≠(id',cnt') := by
      intro eq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      simp at bad
    apply aligned
    refine ⟨.bar,.inl ⟨(g,i),(h,j),p,q,_,_,warp,left,right,rfl,rfl,ord,?_,.inl ?_⟩⟩
    · change (kernel.alignedAt p || kernel.alignedAt q)=true
      cases ep : kernel.alignedAt p <;> cases eq : kernel.alignedAt q <;> try rfl
      exact (ne ((ua ep).trans (ub eq).symm)).elim
    · rintro rfl
      exact ne (a.trans b.symm)
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,he,_⟩ := arr
    cases (Lib.recorded_bar hX hp.block he).1

end PTX.Kernels.InklingRelDecode.Proof.Top
