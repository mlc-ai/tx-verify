-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.Regs
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Tmem.AccessCp
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Flow.NotTcShift
import Lemmas.Flow.TcStLen
import Lemmas.Tcgen05.TcDataCell

/-! # The Tensor Memory accesses of the kernel

Every access is a launched thread's MMA, load or store of a cell of its own CTA below column 512;
the kernel issues no copy and no shift (`Tmem.AccessCp.AccessInfoCp`). The load and store cells
are the `16x32bx2` cells of the buffers of `Tmem.ld_static` and `Tmem.st_static`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem kernel_noShift : kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by
  decide +kernel

/-- **The kernel issues no `tcgen05.shift`.** -/
public theorem no_shift (hX : Consistent L kernel Assumptions.all m X) :
    ∀ i s, ¬ X.ShiftIssue i s := fun _ s ⟨_,he⟩ => no_shift_of_code hX kernel_noShift he s rfl

/-- The cell of a `16x32bx2` access of at most 64 registers at a buffer base column at most 256. -/
private theorem cell_cols {L : Launch} {g a j off : Nat} (hj : j < 64) (hoff : off = 64 ∨ off = 32)
    (ha : a % 2^16 ≤ 256) :
    (tcDataCell L g (.s16x32bx2 off) a j).column < 512 := by
  unfold tcDataCell TcShape.base TcShape.columnIn
  dsimp only
  split <;> omega

/-- **Every Tensor Memory access of the kernel is a thread's MMA, load or store, of a cell of its
own CTA below column 512, and there is no shift.** -/
public theorem access_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) : Tmem.AccessCp.AccessInfoCp L X := by
  have noShift : ∀ i s, ¬ X.ShiftIssue i s := fun i s ⟨pc,he⟩ =>
    no_shift_of_code hX kernel_noShift he s rfl
  refine ⟨fun {e cell} ha => ?_, noShift⟩
  obtain ⟨g,k⟩ := e
  have low : ∀ {ev}, X.get (g,k) = some ev → g < L.threads := fun he => Frame.lt_of_get hX he
  rcases ha with hm | ⟨j,a,vals,sh,hld,hj,rfl⟩ | ⟨a,vals,sh,j,hst,hj,rfl⟩ | hc | ⟨s,hs,-⟩ | ⟨s,hs,-⟩
  · have issue : ∃ d s acc mask, X.MmaIssue (g,k) d s acc mask := by
      rcases hm with ⟨d,s,acc,mask,-,-,hi,-⟩ | ⟨d,s,mask,-,-,hi,-⟩ | ⟨d,s,acc,mask,-,-,hi,-⟩
      · exact ⟨d,s,acc,mask,hi⟩
      · exact ⟨d,s,true,mask,hi⟩
      · exact ⟨d,s,acc,mask,hi⟩
    obtain ⟨d,s,acc,mask,pc,he⟩ := issue
    obtain ⟨cta,col⟩ := mma_cells hp hX hf base hm
    exact ⟨low he,cta,col,.inl ⟨d,s,acc,mask,pc,he⟩⟩
  · obtain ⟨pc,he⟩ := hld
    obtain ⟨i,k',hk,hpc,rfl,hlen⟩ := ld_static hp hX hf base he
    have col := cell_cols (L := L) (g := g) (a := a) (j := j) (off := 64) (by omega) (.inl rfl)
      (by rcases hpc with ⟨-,rfl⟩ | ⟨-,rfl⟩ <;> omega)
    exact ⟨low he,rfl,col,.inr (.inr (.inl ⟨a,vals,_,pc,he⟩))⟩
  · obtain ⟨pc,he⟩ := hst
    obtain ⟨i,k',hk,hpc⟩ := st_static hp hX hf base he
    rcases hpc with ⟨hpc,ha,hsh,hlen⟩ | ⟨hpc,ha,hsh,hlen⟩
    · subst hsh
      have col := cell_cols (L := L) (g := g) (a := a) (j := j) (off := 64) (by omega)
        (.inl rfl) (by omega)
      exact ⟨low he,rfl,col,.inr (.inr (.inr ⟨a,vals,_,pc,he⟩))⟩
    · subst hsh
      have col := cell_cols (L := L) (g := g) (a := a) (j := j) (off := 32) (by omega)
        (.inr rfl) (by omega)
      exact ⟨low he,rfl,col,.inr (.inr (.inr ⟨a,vals,_,pc,he⟩))⟩
  · obtain ⟨c,-,-,-,hi,-⟩ := hc
    exact (Lib.no_cp hX _ c hi).elim
  · exact (noShift _ s hs).elim
  · exact (noShift _ s hs).elim

end PTX.Kernels.InklingRelDecode.Proof.Tmem
