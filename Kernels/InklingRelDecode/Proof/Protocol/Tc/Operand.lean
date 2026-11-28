-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tc.Agree
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
import Kernels.InklingRelDecode.Proof.Common.Export.BcastExit
public import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Lib.TcVec
import Lemmas.Flow.PollRendezvous

@[expose] public section

/-! # ERR-ALIGNED, `tcgen05` collectives: the lanes of a warp agree on the operands

The word the warp's broadcast delivers is the same for every lane of the warp: the shuffles of the
lanes at one ordinal take the operand of the one shuffle of lane zero at that ordinal, since no
lane of the warp has exited before it. The address of a load or store is a function of the round
and that word (`Export.tc_operand`), and the round is fixed by the counts of the earlier data
events, which the lanes of a warp at one ordinal share. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Tc
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem broadcast_source (hb : L.block=256) {x y : Nat} (w : SameWarp L x y)
    (lx : x%L.block<128) :
    x-laneOf L x+(shflSource .idx (laneOf L x) 0 31).1=x-laneOf L x ∧
    y-laneOf L y+(shflSource .idx (laneOf L y) 0 31).1=x-laneOf L x ∧
    (x-laneOf L x)%L.block<128 ∧ (x-laneOf L x)/L.block=x/L.block ∧ y%L.block<128 := by
  have src (g : Nat) : (shflSource .idx (laneOf L g) 0 31).1=0 := by
    simp [shflSource]
  obtain ⟨⟨-,-,cta⟩,warp⟩ := w
  rw [src x,src y]
  simp only [laneOf,Nat.add_zero]
  rw [hb] at lx cta warp ⊢
  refine ⟨trivial,?_,?_,?_,?_⟩ <;> omega

/-- **The lanes of a warp that make the broadcast of one ordinal receive one word.** -/
theorem bcast_agree (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {x y n P wx wy} (site : P=1261 ∨ P=2603) (w : SameWarp L x y)
    (lx : x%L.block<128) (ax : Lib.ShflAt X x P n wx) (ay : Lib.ShflAt X y P n wy) : wx=wy := by
  obtain ⟨jx,a,ok,gx,cx⟩ := ax
  obtain ⟨jy,a',ok',gy,cy⟩ := ay
  obtain ⟨sx,sy,low,cta,ly⟩ := broadcast_source hp.block w lx
  obtain ⟨-,hx⟩ := hX.shfl x jx n P .idx a 0 31 wx ok gx ⟨⟨_,_,_,_,_,_,_,gx⟩,cx⟩
  obtain ⟨-,hy⟩ := hX.shfl y jy n P .idx a' 0 31 wy ok' gy ⟨⟨_,_,_,_,_,_,_,gy⟩,cy⟩
  rw [sx] at hx
  rw [sy] at hy
  rcases hx with ⟨j1,_,_,_,_,_,k1,g1⟩|ex
  swap
  · exact (Export.bcast_not_exited hp hX hf site gx cx low cta ex).elim
  rcases hy with ⟨j2,_,_,_,_,_,k2,g2⟩|ey
  swap
  · exact (Export.bcast_not_exited hp hX hf site gx cx low cta ey).elim
  obtain rfl := ShflK.eq_of_ord k1 k2
  rw [g1] at g2
  simp only [Option.some.injEq,Event.mk.injEq,Kind.shfl.injEq] at g2
  obtain ⟨-,-,same,-⟩ := g2
  exact same

private theorem round_eq {pc i R e i' R' e' : Nat} (a : pc ∈ Lib.addrPcs)
    (h : Lib.tcVec pc i R e = Lib.tcVec pc i' R' e') : i = i' := by
  simp only [Lib.addrPcs,List.mem_cons,List.not_mem_nil,or_false] at a
  rcases a with rfl|rfl|rfl|rfl|rfl <;> simp [Lib.tcVec] at h <;> omega

private theorem static_off {cta pc i i' w w'} (h : pc ∉ Lib.addrPcs) :
    Lib.opStatic L cta pc i w = Lib.opStatic L cta pc i' w' := by
  simp only [Lib.addrPcs,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  obtain ⟨h1,h2,h3,h4,h5⟩ := h
  simp [Lib.opStatic,h1,h2,h3,h4,h5]

/-- **Two lanes of a warp at their `k`-th collective `tcgen05` event show the same static event.**
Their positions agree (`tc_same_pc`), so do the counts of their earlier data events, and with them
the round and, by the shuffle of the round, the word the warp's broadcast delivered. -/
theorem tc_static_agree (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (base : Iface.BaseRead L X) {x y jx jy px py kx ky}
    (w : SameWarp L x y) (gx : X.get (x,jx) = some ⟨px,.tc kx⟩)
    (gy : X.get (y,jy) = some ⟨py,.tc ky⟩) (tcx : isTcColl ⟨px,.tc kx⟩ = true)
    (tcy : isTcColl ⟨py,.tc ky⟩ = true)
    (ord : ((X.tr x).take jx).countP isTcColl = ((X.tr y).take jy).countP isTcColl) :
    tcStatic kx = tcStatic ky := by
  obtain rfl := tc_same_pc hp hX hf safe w gx gy tcx tcy ord
  obtain ⟨ix,wx,⟨Rx,ex,vx⟩,addrx,sx⟩ := Export.tc_operand hp hX hf base gx tcx
  obtain ⟨iy,wy,⟨Ry,ey,vy⟩,addry,sy⟩ := Export.tc_operand hp hX hf base gy tcy
  have cta : x/L.block=y/L.block := w.1.2.2
  rw [sx,sy,cta]
  by_cases a : px ∈ Lib.addrPcs
  · have nubx := Frame.noUbBefore_of_get hX gx
    have nuby := Frame.noUbBefore_of_get hX gy
    have ih : ∀ n < ((X.tr x).take jx).countP isTcColl, ∀ {ix iy ex ey}, X.get (x,ix) = some ex →
        X.get (y,iy) = some ey → isTcColl ex = true → isTcColl ey = true →
        ((X.tr x).take ix).countP isTcColl = n → ((X.tr y).take iy).countP isTcColl = n →
        ex.pc = ey.pc := by
      intro n _ ix iy ex ey a b c d e f
      obtain ⟨pa,ka⟩ := ex
      obtain ⟨pb,kb⟩ := ey
      exact tc_same_pc hp hX hf safe w a b c d (e.trans f.symm)
    have pcle : ∀ P ∈ Lib.dataPcs, ((X.tr x).take jx).countP (fun e => e.pc == P) =
        ((X.tr y).take jy).countP (fun e => e.pc == P) := by
      intro P hP
      rw [pc_count_tc hX nubx hP,pc_count_tc hX nuby hP]
      exact tc_count_agree (q := fun e : Event => e.pc == P && isTcColl e)
        (fun e h => (Bool.and_eq_true_iff.mp h).2) rfl ord.symm
        (ord_same le_rfl ord.le ih (fun _ _ tx ty h => by simp [h,tx,ty]))
    have vec : Lib.tcVec px ix Rx ex = Lib.tcVec px iy Ry ey := by
      rw [← vx,← vy]
      exact List.map_congr_left pcle
    obtain rfl := round_eq a vec
    have lx := Export.tc_data_lane hp hX hf gx tcx
    have ay := addry a
    rw [← cta] at ay
    have site : Lib.bcastPc px=1261 ∨ Lib.bcastPc px=2603 := by
      unfold Lib.bcastPc
      split_ifs <;> simp
    rw [bcast_agree hp hX hf site w lx (addrx a) ay]
  · exact static_off a

/-- **No two lanes of a warp diverge at a collective `tcgen05` event.** -/
theorem not_divergent (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (base : Iface.BaseRead L X) :
    ¬ AlignedClass.tc.Divergent L kernel X := by
  rintro ⟨⟨x,jx⟩,⟨y,jy⟩,pe,pf,ke,kf,w,he,hf',hme,hmf,hord,-,hne⟩
  obtain ⟨a,rfl⟩ := isTcColl_kind hme
  obtain ⟨b,rfl⟩ := isTcColl_kind hmf
  have tcx : isTcColl ⟨pe,.tc a⟩ = true := hme
  have tcy : isTcColl ⟨pf,.tc b⟩ = true := hmf
  have ord : ((X.tr x).take jx).countP isTcColl = ((X.tr y).take jy).countP isTcColl := hord
  have same := tc_same_pc hp hX hf safe w he hf' tcx tcy ord
  have static := tc_static_agree hp hX hf safe base w he hf' tcx tcy ord
  rcases hne with h|h
  · exact h same
  · exact h (by simp only [AlignedClass.operands,static])

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Tc
