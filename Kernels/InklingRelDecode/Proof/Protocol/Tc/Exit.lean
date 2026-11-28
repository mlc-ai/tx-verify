-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tc.Agree
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Lib.TcInject

@[expose] public section

/-! # ERR-ALIGNED, `tcgen05` collectives: no lane exits early

A lane `f` that has exited with at most `k` collective events, while a lane `e` of its warp makes
its `k`-th, has made the same collective events as `e` below its own count (`tc_same_pc`). So `e`'s
earlier events cover `f`'s: its counts of the data positions and of the paired Tensor Memory
operations are at least `f`'s. But `f`'s exit has made every event of the loop and the epilogue, and
warp zero's three paired operations, which no event of `e` that is not past them can cover
(`Lib.tcExit_clash`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Tc
open PTX PTX.Flow PTX.Tmem.Pair

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem forall₂_map_le {l : List Nat} {a b : Nat → Nat} (h : ∀ P ∈ l, a P ≤ b P) :
    List.Forall₂ (· ≤ ·) (l.map a) (l.map b) := by
  induction l with
  | nil => exact .nil
  | cons P rest ih =>
    exact .cons (h P (.head _)) (ih fun Q hQ => h Q (.tail _ hQ))

/-- **No participant of a warp-collective `tcgen05` exits early.** -/
theorem not_exited (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) : ¬ AlignedClass.tc.Exited L kernel X := by
  rintro ⟨⟨x,jx⟩,⟨y,jf⟩,⟨pe,ke⟩,w,gx,hm,-,⟨pcx,gf⟩,hle⟩
  change SameWarp L x y at w
  simp only [AlignedClass.exitMember,AlignedClass.member] at hm hle
  have tcx : isTcColl ⟨pe,ke⟩ = true := hm
  have cta : x/L.block = y/L.block := w.1.2.2
  have lanes : x%L.block/32 = y%L.block/32 := w.2
  have lx : x%L.block < 128 := Export.tc_data_lane hp hX hf gx tcx
  have ly : y%L.block < 128 := by omega
  have ordle : ((X.tr y).take jf).countP isTcColl ≤ ((X.tr x).take jx).countP isTcColl :=
    ((List.take_sublist _ _).countP_le).trans hle
  have nubf := Frame.noUbBefore_of_get hX gf
  have nubx := Frame.noUbBefore_of_get hX gx
  have wy : SameWarp L y x := ⟨⟨w.1.2.1,w.1.1,w.1.2.2.symm⟩,w.2.symm⟩
  have ih : ∀ n < ((X.tr y).take jf).countP isTcColl, ∀ {ix iy ex ey}, X.get (y,ix) = some ex →
      X.get (x,iy) = some ey → isTcColl ex = true → isTcColl ey = true →
      ((X.tr y).take ix).countP isTcColl = n → ((X.tr x).take iy).countP isTcColl = n →
      ex.pc = ey.pc := by
    intro n _ ix iy ex ey a b c d e f
    obtain ⟨pa,ka⟩ := ex
    obtain ⟨pb,kb⟩ := ey
    exact tc_same_pc hp hX hf safe wy a b c d (e.trans f.symm)
  have pcle : ∀ P ∈ Lib.dataPcs, ((X.tr y).take jf).countP (fun e => e.pc == P) ≤
      ((X.tr x).take jx).countP (fun e => e.pc == P) := by
    intro P hP
    rw [pc_count_tc hX nubf hP,pc_count_tc hX nubx hP]
    exact countP_le_of_ordinal (fun e h => by simpa using (Bool.and_eq_true_iff.mp h).2) ordle
      (ord_same le_rfl ordle ih (fun _ _ tx ty h => by simp [h,tx,ty]))
  have tmle : tmemOps ((X.tr y).take jf) ≤ tmemOps ((X.tr x).take jx) :=
    countP_le_of_ordinal (q := isTmemOp) (fun _ h => tmem_tc h) ordle
      (ord_same le_rfl ordle ih (fun {ix iy ex ey} a b tx ty h => by
        rw [tmem_pc hX a tx,tmem_pc hX b ty,h]))
  obtain ⟨Rf,ef,vf,hef,tmf⟩ := Export.exit_counts hp hX hf gf ly
  obtain ⟨i,R,e',vx,cx,mx,l1,l2,l3,l4,l5,l6,bx⟩ := Export.tc_counts hp hX hf gx tcx
  obtain ⟨winx,a11x,a15x,othx⟩ := Export.tc_tmem hp hX hf gx tcx
  rw [← cta] at vf hef
  have hle2 : List.Forall₂ (· ≤ ·) (Lib.tcVec 2851 (Lib.blocksOf Q L (x/L.block)) Rf ef)
      (Lib.tcVec pe i R e') := by
    rw [← vf,← vx]
    exact forall₂_map_le pcle
  have hx : Lib.TcFacts pe i R e' (Lib.blocksOf Q L (x/L.block)) (tmemOps ((X.tr x).take jx))
      (decide (x%L.block/32 = 0)) :=
    ⟨mx,l1,l2,l3,l4,l5,l6,fun h => by simpa using winx h,a11x,a15x,fun h1 h2 => by
      simpa using othx h1 h2⟩
  exact Lib.tcExit_clash hx hle2 hef (by simpa [lanes] using tmf) tmle

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Tc
