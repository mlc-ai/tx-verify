-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.RescaleWord
import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.RescaleSkip
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner
import Kernels.InklingRelDecode.Proof.Softmax.RescaleChoice

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

private theorem xor4 (m j s : Nat) (hj : j<4) (hs : s<4) :
    (4*m+j) ^^^ s = 4*m + (j ^^^ s) := by
  have h1 : ((4*m+j) ^^^ s) % 4 = (j ^^^ s) := by
    have := @Nat.xor_mod_two_pow (4*m+j) s 2
    rw [show 2^2=4 from rfl] at this
    rw [this, Nat.mod_eq_of_lt hs]
    have : (4*m+j)%4 = j := by omega
    rw [this]
  have h2 : ((4*m+j) ^^^ s) / 4 = m := by
    have := @Nat.xor_div_two_pow (4*m+j) s 2
    rw [show 2^2=4 from rfl] at this
    rw [this]
    have : s/4=0 := by omega
    rw [this]; simp; omega
  omega

private theorem lane_xor {L : Launch} {g : Nat} (hb : L.block=256) {s : Nat} (hs : s<4) :
    g-laneOf L g+(laneOf L g ^^^ s)=g-g%4+(g%4 ^^^ s) := by
  have eq : laneOf L g=g%256%32 := by unfold laneOf; rw [hb]
  rw [eq]
  have split : g%256%32=4*(g%256%32/4)+g%256%32%4 := by omega
  rw [split,xor4 _ _ _ (by omega) hs]
  have : g%256%32%4=g%4 := by omega
  rw [this]
  omega

private theorem lane_of {L : Launch} {g z : Nat} (hb : L.block=256) (hz : z<32) :
    laneOf L (g-laneOf L g+z)=z := by
  have eq : laneOf L g=g%256%32 := by unfold laneOf; rw [hb]
  unfold laneOf
  rw [hb]
  omega

private theorem complete_quad : ∀ j<4, ∀ i<4, i≠j → i≠(j ^^^ 1) → i≠(j ^^^ 2) →
    i=((j ^^^ 1) ^^^ 2) := by decide

/-- The partner events of one decision shuffle: the lane `y` of the same warp with the
quad offset `s` holds an event of the same shuffle ordinal. -/
private theorem partner_quad {Q L m X g k a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) {pc : Nat}
    (get : X.get (g,k)=some ⟨pc,.shfl .bfly a b c recv ok⟩) (decision : pc=2253 ∨ pc=2255)
    (lane : g%L.block<128) {s : Nat} (hs : s=1 ∨ s=2) (bs : b=s) (cs : c=31) :
    ∃ j b' c' r' o', X.get (g-g%4+(g%4 ^^^ s),j)=some ⟨pc,.shfl .bfly recv b' c' r' o'⟩ ∧
      ((X.tr (g-g%4+(g%4 ^^^ s))).take j).countP Execution.isShfl=
        ((X.tr g).take k).countP Execution.isShfl := by
  subst cs
  rw [bs] at get
  have hb : L.block=256 := hp.block
  rw [hb] at lane
  obtain ⟨j,pc',b',c',r',o',got,count⟩ :=
    decision_partner hp hX hf get (by omega) (by rw [hb]; exact lane)
  have src := bfly_source (laneOf L g) s (by unfold laneOf; rw [hb]; omega) (by omega)
  rw [src] at got count
  dsimp only at got count
  rw [lane_xor hb (by omega)] at got count
  have low : (g-g%4+(g%4 ^^^ s))%L.block<128 := by
    have : g%4 ^^^ s<4 := Nat.xor_lt_two_pow (n:=2) (by omega) (by omega)
    rw [hb]; omega
  have cta : (g-g%4+(g%4 ^^^ s))/L.block=g/L.block := by
    have : g%4 ^^^ s<4 := Nat.xor_lt_two_pow (n:=2) (by omega) (by omega)
    rw [hb]; omega
  obtain rfl := partner_pc hp hX hf get decision low cta got rfl count
  exact ⟨j,b',c',r',o',got,count⟩

private theorem quad_distinct : ∀ j<4, j ^^^ 1 ≠ j ∧ j ^^^ 2 ≠ j ∧ j ^^^ 2 ≠ j ^^^ 1 ∧
    (j ^^^ 1) ^^^ 2 ≠ j ∧ (j ^^^ 1) ^^^ 2 ≠ j ^^^ 1 ∧ (j ^^^ 1) ^^^ 2 ≠ j ^^^ 2 := by decide

private theorem lane_one {L : Launch} {g : Nat} (hb : L.block=256) (lane : g%L.block<128) :
    (g-g%4+(g%4 ^^^ 1))%L.block<128 ∧
    (g-g%4+(g%4 ^^^ 1))-(g-g%4+(g%4 ^^^ 1))%4+((g-g%4+(g%4 ^^^ 1))%4 ^^^ 2)=
      g-g%4+((g%4 ^^^ 1) ^^^ 2) ∧ (g-g%4+(g%4 ^^^ 1))%4=g%4 ^^^ 1 := by
  have small : g%4 ^^^ 1<4 := Nat.xor_lt_two_pow (n:=2) (by omega) (by omega)
  have mod : (g-g%4+(g%4 ^^^ 1))%4=g%4 ^^^ 1 := by omega
  rw [hb] at lane ⊢
  refine ⟨by omega,?_,mod⟩
  rw [mod]
  omega

/-- The four words of a quad: the decision at the second shuffle is the compare of the minima
of the four scratch words read by the lanes of the quad at the same shuffle ordinal. -/
public theorem decision_four {Q L m X g k a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨2255,.shfl .bfly a b c recv ok⟩) (lane : g%L.block<128) :
    ∃ bsOf : Nat → List (Option Byte),
      (∀ i<4, ∃ j ac, X.get (g-g%4+i,j)=some ⟨2252,.rd ac (bsOf i)⟩ ∧
        ((X.tr (g-g%4+i)).take j).countP Execution.isShfl=
          ((X.tr g).take (k-2)).countP Execution.isShfl) ∧
      Lib.rescaleSkip L a recv=Lib.rescaleSkip L
        (Lib.minWord (Lib.loadWord (bsOf 0)) (Lib.loadWord (bsOf 2)))
        (Lib.minWord (Lib.loadWord (bsOf 1)) (Lib.loadWord (bsOf 3))) := by
  have hb : L.block=256 := hp.block
  obtain ⟨j,ac,bs,p,ok1,rfl,rd,sh1,ha,hb1,hc1⟩ := rescale_data hp hX get
  subst hb1 hc1
  obtain ⟨j1,b1,c1,r1,o1,got1,cnt1⟩ :=
    partner_quad hp hX hf get (Or.inr rfl) lane (s:=1) (Or.inl rfl) rfl rfl
  obtain ⟨jr,ac1,bs1,p1,ok2,rfl,rd1,sh1',ha1,-,-⟩ := rescale_data hp hX got1
  obtain ⟨j2,b2,c2,r2,o2,got2,cnt2⟩ :=
    partner_quad hp hX hf sh1 (Or.inl rfl) lane (s:=2) (Or.inr rfl) rfl rfl
  obtain ⟨jr2,ac2,bs2,rfl,rd2,hp2,-,-⟩ := word_data hp hX got2
  obtain ⟨low1,lane3,mod1⟩ := lane_one hb lane
  obtain ⟨j3,b3,c3,r3,o3,got3,cnt3⟩ :=
    partner_quad hp hX hf sh1' (Or.inl rfl) (by rw [hb] at low1 ⊢; omega) (s:=2) (Or.inr rfl)
      rfl rfl
  rw [lane3] at got3 cnt3
  obtain ⟨jr3,ac3,bs3,rfl,rd3,hp3,-,-⟩ := word_data hp hX got3
  have gj : ((X.tr g).take (j+1)).countP Execution.isShfl=
      ((X.tr g).take j).countP Execution.isShfl := by
    rw [count_succ rd]; simp [Execution.isShfl]
  have gj2 : ((X.tr g).take (j+2)).countP Execution.isShfl=
      ((X.tr g).take j).countP Execution.isShfl+1 := by
    have := count_succ sh1
    rw [gj] at this
    simpa [Execution.isShfl] using this
  have y1a : ((X.tr (g-g%4+(g%4 ^^^ 1))).take (jr+1)).countP Execution.isShfl=
      ((X.tr (g-g%4+(g%4 ^^^ 1))).take jr).countP Execution.isShfl := by
    rw [count_succ rd1]; simp [Execution.isShfl]
  have y1b : ((X.tr (g-g%4+(g%4 ^^^ 1))).take (jr+2)).countP Execution.isShfl=
      ((X.tr (g-g%4+(g%4 ^^^ 1))).take jr).countP Execution.isShfl+1 := by
    have := count_succ sh1'
    rw [y1a] at this
    simpa [Execution.isShfl] using this
  have y2a : ((X.tr (g-g%4+(g%4 ^^^ 2))).take (jr2+1)).countP Execution.isShfl=
      ((X.tr (g-g%4+(g%4 ^^^ 2))).take jr2).countP Execution.isShfl := by
    rw [count_succ rd2]; simp [Execution.isShfl]
  have y3a : ((X.tr (g-g%4+((g%4 ^^^ 1) ^^^ 2))).take (jr3+1)).countP Execution.isShfl=
      ((X.tr (g-g%4+((g%4 ^^^ 1) ^^^ 2))).take jr3).countP Execution.isShfl := by
    rw [count_succ rd3]; simp [Execution.isShfl]
  have c1 : ((X.tr (g-g%4+(g%4 ^^^ 1))).take jr).countP Execution.isShfl=
      ((X.tr g).take j).countP Execution.isShfl := by omega
  have c2 : ((X.tr (g-g%4+(g%4 ^^^ 2))).take jr2).countP Execution.isShfl=
      ((X.tr g).take j).countP Execution.isShfl := by omega
  have c3 : ((X.tr (g-g%4+((g%4 ^^^ 1) ^^^ 2))).take jr3).countP Execution.isShfl=
      ((X.tr g).take j).countP Execution.isShfl := by omega
  have small : g%4<4 := by omega
  obtain ⟨d1,d2,d3,d4,d5,d6⟩ := quad_distinct _ small
  set f : Nat → List (Option Byte) := fun i => if i=g%4 then bs else if i=(g%4 ^^^ 1) then bs1 else
    if i=(g%4 ^^^ 2) then bs2 else bs3 with hf
  have e0 : f (g%4)=bs := by simp [hf]
  have e1 : f (g%4 ^^^ 1)=bs1 := by simp [hf,d1]
  have e2 : f (g%4 ^^^ 2)=bs2 := by simp [hf,d2,d3]
  have e3 : f ((g%4 ^^^ 1) ^^^ 2)=bs3 := by simp [hf,d4,d5,d6]
  refine ⟨f,?_,?_⟩
  · intro i hi
    simp only [Nat.add_sub_cancel]
    by_cases h0 : i=g%4
    · have lane0 : g-g%4+i=g := by omega
      rw [lane0,h0,e0]
      exact ⟨j,ac,rd,rfl⟩
    by_cases h1 : i=(g%4 ^^^ 1)
    · rw [h1,e1]
      exact ⟨jr,ac1,rd1,c1⟩
    by_cases h2 : i=(g%4 ^^^ 2)
    · rw [h2,e2]
      exact ⟨jr2,ac2,rd2,c2⟩
    have h3 := complete_quad _ small i hi h0 h1 h2
    rw [h3,e3]
    exact ⟨jr3,ac3,rd3,c3⟩
  · have key := Control.rescale_four (L:=L) (g:=g) (g':=0) (fun i => Lib.loadWord (f i)) small
    simp only [e0,e1,e2,e3] at key
    rw [ha,hp2,ha1,hp3,←Control.skip_free L g,←Control.skip_free L 0]
    exact key

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
