-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Lemmas.Kernel.Source.WarpColl
import Lemmas.Step.WarpShfl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

public theorem bfly_source (l b : Nat) (hl : l<32) (hb : b<32) :
    shflSource .bfly l b 31 = (l ^^^ b, true) := by
  have : l ^^^ b < 32 := Nat.xor_lt_two_pow (n:=5) hl hb
  simp [shflSource, Nat.mod_eq_of_lt hb]
  omega

public theorem count_succ {X : Execution} {g i : Nat} {e : Event} (get : X.get (g,i)=some e) :
    ((X.tr g).take (i+1)).countP Execution.isShfl=
      ((X.tr g).take i).countP Execution.isShfl+(if Execution.isShfl e then 1 else 0) := by
  have : (X.tr g)[i]?=some e := get
  rw [List.take_add_one,this,List.countP_append]
  simp

/-- A data lane at a butterfly or rescale-decision shuffle has a partner event: the source lane's
shuffle of the same ordinal, whose operand is what this lane received. The source lane never
exited first. -/
theorem decision_partner {Q L m X g k pc mode a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨pc,.shfl mode a b c recv ok⟩)
    (late : pc=1838 ∨ pc=2242 ∨ pc=2244 ∨ pc=2246 ∨ pc=2248 ∨ pc=2253 ∨ pc=2255 ∨ pc=2234)
    (lane : g%L.block<128) :
    ∃ j pc' b' c' r' o', X.get (g-laneOf L g+(shflSource mode (laneOf L g) b c).1,j)=
        some ⟨pc',.shfl mode recv b' c' r' o'⟩ ∧
      ((X.tr (g-laneOf L g+(shflSource mode (laneOf L g) b c).1)).take j).countP
        Execution.isShfl=((X.tr g).take k).countP Execution.isShfl := by
  have hb : L.block%32=0 := by rw [hp.block]
  have src := Step.shflSource_lt mode (show laneOf L g<32 from Nat.mod_lt _ (by decide)) b c
  obtain ⟨_,hw,cta,_,_⟩ := Frame.lane_facts hb (Frame.lt_of_get hX get) rfl src
  obtain ⟨_,hit|gone⟩ := hX.shfl _ _ ((X.tr g).take k |>.countP Execution.isShfl) _ _ _ _ _ _ _
    get ⟨⟨_,_,_,_,_,_,_,get⟩,rfl⟩
  · obtain ⟨j,pc',b',c',r',o',rank,got⟩ := hit
    exact ⟨j,pc',b',c',r',o',got,rank.2⟩
  · exact (decision_not_exited hp hX hf get late rfl (by omega) cta gone).elim

/-- **The partner of a butterfly shuffle at a site of the late code**: the lane `b` away has the
shuffle of the same pc at the same ordinal, which sent what this lane received. -/
public theorem late_partner {Q L m X g k pc a b recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨pc,.shfl .bfly a b 31 recv ok⟩)
    (late : pc=1838 ∨ pc=2242 ∨ pc=2244 ∨ pc=2246 ∨ pc=2248 ∨ pc=2253 ∨ pc=2255 ∨ pc=2234)
    (hb : b<32) (lane : g%L.block<128) :
    ∃ j b' c' r' o', X.get (g-g%32+(g%32 ^^^ b),j)=some ⟨pc,.shfl .bfly recv b' c' r' o'⟩ ∧
      (g-g%32+(g%32 ^^^ b))%L.block<128 ∧ (g-g%32+(g%32 ^^^ b))/L.block=g/L.block ∧
      ((X.tr (g-g%32+(g%32 ^^^ b))).take j).countP Execution.isShfl=
        ((X.tr g).take k).countP Execution.isShfl := by
  have hk : L.block=256 := hp.block
  obtain ⟨j,pc',b',c',r',o',got,count⟩ := decision_partner hp hX hf get late lane
  have lane32 : laneOf L g=g%32 := by unfold laneOf; rw [hk]; omega
  rw [lane32] at got count
  rw [bfly_source _ _ (by omega) hb] at got count
  dsimp only at got count
  have x : g%32 ^^^ b<32 := Nat.xor_lt_two_pow (n:=5) (by omega) hb
  have low : (g-g%32+(g%32 ^^^ b))%L.block<128 := by rw [hk] at lane ⊢; omega
  have cta : (g-g%32+(g%32 ^^^ b))/L.block=g/L.block := by rw [hk]; omega
  obtain rfl := partner_pc_late hp hX hf get late low cta got rfl count
  exact ⟨j,b',c',r',o',got,low,cta,count⟩
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
