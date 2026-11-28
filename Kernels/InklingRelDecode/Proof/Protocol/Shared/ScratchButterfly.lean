-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Softmax.Export.Butterfly
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchEqual
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner
import Kernels.InklingRelDecode.Proof.Softmax.Export.PhysicalBar
import Kernels.InklingRelDecode.Proof.Softmax.Export.ButterflyRound

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Softmax.Export

/-- The operands of stage `k` of the minimum butterfly agree between the lanes of one warp that
agree modulo `16 >> k`, at one shuffle ordinal. -/
def StageAgree (L : Launch) (X : Execution) (k : Nat) : Prop :=
  ∀ {g j a r g' j' a' r'}, Stage X k g j a r → Stage X k g' j' a' r' → g%L.block<128 →
    g-g%32=g'-g'%32 → g%32%(16>>>k)=g'%32%(16>>>k) →
    ((X.tr g).take j).countP Execution.isShfl=((X.tr g').take j').countP Execution.isShfl → a=a'

private theorem lane_split : ∀ k<4, ∀ l<32, ∀ l'<32, l%(16>>>(k+1))=l'%(16>>>(k+1)) →
    l%(16>>>k)=l'%(16>>>k) ∨ l%(16>>>k)=(l' ^^^ 8>>>k)%(16>>>k) := by decide +kernel

private theorem lane_flip : ∀ k<4, ∀ l<32, ∀ l'<32, l%(16>>>k)=l'%(16>>>k) →
    (l ^^^ 8>>>k)%(16>>>k)=(l' ^^^ 8>>>k)%(16>>>k) := by decide +kernel

private theorem lane_back : ∀ k<4, ∀ l<32, ∀ l'<32, l%(16>>>k)=(l' ^^^ 8>>>k)%(16>>>k) →
    (l ^^^ 8>>>k)%(16>>>k)=l'%(16>>>k) := by decide +kernel

private theorem partner_lane {g k : Nat} :
    (g-g%32+(g%32 ^^^ 8>>>k))%32=g%32 ^^^ 8>>>k ∧
      (g-g%32+(g%32 ^^^ 8>>>k))-(g-g%32+(g%32 ^^^ 8>>>k))%32=g-g%32 := by
  have small : 8>>>k<32 := by
    have : 8>>>k≤8 := Nat.shiftRight_le _ _
    omega
  have : g%32 ^^^ 8>>>k<32 := Nat.xor_lt_two_pow (n:=5) (by omega) small
  omega

/-- The minimum a stage computes agrees between lanes that agree modulo half the stage's
period, given that the stage's operands agree modulo the period. -/
private theorem min_agree {L : Launch} {X : Execution} {Q m} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) {k : Nat} (hk : k<4)
    (ih : StageAgree L X k) {g u a r g' u' a' r'} (s1 : Stage X k g u a r)
    (s2 : Stage X k g' u' a' r') (low : g%L.block<128) (warp : g-g%32=g'-g'%32)
    (lanes : g%32%(8>>>k)=g'%32%(8>>>k))
    (cn : ((X.tr g).take u).countP Execution.isShfl=
      ((X.tr g').take u').countP Execution.isShfl) :
    Lib.minWord a r=Lib.minWord a' r' := by
  have hb : L.block=256 := hp.block
  have low' : g'%L.block<128 := by rw [hb] at low ⊢; omega
  obtain ⟨jp,rp,stp,cntp,lowp⟩ := stage_partner hp hX hf (by omega) low s1
  obtain ⟨jp',rp',stp',cntp',lowp'⟩ := stage_partner hp hX hf (by omega) low' s2
  obtain ⟨pl,pw⟩ := partner_lane (g := g) (k := k)
  obtain ⟨pl',pw'⟩ := partner_lane (g := g') (k := k)
  have l1 : g%32<32 := Nat.mod_lt _ (by decide)
  have l2 : g'%32<32 := Nat.mod_lt _ (by decide)
  have sh : 16>>>(k+1)=8>>>k := by interval_cases k <;> rfl
  have cnp : ((X.tr (g-g%32+(g%32 ^^^ 8>>>k))).take jp).countP Execution.isShfl=
      ((X.tr (g'-g'%32+(g'%32 ^^^ 8>>>k))).take jp').countP Execution.isShfl := by
    rw [cntp,cntp',cn]
  rcases lane_split k hk _ l1 _ l2 (by rw [sh]; exact lanes) with same|cross
  · have e1 := ih s1 s2 low warp same cn
    have e2 := ih stp stp' lowp (by omega)
      (by rw [pl,pl']; exact lane_flip k hk _ l1 _ l2 same) cnp
    rw [e1,e2]
  · have e1 := ih s1 stp' low (by omega) (by rw [pl']; exact cross) (by rw [cntp',cn])
    have e2 := ih stp s2 lowp (by omega)
      (by rw [pl]; exact lane_back k hk _ l1 _ l2 cross) (by rw [cntp,cn])
    rw [e1,e2,minWord_comm]

private theorem step_agree {L : Launch} {X : Execution} {Q m} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) {k : Nat} (hk : k<3)
    (ih : StageAgree L X k) : StageAgree L X (k+1) := by
  intro g j a r g' j' a' r' s1 s2 low warp lanes cnt
  obtain ⟨u,a1,r1,rfl,st1,ha⟩ := stage_back hp hX hk s1
  obtain ⟨u',a1',r1',rfl,st1',ha'⟩ := stage_back hp hX hk s2
  obtain ⟨⟨ok1,get1⟩,⟨ok2,get2⟩⟩ := And.intro st1 st1'
  rw [count_succ get1,count_succ get2] at cnt
  simp only [Execution.isShfl,ite_true,Nat.add_right_cancel_iff] at cnt
  have sh : 16>>>(k+1)=8>>>k := by interval_cases k <;> rfl
  rw [sh] at lanes
  rw [ha,ha']
  exact min_agree hp hX hf (by omega) ih st1 st1' low warp lanes cnt

/-- Every stage's operands agree, from the first stage's. -/
theorem stage_agree {L : Launch} {X : Execution} {Q m} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (alpha : StageAgree L X 0) : ∀ k, k≤3 → StageAgree L X k := by
  intro k
  induction k with
  | zero => exact fun _ => alpha
  | succ k ih => exact fun hk => step_agree hp hX hf (by omega) (ih (by omega))

/-- **The stores of one warp in one round are equal**, from the agreement of the first stage's
operands between the two halves of the warp. -/
theorem warp_stores_equal {L : Launch} {X : Execution} {Q m} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (alpha : StageAgree L X 0) : WarpStoresEqual L X := by
  intro h u t v dst ys acc zs one two cta warp lane ord visits
  have hb : L.block=256 := hp.block
  obtain ⟨u3,a1,r1,rfl,st1,hys⟩ := store_back hp hX one
  obtain ⟨v3,a1',r1',rfl,st1',hzs⟩ := store_back hp hX two
  obtain ⟨⟨ok1,get1⟩,⟨ok2,get2⟩⟩ := And.intro st1 st1'
  obtain ⟨r,mr,cr⟩ := store_round hp hX one
  obtain ⟨r',mr',cr'⟩ := store_round hp hX two
  have phys := physical_bar hp hX one (fun _ => nofun) (by show 574<2250; decide)
    (by show 2250<2331; decide)
  have phys' := physical_bar hp hX two (fun _ => nofun) (by show 574<2250; decide)
    (by show 2250<2331; decide)
  have same : mandatory ((X.tr h).take (u3+1))=mandatory ((X.tr t).take (v3+1)) := by
    change ((X.tr h).take (u3+1)).countP (Execution.isBarId 0)=_ at phys
    change ((X.tr t).take (v3+1)).countP (Execution.isBarId 0)=_ at phys'
    unfold barOrdinal at ord
    rw [cta] at phys
    omega
  have rr : r=r' := by omega
  subst rr
  have cn : ((X.tr h).take u3).countP Execution.isShfl=
      ((X.tr t).take v3).countP Execution.isShfl := by
    have c1 := count_succ get1
    have c2 := count_succ get2
    simp only [Execution.isShfl,ite_true] at c1 c2
    rw [cta] at cr
    omega
  have low : h%L.block<128 := lane
  have wp : h-h%32=t-t%32 := by
    have c := cta
    have w := warp
    rw [hb] at c w
    omega
  have sa : StageAgree L X 3 := stage_agree hp hX hf alpha 3 (le_refl _)
  rw [hys,hzs,min_agree hp hX hf (k := 3) (by omega) sa st1 st1' low wp
    (by show h%32%1=t%32%1; omega) cn]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
