-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollMeet
public import Lemmas.Kernel.Progress.NextEv

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- Before a later event the issuer's completed full-mask shuffles are also present
in each live peer. A peer with a next-event witness cannot satisfy the mask by an exit. -/
public theorem shuffle_credit {L K A m X g h k e ev} (hX : Consistent L K A m X)
    (hw : SameWarp L g h) (hn : Sched.NextEv L K A m X g e) (he : X.get (h,k)=some ev) :
    ((X.tr h).take k).countP Execution.isShfl ≤ (X.tr g).countP Execution.isShfl := by
  by_contra! lt
  let c := (X.tr g).countP Execution.isShfl
  have count := countP_take_mono Execution.isShfl (X.tr h)
    (List.getElem?_eq_some_iff.mp he).1.le
  rw [List.take_length] at count
  dsimp only at count
  obtain ⟨b,hb⟩ := Step.exists_shflK (X := X)
    (show c+1≤(X.tr h).countP Execution.isShfl by dsimp [c]; omega)
  obtain ⟨⟨_,_,_,_,_,_,_,get⟩,nb⟩ := id hb
  have b_lt := pos_before nb lt
  have ready : Ready L X (h,b) := hX.dependency.ready _ (by simp [Returned,get,Kind.resume])
  have lane : laneOf L g<32 := Nat.mod_lt _ (by decide)
  have need := maskNeeds_mem L shflClass X (h,b) get rfl lane
    (Nat.testBit_two_pow_sub_one 32 _ ▸ decide_eq_true lane)
  have need' : Need.node (fun t => ∃ j, t=.thread (warpLane L h (laneOf L g),j) ∧
      MaskWait L shflClass X (warpLane L h (laneOf L g),j) (h,b)) ∈ Needs L X (h,b) := by
    simpa only [Needs,get,KindNeeds] using need
  obtain ⟨_,_,j,rfl,mask⟩ := ready _ need'
  rw [Step.warpLane_of_sameWarp (sameWarp_symm hw)] at mask
  obtain ⟨_,_,_,_,atb,hj⟩ := mask
  obtain ⟨rfl,sh⟩ := (maskK_shflClass _ _ _ _).mp atb.1
  rcases hj with vote|⟨_,ex⟩
  · obtain ⟨_,⟨⟨_,_,_,_,_,_,_,hj⟩,ord⟩⟩ := (maskK_shflClass _ _ _ _).mp vote.1
    have num := sh.2.symm.trans nb
    have next := countP_take_succ (p := Execution.isShfl) hj rfl
    have len := (List.getElem?_eq_some_iff.mp hj).1
    have max := countP_take_mono Execution.isShfl (X.tr g) (Nat.succ_le_of_lt len)
    rw [List.take_length] at max
    dsimp only at next max ord
    dsimp [c] at num
    change ((X.tr g).take (j+1)).countP Execution.isShfl ≤ (X.tr g).countP Execution.isShfl at max
    exact (Nat.not_lt_of_ge max) (by omega)
  · obtain ⟨p,exit,_⟩ := (maskExitK_shflClass _ _ _ _).mp ex
    obtain ⟨Y,hY,pref,later⟩ := hn
    have len := (List.getElem?_eq_some_iff.mp exit).1
    have keep : Y.get (g,j)=some ⟨p,.exit⟩ := by
      change (Y.tr g)[j]?=_
      change (X.tr g)[j]?=_ at exit
      rw [←pref,List.getElem?_take,ite_eq_left len] at exit
      exact exit
    have last := Execution.exit_last hY hw.1.1 keep
    have more := (List.getElem?_eq_some_iff.mp later).1
    dsimp only at len more last
    omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
