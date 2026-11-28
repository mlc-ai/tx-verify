-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollMeet

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- A poll also precedes a peer's later shuffle when the peer resumed using
the polling lane's exit as its mask witness. -/
public theorem meet_poll_shfl {L K A m X g h k k' pc l p ok a sc}
    (hX : Consistent L K A m X) (hw : SameWarp L g h)
    (he : X.get (g,k)=some ⟨pc,.wait l p ok a sc⟩)
    (lt : ((X.tr g).take k).countP Execution.isShfl < ((X.tr h).take k').countP Execution.isShfl)
    (len : k'<(X.tr h).length) : PollBefore L K X (g,k) (h,k') := by
  let c := ((X.tr g).take k).countP Execution.isShfl
  have count := countP_take_mono Execution.isShfl (X.tr h) (Nat.le_of_lt len)
  rw [List.take_length] at count
  obtain ⟨b,hb⟩ := Step.exists_shflK (X := X)
    (show c+1 ≤ (X.tr h).countP Execution.isShfl by dsimp [c]; omega)
  obtain ⟨⟨pb,md,x,y,z,r,o,get⟩,nb⟩ := id hb
  have later : b<k' := pos_before nb lt
  have ready : Ready L X (h,b) := hX.dependency.ready _ (by simp [Returned,get,Kind.resume])
  have lane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have need := maskNeeds_mem L shflClass X (h,b) get rfl lane
    (Nat.testBit_two_pow_sub_one 32 _ ▸ decide_eq_true lane)
  have need' : Need.node (fun t => ∃ j, t = .thread (warpLane L h (laneOf L g),j) ∧
      MaskWait L shflClass X (warpLane L h (laneOf L g),j) (h,b)) ∈ Needs L X (h,b) := by
    simpa only [Needs,get,KindNeeds] using need
  obtain ⟨_,present,j,rfl,mask⟩ := ready _ need'
  have wl := Step.warpLane_of_sameWarp (sameWarp_symm hw)
  have mask' := wl ▸ mask
  obtain ⟨_,m',n',_,atb,hj⟩ := mask'
  obtain ⟨rfl,hb'⟩ := (maskK_shflClass _ _ _ _).mp atb.1
  have eq := hb'.2.symm.trans nb
  change n'=c at eq
  subst n'
  have after : k<j := by
    rcases hj with sh | ⟨_,ex⟩
    · have hs := ((maskK_shflClass _ _ _ _).mp sh.1).2
      obtain ⟨⟨_,_,_,_,_,_,_,sg⟩,nu⟩ := hs
      exact count_after he rfl nu ⟨_,sg,rfl⟩
    · obtain ⟨p',ge,_⟩ := (maskExitK_shflClass _ _ _ _).mp ex
      have last := Execution.exit_last hX hw.1.1 ge
      have seen := (List.getElem?_eq_some_iff.mp he).1
      change k < (X.tr g).length at seen
      change j+1 = (X.tr g).length at last
      have ne : k≠j := by rintro rfl; rw [he] at ge; cases ge
      omega
  have witness : Witness L X (.thread (g,j)) (h,b) :=
    Witness.of_need L need' (wl ▸ present) ⟨j,by rw [wl],mask⟩
  exact ⟨j,after,.tail (.single (.inl (DepStep.of_witness L witness)))
    (.inl (DepStep.of_resumes L (Resumes.of_blocking get rfl ⟨rfl,later,len⟩)))⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
