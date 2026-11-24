-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValuePeerExists
import Lemmas.Order.ElectOrdinal
import Lemmas.Flow.PollRendezvous
import Lemmas.Order.WaitOrderObject

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof

private theorem shflPeerWitness {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g h i rank : Nat} (hw : SameWarp l g h)
    (hK : X.ShflK (g,i) rank) :
    ∃ k, Witness l X (.thread (h,k)) (g,i) ∧
      (X.ShflK (h,k) rank ∨ ∃ site, X.get (h,k) = some ⟨site,.exit⟩) := by
  obtain ⟨⟨pc,mode,a,b,c,recv,ok,hGet⟩, hOrd⟩ := hK
  have hReady := hX.dependency.ready (g,i) (by simp [Returned,hGet,Kind.resume])
  have hLane : laneOf l h < 32 := Nat.mod_lt _ (by decide)
  have hBit : (2^32-1 : Nat).testBit (laneOf l h) = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hLane
  have hNeed := maskNeeds_mem l shflClass X (g,i) hGet rfl hLane hBit
  have hn : Need.node (fun x => ∃ k,
      x = .thread (warpLane l g (laneOf l h),k) ∧
        MaskWait l shflClass X (warpLane l g (laneOf l h),k) (g,i)) ∈ Needs l X (g,i) := by
    simpa only [Needs,hGet,KindNeeds] using hNeed
  obtain ⟨ref,hPresent,k,rfl,hWait⟩ := hReady _ hn
  rw [Step.warpLane_of_sameWarp hw] at hPresent hWait
  refine ⟨k, ?_, ?_⟩
  · refine Witness.of_need l hn hPresent ?_
    rw [Step.warpLane_of_sameWarp hw]
    exact ⟨k,rfl,hWait⟩
  · obtain ⟨_,mask,n,q,hAt,hMate⟩ := hWait
    obtain ⟨hm,hn⟩ := (maskK_shflClass _ _ _ _).mp hAt.1
    have heq : n = rank := hn.2.symm.trans hOrd
    subst mask n
    rcases hMate with hS | ⟨_,hExit⟩
    · exact .inl ((maskK_shflClass _ _ _ _).mp hS.1).2
    · obtain ⟨site,he,_⟩ := (maskExitK_shflClass _ _ _ _).mp hExit
      exact .inr ⟨site,he⟩

private theorem shflCountBeforeElectLe {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g h i j : Nat}
    (hw : SameWarp l g h) (he : ElectOrd.Partner X (g,i) (h,j)) :
    ((X.tr g).take i).countP Execution.isShfl ≤ ((X.tr h).take j).countP Execution.isShfl := by
  let rank := ((X.tr h).take j).countP Execution.isShfl
  by_contra! hGt
  obtain ⟨suffix,hTrace⟩ := List.take_prefix i (X.tr g)
  have hCount : rank + 1 ≤ (X.tr g).countP Execution.isShfl := by
    rw [← hTrace,List.countP_append]
    omega
  obtain ⟨a,ha⟩ := Step.exists_shflK hCount
  have haBefore : a < i := by
    by_contra! h
    have hMono := countP_take_mono Execution.isShfl (X.tr g) h
    have hA : ((X.tr g).take a).countP Execution.isShfl = rank := ha.2
    omega
  obtain ⟨b,hB,hKind⟩ := shflPeerWitness hX hw ha
  obtain ⟨hPc,gPc,hMask,gMask,inst,lead,lead',hE,hE'⟩ := he
  have hJ : j < (X.tr h).length := ElectOrd.lt_len hE'
  have hAfter : j < b ∧ b < (X.tr h).length := by
    rcases hKind with hS | ⟨site,hExit⟩
    · have hBLength : b < (X.tr h).length := hS.lt
      refine ⟨?_,hBLength⟩
      by_contra! hBLe
      rcases Nat.lt_or_eq_of_le hBLe with hlt | rfl
      · have hs := shfl_count_succ hS
        have hMono := countP_take_mono Execution.isShfl (X.tr h) (show b+1 ≤ j by omega)
        dsimp only [rank] at hs
        omega
      · obtain ⟨⟨pc,mode,x,y,z,r,o,hGet⟩,_⟩ := hS
        cases congrArg Event.kind (Option.some.inj (hGet.symm.trans hE'))
    · have hLast := Execution.exit_last hX hw.1.2.1 hExit
      have hNe : j ≠ b := by
        rintro rfl
        cases congrArg Event.kind (Option.some.inj (hExit.symm.trans hE'))
      exact ⟨by omega, (List.getElem?_eq_some_iff.mp hExit).1⟩
  obtain ⟨⟨pc,mode,x,y,z,r,o,hA⟩,_⟩ := ha
  have hAResume : DepStep l kernel X (.thread (g,a),true) (.thread (g,i),false) :=
    DepStep.of_resumes l (Resumes.of_blocking hA rfl ⟨rfl,haBefore,ElectOrd.lt_len hE⟩)
  have hEAfter := elect_depStep hX hw hE hE' hAfter.1 hAfter.2
  exact hX.depStepAcyclic _ ((Relation.TransGen.single hAResume).trans
    (hEAfter.tail (DepStep.of_witness l hB)))

/-- Matching full-warp elections cut the same prefix of shuffle ordinals in
their lanes. Reversing a shuffle and its matching election would create a dependency cycle. -/
theorem shuffleCountAtMatchedElection {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g h i j : Nat}
    (hw : SameWarp l g h) (he : ElectOrd.Partner X (g,i) (h,j)) :
    ((X.tr g).take i).countP Execution.isShfl = ((X.tr h).take j).countP Execution.isShfl :=
  Nat.le_antisymm (shflCountBeforeElectLe hX hw he)
    (shflCountBeforeElectLe hX (sameWarp_symm hw) he.symm)

end PTX.Kernels.TmlFa4Fwd.Thread
