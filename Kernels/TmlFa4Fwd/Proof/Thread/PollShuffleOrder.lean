-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollSynced
import Lemmas.Flow.PollRendezvous

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof

/-- If one lane has returned from more shuffles, the first such shuffle depends
on a later event of its peer. The witness can also be the peer's normal exit. -/
theorem pollBeforeOfShuffleCount {K : Kernel} {A : List Assumption}
    {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l K A m X)
    {g h i j pc phase : Nat} {loc : Loc} {ok acq : Bool} {scope : MbarScope} {f : Event}
    (hw : SameWarp l g h) (he : X.get (g,i) = some ⟨pc,.wait loc phase ok acq scope⟩)
    (hf : X.get (h,j) = some f)
    (hCount : ((X.tr g).take i).countP Execution.isShfl <
      ((X.tr h).take j).countP Execution.isShfl) :
    PollBefore l K X (g,i) (h,j) := by
  let rank := ((X.tr g).take i).countP Execution.isShfl
  obtain ⟨b,hBefore,e,hGet,hShfl,hRank⟩ :=
    Flow.exists_nth Execution.isShfl (X.tr h) (n := rank) (k := j) hCount
  obtain ⟨site,mode,x,y,z,r,valid,rfl⟩ :
      ∃ site mode x y z r valid, e = ⟨site,.shfl mode x y z r valid⟩ := by
    obtain ⟨site,kind⟩ := e
    cases kind <;> try cases hShfl
    exact ⟨_,_,_,_,_,_,_,rfl⟩
  let shfl : Event := ⟨site,.shfl mode x y z r valid⟩
  have hb : X.get (h,b) = some shfl := hGet
  have hLength : j < (X.tr h).length := len_of_get hf
  have hReturned : Returned X (h,b) := by simp [Returned,hb,shfl,Kind.resume]
  have hReady := hX.dependency.ready _ hReturned
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hThread : warpLane l h (laneOf l g) = g := Step.warpLane_of_sameWarp (sameWarp_symm hw)
  have hMem := maskNeeds_mem l shflClass X (h,b) hb rfl hLane
    (Nat.testBit_two_pow_sub_one 32 _ ▸ decide_eq_true hLane)
  have hNeed : Need.node (fun x => ∃ a, x = .thread (g,a) ∧
      MaskWait l shflClass X (g,a) (h,b)) ∈ Needs l X (h,b) := by
    simpa only [Needs, hb, KindNeeds, hThread] using hMem
  obtain ⟨_,_,a,rfl,hMask⟩ := hReady _ hNeed
  have hPart := hMask
  obtain ⟨_, mask, ordinal, value, hAt, hPeer⟩ := hPart
  obtain ⟨rfl, hB⟩ := (maskK_shflClass _ _ _ _).mp hAt.1
  have hEq : ordinal = rank := hB.2.symm.trans hRank
  subst ordinal
  have hActual : ∃ e, X.get (g,a) = some e ∧ i < a := by
    rcases hPeer with hEvent | ⟨_, hExit⟩
    · have hA := (maskK_shflClass _ _ _ _).mp hEvent.1 |>.2
      have hStep := shfl_count_succ hA
      obtain ⟨⟨p, m, v, u, c, result, flag, hAGet⟩,_⟩ := hA
      refine ⟨_,hAGet,?_⟩
      have hn : a ≠ i := fun h => by
        subst a
        cases congrArg Event.kind (Option.some.inj (hAGet.symm.trans he))
      by_contra! hTooEarly
      have hEarlier := Nat.lt_of_le_of_ne hTooEarly hn
      have hMon := countP_take_mono Execution.isShfl (X.tr g) (show a+1 ≤ i by omega)
      change _ = ((X.tr g).take i).countP Execution.isShfl + 1 at hStep
      omega
    · obtain ⟨stop,hStop,_⟩ := (maskExitK_shflClass _ _ _ _).mp hExit
      refine ⟨_,hStop,?_⟩
      have hLast := Execution.exit_last hX hw.1.1 hStop
      have hLen : i < (X.tr g).length := len_of_get he
      have hNe : i ≠ a := fun h => by
        subst a
        cases congrArg Event.kind (Option.some.inj (hStop.symm.trans he))
      omega
  obtain ⟨e,ha,haAfter⟩ := hActual
  have hWitness : Witness l X (.thread (g,a)) (h,b) :=
    Witness.of_need l hNeed ⟨e,ha⟩ ⟨a,rfl,hMask⟩
  exact ⟨a,haAfter,.tail (.single (.inl (DepStep.of_witness l hWitness)))
    (.inl (DepStep.of_resumes l (Resumes.of_blocking (b := true) hb rfl
      ⟨rfl,hBefore,hLength⟩)))⟩

end PTX.Kernels.TmlFa4Fwd.Thread
