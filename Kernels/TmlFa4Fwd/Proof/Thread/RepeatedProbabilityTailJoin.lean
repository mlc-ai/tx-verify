-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityCredit
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
import all Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
import Lemmas.Step.Object

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction AsyncCopy

private theorem tailProbabilitySignalLoc (l : Launch) (g : Nat) (warp : Fin 8) (round : Round) :
    signalLoc l g (stageOf warp) (tailPublication round) =
      Thread.Scores.probabilityObject l (g/l.block) (stageOf warp) 1 := by
  cases round <;> simp [tailPublication,signalLoc,signalSite,Thread.Scores.probabilityObject] <;>
    omega

/-- The actual elected tail lane publishes a unit credit. Other lanes take the
local skip, and both routes preserve the live operands at the correction join. -/
theorem repeatedProbabilityTailJoinOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (round : Round) (warp : Fin 8) (values : Option (Nat → Value)) (keep chosen : Bool)
    (c : OpeningTripCursor l X g (probabilityWaitPc round true+3)
      ((tailElectPred round,.pred chosen)::tailCarryWith l warp round values keep)) :
    ∃ u : OpeningTripCursor l X g ((signalSite (tailPublication round)).pc+1)
        (tailCarryWith l warp round values keep),
      (chosen = true →
        Thread.Scores.ProbabilityCredit l X (g,c.pos) (g/l.block) (stageOf warp) 1) ∧
      u.pos = (if chosen then c.pos+1 else c.pos) ∧ u.ending = c.ending := by
  let i := tailPublication round
  let stage := stageOf warp
  let loc := signalLoc l g stage i
  let carry := tailCarryWith l warp round values keep
  obtain ⟨s,hLocal,hs⟩ := ((tailNegate l g round warp values keep chosen).comp
    (tailBranch round warp values keep chosen)).rtg c.checkpoint
  cases chosen with
  | false =>
    exact ⟨⟨c.pos,c.before,s,c.ending,c.positive,c.bounded,c.released,hs,c.recorded,
      c.remaining,c.localSteps.trans hLocal⟩,(fun h => by cases h),rfl,rfl⟩
  | true =>
    obtain ⟨v,hPrepare,hv⟩ := (tailPrepare hp g round warp values keep).rtg hs
    let u := next (mbarStateDest v (some (signalSite i).state))
    have hOut : out kernel Assumptions.all l g v = .ev (.arrive loc 0 u 1 true .cta) :=
      signalTemplate hp stage i hv.1 hv.2.2.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2.1
    let event := Event.mk v.pc (.arrive loc 0 1 true .cta)
    have hStep : EStep kernel Assumptions.all l g v event (some u) := ⟨_,hOut,rfl,rfl⟩
    have hReach := c.localSteps.trans (hLocal.trans hPrepare)
    have hRecord : c.pos < (X.tr g).length := by
      by_contra! hShort
      have hEnd := Nat.le_antisymm c.bounded hShort
      have hStarted : X.tr g ≠ [] := List.ne_nil_of_length_pos (by
        have := c.positive
        omega)
      have hPast : Run kernel Assumptions.all l g {} (X.tr g) (some c.before) := by
        simpa only [List.take_of_length_le hShort] using c.recorded
      apply hMax.not_grows
      refine Step.object_counted_extension_silent hMax.1 (by trivial) hg (.inl hStarted)
        (c.released hEnd) hPast hReach hStep ⟨trivial,fun _ h => by cases h⟩ (by trivial)
        (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) rfl (mb := loc) (act := .arrive 1 0)
        (fun _ _ h => by cases h) ?_ ?_
      · intro a
        by_cases h : a = loc
        · subst a
          simp [objectAction,snoc_get_new,event]
        · simp [objectAction,snoc_get_new,event,h,Ne.symm h]
      · intro ref
        exact Assumptions.wfStep.quiet hMax.1
          (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
            ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
              (Execution.noNewRead_of_tr rfl))
    have hn := Next.mk hReach hOut
    obtain ⟨_,_,he,⟨rfl,hAfter⟩,hTail⟩ := hn.continuing_at_nonempty
      (by rintro _ ⟨_,h⟩; cases h) c.remaining
      (fun hNil => (Nat.not_le_of_lt hRecord) (List.drop_eq_nil_iff.mp hNil))
    obtain rfl := Option.some.inj hAfter
    have hu : At u ((signalSite i).pc+1) carry := by
      refine ⟨congrArg (·+1) hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,?_⟩
      exact holds_update hv.2.2.2.2.2.2 (fun pair hPair => by
        rcases tailCarryWith_member hPair with h | h | h
        · rw [h]
          cases round <;> decide
        · rw [h]
          cases round <;> decide
        · exact (tailLiveDistinct round keep h).2.2)
    have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some u) := by
      rw [List.take_add_one,show (X.tr g)[c.pos]? = some event from he]
      exact c.recorded.snoc hReach hStep
    have hRelease (hEnd : c.pos+1 = (X.tr g).length) : Step.Released l X g :=
      Prologue.releasedIfLast he (by simp [Kind.resume]) hEnd
    refine ⟨⟨c.pos+1,u,u,c.ending,Nat.succ_pos _,len_of_get he,hRelease,hu,
      hPast,hTail,.refl⟩,fun _ => ⟨v.pc,?_⟩,rfl,rfl⟩
    change X.get (g,c.pos) = some ⟨v.pc,.arrive (signalLoc l g (stageOf warp)
      (tailPublication round)) 0 1 true .cta⟩ at he
    rwa [tailProbabilitySignalLoc] at he

end PTX.Kernels.TmlFa4Fwd.Softmax
