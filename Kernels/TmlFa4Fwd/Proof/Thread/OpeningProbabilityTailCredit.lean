-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityElection
import Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.RegisterProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.Object
import Lemmas.Order.ElectOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue AsyncCopy

private theorem replayReturningPath {l : Launch} {g : Nat} {t u : TState} {es : List Event}
    (h : TraceReach kernel Assumptions.all l g t es u)
    {initial before : TState} {esBefore : List Event}
    (hPrefix : Run kernel Assumptions.all l g initial esBefore (some before))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t) :
    ∃ after, Run kernel Assumptions.all l g initial (esBefore ++ es) (some after) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after u := by
  induction h generalizing before esBefore with
  | refl => exact ⟨before,by simpa using hPrefix,hLocal⟩
  | tau hs _ ih => exact ih hPrefix (hLocal.tail hs)
  | @event _ _ _ _ e he _ ih =>
    simpa only [List.append_assoc,List.singleton_append] using
      ih (hPrefix.snoc hLocal he) .refl

private theorem electionStartupFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (c : OpeningProbabilityElection p l X g stage)
    (w : Fin 8) (hw : w.val = warpIndex l g) :
    Holds (next (next c.barrier.wait.tail.state)).regs (tailFrame l w) := by
  let pos := c.barrier.wait.tail.main.main.stored.wait.statistics.index+10
  let t := next (next c.barrier.wait.tail.state)
  obtain ⟨j,u,_,e,inc,n,inst,he,hKind,_,hu,hBefore,hTail⟩ :=
    Thread.Register.requestReturn hp hMax hg
  have hWarp : (⟨warpIndex l g, warpIndex_lt hp g⟩ : Fin 16) =
      ⟨w.val, w.isLt.trans (by decide)⟩ := Fin.ext hw.symm
  have hHint : registerHintPc (⟨w.val, w.isLt.trans (by decide)⟩ : Fin 16) = 3102 := by
    fin_cases w <;> decide
  have he' : SetMaxNReg.Request X (g,j) e.pc inc n inst := by
    change X.get (g,j) = some ⟨e.pc,.setMaxReg inc n inst⟩
    rw [he]
    cases e
    cases hKind
    rfl
  have hReq := (registerRequestShape hp hMax.1 he').2.1
  rw [hWarp,hHint] at hReq hu
  have hElection : X.get (g,pos) = some ⟨4859,.elect 4294967295 c.label c.leader⟩ := c.elected
  have hIndex : j+1 ≤ pos := c.afterEarlierEvent hMax.1 he (by rw [hReq]; decide)
  have hEntry : At u 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)] := by
    simpa only [hw] using hu
  obtain ⟨v,_,_,_,hWarpReg,hShared,_,_,hEvent,_,hReach⟩ :=
    softmaxRoleEventFromEntryWithScratch hp w hEntry hTail hElection hIndex
      (show 4859 < 7742 by decide)
      (Q := fun _ => True) trivial (by simp)
  obtain ⟨after,hPast,hLocal⟩ := replayReturningPath hReach hBefore .refl
  have hSplit : ((X.tr g).take (j+1)) ++ (((X.tr g).drop (j+1)).take (pos-(j+1))) =
      (X.tr g).take pos := by
    have h := List.take_append_drop (j+1) ((X.tr g).take pos)
    simpa only [List.take_take,Nat.min_eq_left hIndex,List.drop_take] using h
  rw [hSplit] at hPast
  have hSame := Run.det hPast c.barrier.recorded
  obtain rfl := Option.some.inj hSame
  have ht : At t 4859 [] := c.barrier.wait.tail.ready.next.next
  have htStop : Stops kernel Assumptions.all l g t := by
    rw [Stops,out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_4859) rfl rfl]
    exact ⟨_,rfl⟩
  have hvStop := stops_of_estep hEvent
  have hEq := stop_unique hLocal .refl hvStop htStop
  simpa only [hEq,tailFrame,Holds] using And.intro hWarpReg (And.intro hShared trivial)

/-- The selected lane of an active softmax warp publishes its opening P-tail credit. -/
theorem OpeningProbabilityElection.creditAtElectionOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (hRole : warpIndex l g/4 = stage.val)
    (c : OpeningProbabilityElection p l X g stage) (hLeader : laneOf l g = c.leader) :
    Thread.Scores.ProbabilityCredit l X
      (g,c.barrier.wait.tail.main.main.stored.wait.statistics.index+11) (g/l.block) stage 1 := by
  let w : Fin 8 := ⟨warpIndex l g, by have := stage.isLt; omega⟩
  have hStage : stageOf w = stage := Fin.ext hRole
  let t := next (next c.barrier.wait.tail.state)
  let s := tailElectionReturn l g t c.leader
  let pos := c.barrier.wait.tail.main.main.stored.wait.statistics.index+10
  have ht : At t 4859 [] := c.barrier.wait.tail.ready.next.next
  have hFrame := electionStartupFrame hp hMax hg c w rfl
  change Holds t.regs (tailFrame l w) at hFrame
  have hAt : At s 4860 ((623,.pred true) :: tailFrame l w) := by
    refine ⟨congrArg (·+1) ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,?_⟩
    simp [s,tailElectionReturn,next,setReg,hLeader,tailFrame] at hFrame ⊢
    exact hFrame
  obtain ⟨u,v,hn⟩ := firstTailSelectedRelease hp w hAt
  rw [hStage] at hn
  let addr := signalLoc l g stage 2
  let event := Event.mk u.pc (.arrive addr 0 1 true .cta)
  have hStep : EStep kernel Assumptions.all l g u event (some v) := ⟨_,hn.stop,rfl,rfl⟩
  have hBound : pos+1 ≤ (X.tr g).length := len_of_get c.elected
  have hLt : pos+1 < (X.tr g).length := by
    by_contra! hShort
    have hEq := Nat.le_antisymm hBound hShort
    have hReleased : Step.Released l X g := by
      constructor
      intro _ _ _ _
      have hPrev : (X.tr g).length-1 = pos := by omega
      rw [hPrev]
      exact elect_ready hMax.1 c.elected
    have hStarted : X.tr g ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hBefore : Run kernel Assumptions.all l g {} (X.tr g) (some s) := by
      have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some s) := c.recorded
      rw [List.take_of_length_le hShort] at hPast
      exact hPast
    apply hMax.not_grows
    refine Step.object_counted_extension_silent hMax.1 (by trivial) hg (.inl hStarted)
      hReleased hBefore hn.steps hStep ⟨trivial,fun _ h => by cases h⟩ (by trivial)
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rfl (mb := addr) (act := .arrive 1 0)
      (fun _ _ h => by cases h) ?_ ?_
    · intro loc
      by_cases h : loc = addr
      · subst loc
        simp [objectAction,snoc_get_new,event]
      · simp [objectAction,snoc_get_new,event,h,Ne.symm h]
    · intro rec
      exact Assumptions.wfStep.quiet hMax.1
        (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  obtain ⟨_,_,he,⟨rfl,_⟩,_⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) c.continuation
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  have hLoc : addr = Thread.Scores.probabilityObject l (g/l.block) stage 1 := by
    change Loc.mk .shared (g/l.block) (l.sharedBase+8*stage.val+112) =
      Loc.mk .shared (g/l.block) (l.sharedBase+(96+8*stage.val+16))
    congr 1
    omega
  change X.get (g,pos+1) = some ⟨u.pc,.arrive addr 0 1 true .cta⟩ at he
  exact ⟨u.pc,hLoc ▸ he⟩

theorem OpeningProbabilityElection.creditOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (hRole : warpIndex l g/4 = stage.val)
    (c : OpeningProbabilityElection p l X g stage) (hLeader : laneOf l g = c.leader) :
    ∃ j, Thread.Scores.ProbabilityCredit l X (g,j) (g/l.block) stage 1 := by
  exact ⟨_,c.creditAtElectionOfMaximal hp hMax hg hRole hLeader⟩

/-- The recorded election identifies a real selected lane in the same warp. -/
theorem OpeningProbabilityElection.selectedPeer {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (c : OpeningProbabilityElection p l X g stage)
    (hPeers : ∀ peer, SameWarp l g peer →
      Nonempty (OpeningProbabilityElection p l X peer stage)) :
    ∃ peer, SameWarp l g peer ∧ ∃ o : OpeningProbabilityElection p l X peer stage,
      laneOf l peer = o.leader := by
  obtain ⟨hWarp,hLane⟩ := Step.sameWarp_lane (by rw [hp.block]) hg c.leader.isLt
  obtain ⟨o⟩ := hPeers _ hWarp
  exact ⟨_,hWarp,o,hLane.trans (hX.elect.2.2 _ _ _ _ _ _ _ _ _ c.elected o.elected hWarp)⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
