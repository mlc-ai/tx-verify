-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityCredit
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublish
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part116
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import all Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
import Lemmas.Flow.CountTake
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction AsyncCopy

private theorem firstProbabilitySignalLoc (l : Launch) (g : Nat) (stage : Fin 2)
    (round : Round) :
    signalLoc l g stage (firstPublication round) =
      Thread.Scores.probabilityObject l (g/l.block) stage 0 := by
  cases round <;> simp [firstPublication,signalLoc,signalSite,Thread.Scores.probabilityObject] <;>
    omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
include hp hMax

/-- Reaching the decoded P wait suffices to issue the actual collective. -/
theorem probabilityStoreWaitOfMaximal (hg : g < l.threads) (round : Round) (tail : Bool)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (probabilityWaitPc round tail) F) :
    X.get (g,c.pos) = some ⟨probabilityWaitPc round tail,.tc .waitSt⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some (next c.ready)) ∧
      Run kernel Assumptions.all l g (next c.ready) ((X.tr g).drop (c.pos+1)) c.ending := by
  have hOut :=
    probabilityWaitTemplate hp round tail (g := g) c.checkpoint.1 c.checkpoint.2.2.2.1
  obtain ⟨he,hPast,hTail⟩ := probabilityCollectiveOfMaximal hg c.positive c.bounded
    hOut rfl nofun c.recorded c.localSteps c.remaining (fun h => ⟨X,hMax,rfl,c.released h⟩)
  rw [c.checkpoint.1] at he
  exact ⟨he,hPast,hTail⟩

/-- Reaching the decoded main P wait suffices to issue the actual collective. -/
theorem mainProbabilityWaitOfMaximal (hg : g < l.threads) (round : Round) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (probabilityWaitPc round false) F) :
    X.get (g,c.pos) = some ⟨probabilityWaitPc round false,.tc .waitSt⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some (next c.ready)) ∧
      Run kernel Assumptions.all l g (next c.ready) ((X.tr g).drop (c.pos+1)) c.ending := by
  exact probabilityStoreWaitOfMaximal hp hMax hg round false c

omit hp hMax in
/-- Registers written by the setup and returned state of the main probability arrival. -/
def mainProbabilityCreditWrites (round : Round) : List Nat :=
  match round with
  | .first => [8186,3927]
  | .biased => 8603 :: biasedReleaseScratch
  | .unbiased => [8850,5781]

omit hp hMax in
private theorem mainProbabilitySignalKeeps {l : Launch} {g : Nat} (round : Round)
    {s t : TState} (hs : At s (probabilityWaitPc round false+1) [])
    (hRun : run kernel Assumptions.all l g (firstPublicationSteps round) s = some t)
    (r : Nat) (hr : r ∉ mainProbabilityCreditWrites round) : t.regs r = s.regs r := by
  cases round with
  | biased =>
    exact biasedReleaseFrame (by rw [hs.1]; decide) (by rw [hs.1]; decide) hRun r
      (fun h => hr (.tail _ h))
  | first =>
    have hLocal : run kernel Assumptions.all l g 1 s = some (next (setReg s 3927 (b32 1))) := by
      apply run_local Flow.code_4846 rfl hs
      rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil
        (by rw [hs.1]; decide) rfl]
      rfl
    obtain rfl := Option.some.inj (hRun.symm.trans hLocal)
    have hNe : r ≠ 3927 := by
      intro h
      subst r
      exact hr (.tail _ (.head _))
    exact Function.update_of_ne hNe _ _
  | unbiased =>
    have hLocal : run kernel Assumptions.all l g 1 s = some (next (setReg s 5781 (b32 1))) := by
      apply run_local Flow.code_7436 rfl hs
      rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil
        (by rw [hs.1]; decide) rfl]
      rfl
    obtain rfl := Option.some.inj (hRun.symm.trans hLocal)
    have hNe : r ≠ 5781 := by
      intro h
      subst r
      exact hr (.tail _ (.head _))
    exact Function.update_of_ne hNe _ _

/-- A reached main-packet wait and the matching warp operations suffice for every
lane's stage credit. The returned position can proceed to the fourth P quarter. -/
theorem mainProbabilityCreditOfMaximalKeeping (hg : g < l.threads) (round : Round) (stage : Fin 2)
    (c : OpeningTripCursor l X g (probabilityWaitPc round false)
      (firstPublicationFacts l stage round))
    (hPeers : c.pos+1 = (X.tr g).length → ∀ peer ∈ warpLanes l g, ∃ k,
      X.TcK (peer,k) (((X.tr g).take c.pos).countP isTcColl)) :
    let site := signalSite (firstPublication round)
    ∃ u : OpeningTripCursor l X g (site.pc+1) [],
      X.get (g,c.pos) = some ⟨probabilityWaitPc round false,.tc .waitSt⟩ ∧
      Thread.Scores.ProbabilityCredit l X (g,c.pos+1) (g/l.block) stage 0 ∧
      u.pos = c.pos+2 ∧ u.ending = c.ending ∧
      ((X.tr g).take u.pos).countP isTcColl = ((X.tr g).take c.pos).countP isTcColl+1 ∧
      ∀ r ∉ mainProbabilityCreditWrites round, u.ready.regs r = c.ready.regs r := by
  let site := signalSite (firstPublication round)
  let addr := signalLoc l g stage (firstPublication round)
  obtain ⟨hWait,hPast,hTail⟩ := mainProbabilityWaitOfMaximal hp hMax hg round c
  obtain ⟨v,hLocal,hAt⟩ := (firstPublicationSetup hp g round stage).apply c.checkpoint.next
  let u := next (mbarStateDest v (some site.state))
  have hSignal : out kernel Assumptions.all l g v = .ev (.arrive addr 0 u 1 true .cta) :=
    signalTemplate hp stage (firstPublication round) hAt.1 hAt.2.2.2.1
      hAt.2.2.2.2.1 hAt.2.2.2.2.2.1
  let event := Event.mk v.pc (.arrive addr 0 1 true .cta)
  have hStep : EStep kernel Assumptions.all l g v event (some u) := ⟨_,hSignal,rfl,rfl⟩
  have hBound : c.pos+1 ≤ (X.tr g).length := len_of_get hWait
  have hLt : c.pos+1 < (X.tr g).length := by
    by_contra! hShort
    have hEq := Nat.le_antisymm hBound hShort
    have hReleased := probabilityCollectiveReleased hWait (.inr (.inl rfl)) rfl
      (hPeers hEq) hEq
    have hStarted : X.tr g ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hBefore : Run kernel Assumptions.all l g {} (X.tr g) (some (next c.ready)) := by
      simpa only [List.take_of_length_le hShort] using hPast
    apply hMax.not_grows
    refine Step.object_counted_extension_silent hMax.1 (by trivial) hg (.inl hStarted)
      hReleased hBefore (run_rtg hLocal) hStep ⟨trivial,fun _ h => by cases h⟩ (by trivial)
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
  have hn : Next kernel Assumptions.all l g (next c.ready) v (.arrive addr 0 u 1 true .cta) :=
    ⟨run_rtg hLocal,hSignal⟩
  obtain ⟨_,_,hGet,⟨rfl,hAfter⟩,hRemaining⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hAfter
  have hRecord : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+2)) (some u) := by
    change Run kernel Assumptions.all l g {} ((X.tr g).take ((c.pos+1)+1)) (some u)
    rw [List.take_add_one,show (X.tr g)[c.pos+1]? = some event from hGet]
    exact hPast.snoc (run_rtg hLocal) hStep
  have hShape : At u (site.pc+1) [] :=
    ⟨congrArg (·+1) hAt.1,hAt.2.1,hAt.2.2.1,hAt.2.2.2.1,trivial⟩
  have hRelease (hEnd : c.pos+2 = (X.tr g).length) : Step.Released l X g :=
    Prologue.releasedIfLast hGet (by simp [Kind.resume]) hEnd
  refine ⟨⟨c.pos+2,u,u,c.ending,by omega,len_of_get hGet,hRelease,hShape,hRecord,
    hRemaining,.refl⟩,hWait,?_,rfl,rfl,?_,?_⟩
  · change X.get (g,c.pos+1) = some ⟨v.pc,.arrive (signalLoc l g stage (firstPublication round))
      0 1 true .cta⟩ at hGet
    exact ⟨_,by rwa [firstProbabilitySignalLoc] at hGet⟩
  · change ((X.tr g).take ((c.pos+1)+1)).countP isTcColl = _
    rw [countP_take_succ_false (p := isTcColl) hGet rfl,countP_take_succ (p := isTcColl) hWait rfl]
  · intro r hr
    have hn : r ≠ site.state := by
      intro h
      apply hr
      rw [h]
      cases round <;> exact .head _
    change u.regs r = c.ready.regs r
    simp only [u,next,mbarStateDest,Function.update_of_ne hn]
    exact mainProbabilitySignalKeeps round (c.checkpoint.next.mono trivial) hLocal r hr

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {lead : Nat} (round : Round) (stage : Fin 2)
    (ordinal : Nat)
    (input : ∀ g, SameWarp l lead g →
      OpeningTripCursor l X g (probabilityWaitPc round false)
        (firstPublicationFacts l stage round))
    (hRank : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).pos).countP isTcColl = ordinal)
include hp hMax round stage ordinal input hRank

/-- Aligned reached main-P cursors supply their peer waits from the same maximal trace
and therefore each lane contributes the stage's main packet credit. -/
theorem warpMainProbabilityCreditOfMaximalKeeping :
    ∀ g (hw : SameWarp l lead g),
      let c := input g hw
      let site := signalSite (firstPublication round)
      ∃ u : OpeningTripCursor l X g (site.pc+1) [],
        X.get (g,c.pos) = some ⟨probabilityWaitPc round false,.tc .waitSt⟩ ∧
        Thread.Scores.ProbabilityCredit l X (g,c.pos+1) (g/l.block) stage 0 ∧
        u.pos = c.pos+2 ∧ u.ending = c.ending ∧
        ((X.tr g).take u.pos).countP isTcColl = ordinal+1 ∧
        ∀ r ∉ mainProbabilityCreditWrites round, u.ready.regs r = c.ready.regs r := by
  intro g hw
  let c := input g hw
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hPeers (peer : Nat) (hm : peer ∈ warpLanes l g) : ∃ k, X.TcK (peer,k) ordinal := by
    obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hm
    have hLaneBound := (List.mem_range.mp hLane).trans_le (Nat.min_le_left ..)
    have hSame := (Step.sameWarp_lane hBlock hw.1.2.1 hLaneBound).1
    let hPeer := Step.sameWarp_trans hw hSame
    let w := input (warpLane l g lane) hPeer
    obtain ⟨he,_,_⟩ := mainProbabilityWaitOfMaximal hp hMax hPeer.1.2.1 round w
    exact ⟨w.pos,⟨⟨_,he,rfl⟩,hRank _ hPeer⟩⟩
  obtain ⟨u,hWait,hCredit,hPos,hEnding,hOrdinal,hKeeps⟩ :=
    mainProbabilityCreditOfMaximalKeeping hp hMax hw.1.2.1 round stage c (fun _ => by
      have hHere : ((X.tr g).take c.pos).countP isTcColl = ordinal := hRank g hw
      rw [hHere]
      exact hPeers)
  exact ⟨u,hWait,hCredit,hPos,hEnding,hOrdinal.trans (congrArg (·+1) (hRank g hw)),hKeeps⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
