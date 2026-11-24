-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.TcLoad
public import Lemmas.Flow.ContinuingEvent
import Lemmas.Snoc.SnocPendingVisibility
import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Step
open PTX PTX.Flow PTX.AsyncCopy

private theorem tc_issue_counted_extension {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {g : Nat} (hg : g < L.threads) (hStarted : X.tr g ≠ []) (hReleased : Released L X g)
    {t u : TState} {event : Event} {ending : Option TState} {site : Nat} {kind : TcKind}
    (hKind : event = ⟨site,.tc kind⟩) (hOrdinary : isTcColl event = false)
    (hPrefix : Run K A L g {} (X.tr g) (some t))
    (hSteps : Relation.ReflTransGen (Tau K A L g) t u) (he : EStep K A L g u event ending)
    (hasm : ∀ a ∈ A, a.wf L m (X.snoc g event (fun _ => none))) :
    ∃ Y, Consistent L K A m Y ∧ X.le Y ∧ X.size L < Y.size L := by
  subst event
  let e : Event := ⟨site,.tc kind⟩
  let Y := X.snoc g e (fun _ => none)
  have hNotLoad : ∀ pc a vals sh, e ≠ ⟨pc,.tc (.ld a vals sh)⟩ := by
    intro pc a vals sh h
    change isTcColl e = false at hOrdinary
    rw [h] at hOrdinary
    cases hOrdinary
  have hExtra : ExtensionObligations L A Y :=
    ExtensionObligations.snoc_frame hX nofun nofun nofun (ClcOk.snoc hX.clc (.inl hStarted) nofun)
      (hX.tmemPairResult.snoc_not_wr (by intros; simp [e]))
      (hX.tcRead_snoc nofun nofun nofun nofun hNotLoad)
      (hX.atomic.snoc hX.store hX.tma.1 nofun) (hX.fenceSc_snoc nofun nofun nofun nofun)
      (hX.matrix.snoc rfl) (fun _ h => Kind.noConfusion h)
  have hTma : TmaOk Y := tmaOk_snoc_tc hX.tma hX.tcCommit rfl
  have hFrame := snoc_noncollective_sinkFrame (g := g) (r := fun _ => none)
    hX hg (e := e) rfl hOrdinary
  have hBase {a b : EvId} (hb : b.2 < (X.tr b.1).length) :
      baseCausality L Y a b ↔ baseCausality L X a b := by
    refine ⟨baseCausality_snocHistory_ordinary hX SnocRecords.same ?_ a b hb,?_⟩
    · simp [e,Kind.Ordinary]
    · exact baseCausality_snoc
  refine ⟨Y,consistent_snoc_preserving_present hX hg hPrefix hSteps he nofun
    (fun h => by cases h) hReleased.ready
    (fun h => (not_returned_new_of_noncollective rfl hOrdinary h).elim)
    (fun _ _ _ h => (TcIssue.snoc_memReads rfl hX.tma).mp h)
    (fun _ _ _ => snoc_memWrites_control hX.effectValidity (by intros; simp [e])
      (by intros; simp [e]))
    ?_ (hFrame.orderOk hX.orderOk) hasm hTma hExtra,le_snoc,?_⟩
  · intro _ _ _ hSrc hDst
    exact snoc_modelCausality_retained_effects hX.effectValidity
      (TcIssue.snoc_asyncPresent hX.tma.2.1).mp hBase
      (snoc_allocResultBefore_old hX.dependency.ready)
      (refPresent_issuer_lt hX.effectValidity hSrc) (refPresent_issuer_lt hX.effectValidity hDst)
  · unfold Y e
    rw [size_snoc hX hg rfl]
    omega

/-- A released noncollective tensor-core issue must be recorded by a maximal prefix. Its
effects are delivered separately, so issuing it preserves all existing observations. -/
theorem tc_issue_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X)
    {g pos : Nat} (hg : g < L.threads)
    {t u dst : TState} {ending : Option TState} {kind : TcKind}
    (hn : Next K A L g t u (.tc kind dst)) (hOrdinary : isTcColl ⟨u.pc,.tc kind⟩ = false)
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Released L X g)
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g ⟨u.pc,.tc kind⟩ (fun _ => none))) :
    X.get (g,pos) = some ⟨u.pc,.tc kind⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some dst) ∧
      Run K A L g dst ((X.tr g).drop (pos+1)) ending := by
  let event : Event := ⟨u.pc,.tc kind⟩
  have he : EStep K A L g u event (some dst) := ⟨_,hn.stop,rfl,rfl⟩
  have hMore : pos < (X.tr g).length := by
    by_contra! hNo
    have hEq := Nat.le_antisymm hBound hNo
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
    rw [List.take_of_length_le hNo] at hPrefix
    exact hMax.not_grows (tc_issue_counted_extension hMax.1 hg hStarted (hRelease hEq)
      rfl hOrdinary hPrefix hn.steps he hasm)
  rw [List.drop_eq_getElem_cons hMore] at hTail
  obtain ⟨_,⟨hKind,hDst⟩,hRest⟩ := hn.continuing_event (by rintro ⟨_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hDst
  have hGet : X.get (g,pos) = some event := by
    change (X.tr g)[pos]? = _
    rw [List.getElem?_eq_getElem hMore,hKind]
  refine ⟨hGet,?_,hRest⟩
  rw [List.take_succ_eq_append_getElem hMore,hKind]
  exact hPrefix.snoc hn.steps he

end PTX.Step
