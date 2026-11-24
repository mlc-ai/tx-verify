-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Issue
public import Lemmas.Flow.ContinuingEvent
import Lemmas.Kernel.ProgressDescent
import Lemmas.Snoc.SnocPendingVisibility

@[expose] public section

namespace PTX.Step
open PTX PTX.Flow PTX.AsyncCopy

/-- An ordinary asynchronous copy issue, group commit, or no-increment arrive-on. -/
def CpAsyncIssueEvent (e : Event) : Prop :=
  (∃ s, e.kind = .copy s ∧ s.generic = true) ∨ e.kind = .asyncCommit ∨
    ∃ loc, e.kind = .asyncArrive loc true

/-- A copy-related instruction with separately recorded effects. -/
def DeferredCopyIssueEvent (e : Event) : Prop :=
  CpAsyncIssueEvent e ∨ ∃ a spec, e.kind = .tensorIssue a spec

/-- A transfer issue or commit with no performed memory effect in its thread event. -/
def DeferredTransferIssueEvent (e : Event) : Prop :=
  DeferredCopyIssueEvent e ∨ (∃ a spec, e.kind = .tensorStore a spec) ∨ e.kind = .bulkCommit

private theorem preserving_issue_counted_extension
    {L : Launch} {K : Kernel} {A : List Assumption} {m : Mem0} {X : Execution}
    (hX : Consistent L K A m X)
    {g : Nat} (hg : g < L.threads) (hReleased : Released L X g)
    {t u : TState} {e : Event} {ending : Option TState}
    (hPrefix : Run K A L g {} (X.tr g) (some t))
    (hSteps : Relation.ReflTransGen (Tau K A L g) t u) (he : EStep K A L g u e ending)
    (hWf : e.kind.WaitFree)
    (hNoShfl : ∀ mode a b c recv ok, e.kind ≠ .shfl mode a b c recv ok)
    (hNoWarpBar : ∀ mask inst, e.kind ≠ .warpBar mask inst)
    (hNoBar : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hNoExit : e.kind ≠ .exit) (hLane : e.kind.laneValue = false)
    (hMat : isMatrix e = false) (hCount : e.counts = true)
    (hNoTc : ∀ k, e.kind ≠ .tc k)
    (hNoArrive : ∀ loc tx count scope, e.kind ≠ .arrive loc tx count true scope)
    (hNoSc : ∀ scope, e.kind ≠ .fence .sc scope)
    (hNoRead : ∀ a bs, e.kind ≠ .rd a bs)
    (hNoWrite : ∀ a bs, e.kind ≠ .wr a bs)
    (hNoRmw : ∀ a old new, e.kind ≠ .rmw a old new)
    (hTma : TmaOk (X.snoc g e (fun _ => none)))
    (hExtra : ExtensionObligations L A (X.snoc g e (fun _ => none)))
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A m Y ∧ X.le Y ∧ X.size L < Y.size L := by
  refine ⟨_,consistent_snoc_preserving_present hX hg hPrefix hSteps he hNoShfl
    (fun h => by rw [hMat] at h; cases h) hReleased.ready
    (snoc_new_ready hWf hNoShfl hLane hMat)
    (fun _ _ _ h => (snoc_memReads_control hX.effectValidity hNoTc hNoRead hNoRmw).mp h)
    (fun _ _ _ => snoc_memWrites_control hX.effectValidity hNoWrite hNoRmw) ?_
    (snoc_plain_orderOk hX hWf hNoShfl hNoExit hLane hMat hNoArrive
      (fun a old new h => (hNoRmw a old new h).elim)) hasm hTma hExtra,le_snoc,?_⟩
  · intro _ _ _ hSrc hDst
    exact snoc_modelCausality_old_effects hX.effectValidity hNoTc
      (baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf)
        hNoWarpBar hNoBar hNoArrive hNoSc)
      (snoc_allocResultBefore_old hX.dependency.ready)
      (refPresent_issuer_lt hX.effectValidity hSrc) (refPresent_issuer_lt hX.effectValidity hDst)
  · rw [size_snoc hX hg hCount]
    omega

local macro "distinct_event" : tactic => `(tactic| (intros; intro h; cases h))

/-- A transfer issue or commit is recorded before its independent effects. -/
theorem deferred_transfer_issue_counted_extension {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {g : Nat} (hg : g < L.threads) (hStarted : X.tr g ≠ []) (hReleased : Released L X g)
    {t u : TState} {e : Event} {ending : Option TState}
    (hPrefix : Run K A L g {} (X.tr g) (some t))
    (hSteps : Relation.ReflTransGen (Tau K A L g) t u) (he : EStep K A L g u e ending)
    (hKind : DeferredTransferIssueEvent e)
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A m Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨site,kind⟩ := e
  rcases hKind with ((⟨spec,rfl,_⟩ | rfl | ⟨loc,rfl⟩) | ⟨a,spec,rfl⟩) | ⟨a,spec,rfl⟩ | rfl
  all_goals
    refine preserving_issue_counted_extension hX hg hReleased hPrefix hSteps he
      (Kind.WaitFree.mk trivial (fun _ h => by cases h))
      (by distinct_event) (by distinct_event) (by distinct_event) (by distinct_event)
      rfl rfl rfl
      (by distinct_event) (by distinct_event) (by distinct_event)
      (by distinct_event) (by distinct_event) (by distinct_event) ?_ ?_ hasm
    · exact hX.tmaOk_snoc_unobserved (by distinct_event)
        (objectAction_snoc_new (by distinct_event) (by distinct_event)
          (by distinct_event) (by distinct_event)
          (fun _ h => by cases h))
    · refine ExtensionObligations.snoc_frame_of hX (by distinct_event)
        (by distinct_event) (by distinct_event)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact ClcOk.snoc hX.clc (.inl hStarted) (by distinct_event)
      · exact hX.tmemPairResult.snoc_not_wr (by distinct_event)
      · exact hX.tcRead_snoc (by distinct_event) (by distinct_event) (by distinct_event)
          (by distinct_event) (by distinct_event)
      · exact hX.atomic.snoc hX.store hX.tma.1 (by distinct_event)
      · exact hX.fenceSc_snoc (by distinct_event) (by distinct_event)
          (by distinct_event) (by distinct_event)
      · exact hX.matrix.snoc rfl
      · exact TensorStore.ReduceOk.snoc_issue hX

/-- A deferred copy issue adds a thread event before recording any independent effects. -/
theorem deferred_copy_issue_counted_extension {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {g : Nat} (hg : g < L.threads) (hStarted : X.tr g ≠ []) (hReleased : Released L X g)
    {t u : TState} {e : Event} {ending : Option TState}
    (hPrefix : Run K A L g {} (X.tr g) (some t))
    (hSteps : Relation.ReflTransGen (Tau K A L g) t u) (he : EStep K A L g u e ending)
    (hKind : DeferredCopyIssueEvent e)
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A m Y ∧ X.le Y ∧ X.size L < Y.size L :=
  deferred_transfer_issue_counted_extension hX hg hStarted hReleased hPrefix hSteps he
    (.inl hKind) hasm

/-- The issue of a cp.async operation adds only a thread event.
The copy's read, write, and arrive-on delivery are separate operations. -/
theorem cp_async_issue_counted_extension {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {g : Nat} (hg : g < L.threads) (hStarted : X.tr g ≠ []) (hReleased : Released L X g)
    {t u : TState} {e : Event} {ending : Option TState}
    (hPrefix : Run K A L g {} (X.tr g) (some t))
    (hSteps : Relation.ReflTransGen (Tau K A L g) t u) (he : EStep K A L g u e ending)
    (hKind : CpAsyncIssueEvent e)
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A m Y ∧ X.le Y ∧ X.size L < Y.size L :=
  deferred_copy_issue_counted_extension hX hg hStarted hReleased hPrefix hSteps he
    (.inl hKind) hasm

/-- A maximal cursor records its transfer issue or commit and the actual continuation. -/
theorem deferred_transfer_issue_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X) {g pos : Nat} (hg : g < L.threads)
    {t u dst : TState} {ending : Option TState} {tmpl : Tmpl} {kind : Kind}
    (hn : Next K A L g t u tmpl)
    (hFire : ∀ e ret, Fires u.pc tmpl e ret ↔ e = ⟨u.pc,kind⟩ ∧ ret = some dst)
    (hKind : DeferredTransferIssueEvent ⟨u.pc,kind⟩)
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Released L X g)
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g ⟨u.pc,kind⟩ (fun _ => none))) :
    X.get (g,pos) = some ⟨u.pc,kind⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some dst) ∧
      Run K A L g dst ((X.tr g).drop (pos+1)) ending := by
  let event : Event := ⟨u.pc,kind⟩
  have he : EStep K A L g u event (some dst) :=
    ⟨tmpl,hn.stop,(hFire ..).mpr ⟨rfl,rfl⟩⟩
  have hMore : pos < (X.tr g).length := by
    by_contra! hNo
    have hEq := Nat.le_antisymm hBound hNo
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
    rw [List.take_of_length_le hNo] at hPrefix
    exact hMax.not_grows (deferred_transfer_issue_counted_extension hMax.1 hg hStarted
      (hRelease hEq) hPrefix hn.steps he hKind hasm)
  rw [List.drop_eq_getElem_cons hMore] at hTail
  obtain ⟨_,hFired,hRest⟩ := hn.continuing_event
    (by
      intro h
      have hFalse := ((hFire ..).mp h).2
      cases hFalse) hTail
  obtain ⟨hRead,hEq⟩ := (hFire ..).mp hFired
  obtain rfl := Option.some.inj hEq
  have hGet : X.get (g,pos) = some event := by
    change (X.tr g)[pos]? = _
    rw [List.getElem?_eq_getElem hMore,hRead]
  refine ⟨hGet,?_,hRest⟩
  rw [List.take_succ_eq_append_getElem hMore,hRead]
  exact hPrefix.snoc hn.steps he

/-- A live maximal cursor records its deferred copy issue and the actual continuation. -/
theorem deferred_copy_issue_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X) {g pos : Nat} (hg : g < L.threads)
    {t u dst : TState} {ending : Option TState} {tmpl : Tmpl} {kind : Kind}
    (hn : Next K A L g t u tmpl)
    (hFire : ∀ e ret, Fires u.pc tmpl e ret ↔ e = ⟨u.pc,kind⟩ ∧ ret = some dst)
    (hKind : DeferredCopyIssueEvent ⟨u.pc,kind⟩)
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Released L X g)
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g ⟨u.pc,kind⟩ (fun _ => none))) :
    X.get (g,pos) = some ⟨u.pc,kind⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some dst) ∧
      Run K A L g dst ((X.tr g).drop (pos+1)) ending :=
  deferred_transfer_issue_of_maximal hMax hg hn hFire (.inl hKind) hPrefix hTail hPos
    hBound hRelease hasm

/-- A live maximal cursor records its deterministic cp.async issue and the actual continuation. -/
theorem cp_async_issue_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X) {g pos : Nat} (hg : g < L.threads)
    {t u dst : TState} {ending : Option TState} {tmpl : Tmpl} {kind : Kind}
    (hn : Next K A L g t u tmpl)
    (hFire : ∀ e ret, Fires u.pc tmpl e ret ↔ e = ⟨u.pc,kind⟩ ∧ ret = some dst)
    (hKind : CpAsyncIssueEvent ⟨u.pc,kind⟩)
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Released L X g)
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g ⟨u.pc,kind⟩ (fun _ => none))) :
    X.get (g,pos) = some ⟨u.pc,kind⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some dst) ∧
      Run K A L g dst ((X.tr g).drop (pos+1)) ending :=
  deferred_copy_issue_of_maximal hMax hg hn hFire (.inl hKind) hPrefix hTail hPos hBound
    hRelease hasm

end PTX.Step
