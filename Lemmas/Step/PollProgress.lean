-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Released
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Step.WfInOrder
import Lemmas.Kernel.ProgressDescent
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Step
open PTX.Flow PTX.MBarrier PTX.Assumption

/-- A stopped poll needs readiness only at its starting ordinal. Failed retries
preserve any event count whose marker excludes the failed poll. -/
theorem retrying_poll_at_count_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X)
    {selected : Nat → Bool} (hA : Assumption.WfStep selected L K m A)
    {g site parity : Nat} (hg : g < L.threads) {loc : Loc} {scope : MbarScope}
    {P : TState → Prop} {resume : TState → Bool → TState}
    (hOut : ∀ u, P u → u.pc = site ∧ out K A L g u = .ev (.wait loc parity (resume u) true scope))
    (hRetry : ∀ u, P u → ∃ v, Relation.ReflTransGen (Tau K A L g) (resume u false) v ∧ P v)
    (mark : Event → Bool) (hFail : mark ⟨site,.wait loc parity false true scope⟩ = false)
    (ordinal : Nat) (hReady : (X.tr g).countP mark = ordinal →
      ∀ {t u}, Run K A L g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau K A L g) t u → P u →
      ∃ s, stateBefore (X.objects loc) (X.objects loc).length = some s ∧
        s.phase % 2 ≠ parity % 2)
    {pos : Nat} {t u : TState} {ending : Option TState}
    (hCount : ((X.tr g).take pos).countP mark = ordinal)
    (hPositive : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hReleased : pos = (X.tr g).length → Released L X g)
    (hAt : P u) (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau K A L g) t u) :
    ∃ n v, P v ∧ X.get (g,pos+n) = some ⟨site,.wait loc parity true true scope⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+n+1)) (some (resume v true)) ∧
      Run K A L g (resume v true) ((X.tr g).drop (pos+n+1)) ending ∧
      (X.tr g).drop pos =
        List.replicate n ⟨site,.wait loc parity false true scope⟩ ++
        (⟨site,.wait loc parity true true scope⟩ :: (X.tr g).drop (pos+n+1)) := by
  suffices ∀ fuel, (X.tr g).length-pos = fuel → _ from this _ rfl
  intro fuel hFuel
  induction fuel using Nat.strong_induction_on generalizing pos t u with
  | h fuel ih =>
    obtain ⟨hPc,hTmpl⟩ := hOut u hAt
    have hn : Next K A L g t u (.wait loc parity (resume u) true scope) := ⟨hLocal,hTmpl⟩
    have hMore : pos < (X.tr g).length := by
      by_contra! hNo
      have hEq : pos = (X.tr g).length := Nat.le_antisymm hBound hNo
      have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
      have hFull : Run K A L g {} (X.tr g) (some t) := by
        simpa [hEq] using hPrefix
      obtain ⟨s,hState,hParity⟩ := hReady (by simpa [hEq] using hCount) hFull hLocal hAt
      have hStep : EStep K A L g u ⟨u.pc,.wait loc parity true true scope⟩
          (some (resume u true)) := ⟨_,hTmpl,true,rfl,rfl⟩
      exact hMax.not_grows (poll_counted_extension hMax.1 hg hStarted (hReleased hEq)
        (fun a ha _ _ => hA.quiet hMax.1 (Execution.le_trans le_snoc
          (Execution.le_appendObject ..)) rfl ((Execution.noNewRead_snoc (r := fun _ => none)
            rfl).trans (Execution.noNewRead_of_tr rfl)) a ha)
        hFull hLocal hStep hState hParity)
    have hSkip : (X.tr g).drop pos = (X.tr g)[pos] :: (X.tr g).drop (pos+1) := by
      simpa only [List.drop_drop] using List.drop_eq_getElem_cons hMore
    rw [hSkip] at hTail
    obtain ⟨_,⟨ok,hRead,hRet⟩,hRest⟩ := hn.continuing_event
      (by rintro ⟨_,_,hBad⟩; cases hBad) hTail
    obtain rfl := Option.some.inj hRet
    have he : X.get (g,pos) = some ⟨site,.wait loc parity ok true scope⟩ := by
      change (X.tr g)[pos]? = _
      rw [List.getElem?_eq_getElem hMore,hRead,hPc]
    have hCut := List.take_succ_eq_append_getElem hMore
    rw [hRead] at hCut
    have hPast : Run K A L g {} ((X.tr g).take (pos+1)) (some (resume u ok)) := by
      rw [hCut]
      exact hPrefix.snoc hLocal ⟨_,hTmpl,ok,rfl,rfl⟩
    rw [hRead,hPc] at hSkip
    cases ok with
    | true => exact ⟨0,u,hAt,he,hPast,hRest,hSkip⟩
    | false =>
      obtain ⟨v,hRetry,hPV⟩ := hRetry u hAt
      have hRel (hEnd : pos+1 = (X.tr g).length) : Released L X g := by
        constructor
        intro pc kind hGet _
        have hIdx : (X.tr g).length-1 = pos := by omega
        rw [hIdx] at hGet ⊢
        rw [he] at hGet
        cases hGet
        exact ready_of_wait he
      obtain ⟨n,w,hW,hGet,hPrefix',hRest',hTrace⟩ := ih ((X.tr g).length-(pos+1)) (by omega)
        (pos := pos+1) (by
          rw [hCut,hPc]
          simpa [List.countP_append,hFail] using hCount)
        (by omega) (len_of_get he) hRel hPV hPast hRest hRetry rfl
      have hSum : pos+(n+1) = pos+1+n := by omega
      refine ⟨n+1,w,hW,?_,?_,?_,?_⟩
      · rwa [hSum]
      · rwa [hSum]
      · rwa [hSum]
      · rw [hSum,hSkip,hTrace,List.replicate_succ,List.cons_append]

/-- In a maximal trace a retrying acquire poll succeeds if its final object state would make
it succeed whenever the issuing thread is stopped at that poll. The retry rule describes the
actual local control flow after a failed poll. -/
theorem retrying_poll_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X)
    {selected : Nat → Bool} (hA : Assumption.WfStep selected L K m A)
    {g site parity : Nat} (hg : g < L.threads) {loc : Loc} {scope : MbarScope}
    {P : TState → Prop} {resume : TState → Bool → TState}
    (hOut : ∀ u, P u → u.pc = site ∧ out K A L g u = .ev (.wait loc parity (resume u) true scope))
    (hRetry : ∀ u, P u → ∃ v, Relation.ReflTransGen (Tau K A L g) (resume u false) v ∧ P v)
    (hReady : ∀ {t u}, Run K A L g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau K A L g) t u → P u →
      ∃ s, stateBefore (X.objects loc) (X.objects loc).length = some s ∧
        s.phase % 2 ≠ parity % 2)
    {pos : Nat} {t u : TState} {ending : Option TState}
    (hPositive : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hReleased : pos = (X.tr g).length → Released L X g)
    (hAt : P u) (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau K A L g) t u) :
    ∃ n v, P v ∧ X.get (g,pos+n) = some ⟨site,.wait loc parity true true scope⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+n+1)) (some (resume v true)) ∧
      Run K A L g (resume v true) ((X.tr g).drop (pos+n+1)) ending ∧
      (X.tr g).drop pos =
        List.replicate n ⟨site,.wait loc parity false true scope⟩ ++
        (⟨site,.wait loc parity true true scope⟩ :: (X.tr g).drop (pos+n+1)) :=
  retrying_poll_at_count_of_maximal hMax hA hg hOut hRetry (okPoll loc) rfl _ (fun _ => hReady) rfl
    hPositive hBound hReleased hAt hPrefix hTail hLocal

end PTX.Step
