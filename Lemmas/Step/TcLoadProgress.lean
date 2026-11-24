-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.TcLoad
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Step
open PTX.Flow TcMma

/-- In a maximal execution, an enabled Tensor Memory load occurs in the recorded
suffix if every last writer leaves a whole word. The callback records the returned words. -/
theorem tcLoadOfMaximal {K : Kernel} {A : List Assumption} {L : Launch} {m : Mem0}
    {X : Execution} {g pos address count : Nat} {sh : TcShape}
    {before ready : TState} {ending : Option TState} {resume : List Value → TState}
    (hMax : Maximal L K A m X) (hGuard : SyncGuarded L K X) (hLayout : LayoutInjective X)
    (hg : g < L.threads) (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hReleased : pos = (X.tr g).length → Released L X g)
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some before))
    (hSuffix : Run K A L g before ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau K A L g) before ready)
    (hOut : out K A L g ready = .ev (.tcLd address count sh resume))
    (hWords : ∀ j < count, ∀ v, LastWrote L A X (tcDataCell L g sh address j) v → v.bytes = 4)
    (hAsm : ∀ a ∈ A, a.wf L m
      (X.snoc g ⟨ready.pc,.tc (.ld address (loadVals L A X g sh address count) sh)⟩
        (fun _ => none))) :
    ∃ words, words.length = count ∧
      X.get (g,pos) = some ⟨ready.pc,.tc (.ld address words sh)⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some (resume words)) ∧
      Run K A L g (resume words) ((X.tr g).drop (pos+1)) ending := by
  have hMore : pos < (X.tr g).length := by
    by_contra! hStop
    have hEnd := Nat.le_antisymm hBound hStop
    have hNonempty := List.ne_nil_of_length_pos (hPos.trans_le hBound)
    have hFull : Run K A L g {} (X.tr g) (some before) := by
      simpa only [hEnd,List.take_length] using hPrefix
    let words := loadVals L A X g sh address count
    have hStep : EStep K A L g ready
        ⟨ready.pc,.tc (.ld address words sh)⟩ (some (resume words)) :=
      ⟨_,hOut,words,loadVals_length,rfl,rfl⟩
    exact hMax.not_grows (tc_load_counted_extension hMax.1 hg hNonempty (hReleased hEnd)
      hFull hLocal hStep (fun j v hj hLast => by
        rw [loadVals_length] at hj
        exact ⟨loadVals_spec hMax.1 hGuard hLayout hj hLast,hWords j hj v hLast⟩) hAsm)
  have hNext : Next K A L g before ready (.tcLd address count sh resume) := ⟨hLocal,hOut⟩
  have hMoreEvents : (X.tr g).drop pos ≠ [] := by
    intro hNil
    exact Nat.not_le_of_lt hMore (List.drop_eq_nil_iff.mp hNil)
  obtain ⟨event,events,hDrop⟩ := List.exists_cons_of_ne_nil hMoreEvents
  have hGet : X.get (g,pos) = some event := by
    change (X.tr g)[pos]? = some event
    rw [show (X.tr g)[pos]? = ((X.tr g).drop pos)[0]? by simp,hDrop]
    rfl
  have hTail : (X.tr g).drop (pos+1) = events := by
    rw [← List.drop_drop,hDrop]
    rfl
  rw [hDrop] at hSuffix
  obtain ⟨u,⟨words,hLen,hEvent,hResume⟩,hRest⟩ :=
    hNext.continuing_event (by rintro ⟨_,_,_,hBad⟩; cases hBad) hSuffix
  subst event
  rw [← hTail] at hRest
  obtain rfl := Option.some.inj hResume
  have hStep : EStep K A L g ready
      ⟨ready.pc,.tc (.ld address words sh)⟩ (some (resume words)) :=
    ⟨_,hOut,words,hLen,rfl,rfl⟩
  have hPast : Run K A L g {} ((X.tr g).take (pos+1)) (some (resume words)) := by
    rw [List.take_succ_eq_append_getElem hMore,(List.getElem?_eq_some_iff.mp hGet).2]
    exact hPrefix.snoc hLocal hStep
  exact ⟨words,hLen,hGet,hPast,hRest⟩

/-- A Tensor Memory data collective at the end of the trace is released
when all warp lanes have recorded that ordinal. -/
theorem releasedOfTcOrdinal {L : Launch} {X : Execution} {g pos ordinal site : Nat}
    {kind : TcKind} (he : X.get (g,pos) = some ⟨site,.tc kind⟩)
    (hNeeds : KindNeeds L X (.tc kind) (g,pos) = tcNeeds L X (g,pos))
    (hRank : ((X.tr g).take pos).countP isTcColl = ordinal)
    (hPeers : ∀ peer ∈ warpLanes L g, ∃ k, X.TcK (peer,k) ordinal)
    (hLast : pos+1 = (X.tr g).length) : Released L X g := by
  constructor
  intro pc actual hGet _
  have hIndex : (X.tr g).length-1 = pos := by omega
  rw [hIndex,he,Option.some.injEq] at hGet
  cases hGet
  rw [hIndex]
  intro need hNeed
  simp only [Needs,he,hNeeds,tcNeeds,hRank] at hNeed
  obtain ⟨peer,hPeer,rfl⟩ := List.mem_map.mp hNeed
  obtain ⟨k,hK⟩ := hPeers peer hPeer
  obtain ⟨event,hEvent,_⟩ := hK.1
  exact ⟨.thread (peer,k),⟨event,hEvent⟩,k,rfl,hK⟩

end PTX.Step
