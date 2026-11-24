-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseSource
import Lemmas.Protocol.UnitNotify

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.AsyncCopy PTX.MBarrier
open Observation (emptyObject readyObject)

private def isUnitRelease (r : Record Ref) : Bool :=
  decide (r.action = .arrive 1 0 ∧ r.fault = none)

private theorem arrivalUnits_eq_count (rs : List (Record Ref))
    (hUnit : ∀ r ∈ rs, ∀ count tx, r.action = .arrive count tx → count = 1 ∧ tx = 0) :
    arrivalUnits rs = rs.countP isUnitRelease := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    have hRest := ih fun s hs => hUnit s (List.mem_cons_of_mem _ hs)
    obtain ⟨_, action, _, fault⟩ := r
    cases action <;> cases fault <;> simp [arrivalUnits, List.countP_cons, isUnitRelease, hRest]
    have h := hUnit _ List.mem_cons_self _ _ rfl
    simp [h, Nat.add_comm]

/-- A delivered notification with its matching ready acquisition on the issuer. -/
structure EmptyReleaseAt (l : Launch) (X : Execution) (loc : Loc) (g k : Nat) where
  record : Record Ref
  atIndex : (X.objects loc)[k]? = some record
  index : Nat
  rank : Fin 16
  form : ReleaseForm
  spec : TcCommit.Spec
  notification : record.id = .async (g, index) (.tcNotify rank)
  issue : ReleaseIssue X g index form spec
  target : TcCommit.target spec rank = some loc
  matched : ReleaseMatch l X g index form loc

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Two records for the same ready acquisition of its issuer identify one notification. -/
theorem EmptyReleaseAt.position_eq_of_wait_eq {loc : Loc} {g k k' : Nat} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (a : EmptyReleaseAt l X loc g k)
    (b : EmptyReleaseAt l X loc g k') (hWait : a.matched.wait = b.matched.wait) : k = k' := by
  have hIndex := a.matched.issue_eq_of_wait_eq hp hX a.issue b.issue b.matched hWait
  have hSpec : a.spec = b.spec := by
    have ha := a.issue
    have hb := b.issue
    unfold ReleaseIssue at ha hb
    rw [hIndex] at ha
    have he := congrArg Event.kind (Option.some.inj (ha.symm.trans hb))
    exact TcKind.commit.inj (Kind.tc.inj he)
  have hRank := MbarRing.Notify.rank_eq a.target (hSpec ▸ b.target)
  have hId : a.record.id = b.record.id := by
    rw [a.notification, b.notification, hIndex, hRank]
  exact ObjectInit.checked_record_index_eq (X.objects_checked hX loc) a.atIndex b.atIndex hId

/-- A unit record on an empty slot identifies the issuer and its paired ready acquisition. -/
theorem emptyReleaseAt (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner k : Nat} {slot : Fin 3} {r : Record Ref}
    (hAt : (X.objects (emptyObject l owner slot))[k]? = some r) (hUnit : r.action = .arrive 1 0) :
    ∃ g, Nonempty (EmptyReleaseAt l X (emptyObject l owner slot) g k) := by
  have hMem := List.mem_of_getElem? hAt
  obtain ⟨g, i, rank, hId⟩ := emptyUpdateSource hp hX hMem (by rw [hUnit]; trivial)
  obtain ⟨form, spec, hIssue, hTarget⟩ := releaseOfEmptyNotification hp hX hMem hId
  obtain ⟨w⟩ := hIssue.matchReady hp hX hTarget
  exact ⟨g, ⟨⟨r, hAt, i, rank, form, spec, hId, hIssue, hTarget, w⟩⟩⟩

/-- The notification targets its own CTA's empty object. -/
theorem EmptyReleaseAt.issuerCta (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner g k : Nat} {slot : Fin 3} (h : EmptyReleaseAt l X (emptyObject l owner slot) g k) :
    owner / l.block = g / l.block :=
  actualCommitTargetOwner hp hX ⟨_, h.issue⟩ h.target

/-- The matching ready acquisition refers to the same physical slot as the empty record. -/
theorem EmptyReleaseAt.matchedSlot {l : Launch} {X : Execution} {owner g k : Nat} {slot : Fin 3}
    (h : EmptyReleaseAt l X (emptyObject l owner slot) g k) : h.matched.slot = slot := by
  have hAddr := congrArg Loc.addr h.matched.target_eq
  change (Prologue.initObject l (owner / l.block) (Loader.emptySlot slot)).addr =
    (Prologue.initObject l (g / l.block) (Loader.emptySlot h.matched.slot)).addr at hAddr
  rw [Loader.emptySlot_address, Loader.emptySlot_address] at hAddr
  simp only at hAddr
  exact Fin.ext (by omega)

/-- The ordinal of the successful ready acquisition returned by a delivered notification. -/
def EmptyReleaseAt.ordinal {l : Launch} {X : Execution} {loc : Loc} {g k : Nat}
    (h : EmptyReleaseAt l X loc g k) : Nat :=
  (atPrefix l X g h.matched.wait).kvAcquires h.matched.slot

/-- On one CTA and slot, the abstract ready ordinal identifies the release issue. -/
theorem EmptyReleaseAt.issue_eq_of_ordinal_eq (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {owner owner' g h k k' : Nat} {slot : Fin 3}
    (a : EmptyReleaseAt l X (emptyObject l owner slot) g k)
    (b : EmptyReleaseAt l X (emptyObject l owner' slot) h k')
    (hCta : owner / l.block = owner' / l.block) (hOrdinal : a.ordinal = b.ordinal) :
    (g, a.index) = (h, b.index) := by
  have hIssuer := a.issue.sameIssuer hp hX b.issue
    ((a.issuerCta hp hX).symm.trans (hCta.trans (b.issuerCta hp hX)))
  subst h
  obtain ⟨⟨pa, ea⟩, ha, hka⟩ := a.matched.ready
  obtain ⟨⟨pb, eb⟩, hb, hkb⟩ := b.matched.ready
  rw [a.matchedSlot] at hka
  rw [b.matchedSlot] at hkb
  dsimp only at hka hkb
  subst ea eb
  simp only [ordinal, a.matchedSlot, b.matchedSlot, atPrefix, kvAcquireCount] at hOrdinal
  have hWait := MbarRing.Poll.okPoll_index_unique ha hb hOrdinal
  exact Prod.ext rfl (a.matched.issue_eq_of_wait_eq hp hX a.issue b.issue b.matched hWait)

/-- A later empty phase cannot reuse an ordinal already assigned to an earlier phase. -/
theorem EmptyReleaseAt.ordinalGeOfPriorExact (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {owner g k phase lower : Nat} {slot : Fin 3}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g k)
    (hPhase : phaseAt (X.objects (emptyObject l owner slot)) k = some phase)
    (hLower : lower ≤ phase)
    (hPrior : ∀ q < lower, ∀ j issuer
      (r : EmptyReleaseAt l X (emptyObject l owner slot) issuer j),
      r.record.fault = none → phaseAt (X.objects (emptyObject l owner slot)) j = some q →
      r.ordinal = q) : lower ≤ release.ordinal := by
  by_contra! hLt
  cases hState : stateBefore (X.objects (emptyObject l owner slot)) k with
  | none => simp [phaseAt, hState] at hPhase
  | some st =>
    have hStage : st.phase = phase := by simpa [phaseAt, hState] using hPhase
    obtain ⟨i, r, hAt, hUnit, hClean, hOld⟩ := emptyUnitOfPriorPhase hp hX release.atIndex hState
      (phase := release.ordinal) (by omega)
    obtain ⟨other, ⟨prior⟩⟩ := emptyReleaseAt hp hX hAt hUnit
    have hOther := release.issue.sameIssuer hp hX prior.issue
      ((release.issuerCta hp hX).symm.trans (prior.issuerCta hp hX))
    subst other
    have hClean' : prior.record.fault = none :=
      Option.some.inj (hAt.symm.trans prior.atIndex) ▸ hClean
    have hCounts := hPrior release.ordinal hLt i g prior hClean' hOld
    have hReads {k : Nat} (w : EmptyReleaseAt l X (emptyObject l owner slot) g k) :
        ∃ e, X.get (g, w.matched.wait) = some e ∧
          e.kind = .wait (readyObject l g slot) w.matched.parity true true .cta := by
      obtain ⟨e, he, hk⟩ := w.matched.ready
      exact ⟨e, he, by rwa [w.matchedSlot] at hk⟩
    obtain ⟨⟨_, kind⟩, ha, haKind⟩ := hReads release
    obtain ⟨⟨_, kind'⟩, hb, hbKind⟩ := hReads prior
    dsimp only at haKind hbKind
    subst kind kind'
    simp only [ordinal, prior.matchedSlot, release.matchedSlot, atPrefix, kvAcquireCount] at hCounts
    have hWait := MbarRing.Poll.okPoll_index_unique ha hb hCounts.symm
    have hPosition := release.position_eq_of_wait_eq hp hX prior hWait
    rw [← hPosition, hPhase] at hOld
    have hEqual := Option.some.inj hOld
    omega

/-- The delivered release units in any prefix of an empty-slot history consume distinct
successful acquisitions of that slot by its elected MMA issuer. -/
theorem emptyUnitsLeReadyAcquires (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g owner j index : Nat} {slot : Fin 3} {form : ReleaseForm} {spec : TcCommit.Spec}
    (anchor : ReleaseIssue X g index form spec) (hCta : owner / l.block = g / l.block) :
    unitsBefore (X.objects (emptyObject l owner slot)) j ≤
      (atPrefix l X g (X.tr g).length).kvAcquires slot := by
  classical
  let loc := emptyObject l owner slot
  let log := X.objects loc
  let ready := readyObject l g slot
  have hReadyObject : ready = Prologue.initObject l (g / l.block) (Loader.readySlot slot) := rfl
  simp only [atPrefix, kvAcquireCount, ← hReadyObject]
  change arrivalUnits (log.take j) ≤ ((X.tr g).take (X.tr g).length).countP (Flow.okPoll ready)
  rw [arrivalUnits_eq_count (log.take j), MbarRing.Slot.countP_take_card,
    MbarRing.Slot.countP_take_card]
  · apply PairTmaRing.card_le_of_rel _ _ (fun k w =>
      ∃ h : EmptyReleaseAt l X loc g k, h.matched.wait = w)
    · intro k hk
      obtain ⟨_, hSome⟩ := Finset.mem_filter.mp hk
      cases hAt : log[k]? with
      | none => simp [hAt] at hSome
      | some r =>
        have hAction : r.action = .arrive 1 0 := by
          simp only [hAt, Option.any_some, isUnitRelease, decide_eq_true_eq] at hSome
          exact hSome.1
        obtain ⟨actor, ⟨h⟩⟩ := emptyReleaseAt hp hX hAt hAction
        have hActor := anchor.sameIssuer hp hX h.issue (hCta.symm.trans (h.issuerCta hp hX))
        subst actor
        let w := h.matched
        have hSlot : w.slot = slot := h.matchedSlot
        obtain ⟨e, he, hKind⟩ := w.ready
        have hLt : w.wait < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
        have hActive : Flow.okPoll ready e = true := by
          simp [Flow.okPoll, hKind, sourceWaitSuccess, ready, hSlot]
        refine ⟨w.wait, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hLt, ?_⟩, ?_⟩
        · change ((X.get (g, w.wait)).any (Flow.okPoll ready)) = true
          simpa only [he, Option.any_some] using hActive
        · exact ⟨h, rfl⟩
    · rintro k _ k' _ w _ ⟨a, ha⟩ ⟨b, hb⟩
      exact a.position_eq_of_wait_eq hp hX b (ha.trans hb.symm)
  · intro r hr count tx hAction
    obtain ⟨_, _, _, _, hUnit⟩ := emptyUpdateArrival hp hX (List.mem_of_mem_take hr)
      (by rw [hAction]; trivial)
    rw [hAction] at hUnit
    exact Action.arrive.inj hUnit

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
