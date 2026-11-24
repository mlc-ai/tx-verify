-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncOrder
public import Lemmas.Snoc.Snoc
public import Lemmas.Execution.EffectValidity
public import Lemmas.Tmem.TmemPairHistory

@[expose] public section

/-! Every waiting node has an actual instruction/effect origin. These facts are derived
from object provenance and completion rules, not additional execution restrictions. -/
namespace PTX
noncomputable section
open AsyncCopy
section
variable {L : Launch} {X : Execution}

/-- Every footprint of a stage of an asynchronous operation has an actual issuing instruction,
whether or not the stage is present: the footprint is fixed at issue. -/
private theorem footprint_issuer {i : EvId} {p : Part} {a : Acc}
    (h : X.AsyncFootprint i p a) : X.RefPresent (.thread i) := by
  cases p with
  | mmaRead isB index =>
    obtain ⟨-, h⟩ := h
    rcases h with ⟨_, _, _, _, ⟨pc, hi⟩, _⟩ | ⟨_, _, _, ⟨pc, hi⟩, _, _, _⟩
    · exact ⟨_, hi⟩
    · exact ⟨_, hi⟩
  | readLoad x y k | readStore x y k | writeLoad x y k | writeStore x y k =>
    obtain ⟨_, _, ⟨pc, hi⟩, _, _⟩ := h; exact ⟨_, hi⟩
  | readPrefetch x y k | writeCta c =>
    obtain ⟨_, _, ⟨pc, hi⟩, _, _⟩ := h; exact ⟨_, hi⟩
  | writeCopy => obtain ⟨_, ⟨pc, hi⟩, _, _⟩ := h; exact ⟨_, hi⟩
  | writeElem j => obtain ⟨_, ⟨pc, hi⟩, _⟩ := h; exact ⟨_, hi⟩
  | oldStore x y k => obtain ⟨_, _, ⟨pc, hi⟩, _, _, _⟩ := h; exact ⟨_, hi⟩
  | oldElem j => obtain ⟨_, _, ⟨pc, hi⟩, _, _⟩ := h; exact ⟨_, hi⟩
  | readCopy =>
    rcases h with ⟨_, ⟨pc, hi⟩, _⟩ | ⟨pc, hi⟩
    · exact ⟨_, hi⟩
    · exact ⟨_, hi⟩
  | writePrefetch x y k | oldPrefetch x y k | readCta | readElem j | oldCopy =>
    exact h.elim
  | oldLoad x y k | oldCta c | notifyCopy | notifyLoad | notifyCta c => exact h.elim
  | readsDone | fullDone | resolve | tcNotify r | mmaDone | arriveOn => exact h.elim

/-- Even a pending access intent has a concrete issuing instruction. -/
theorem intent_issuer {e : Ref} {a : Acc} {w : Bool} (he : X.Intent e a w) :
    X.RefPresent (.thread e.issuer) := by
  cases e with
  | thread i =>
    simp only [Execution.Intent, Execution.Access] at he
    rcases he with ⟨bs, ⟨pc, hi⟩, _⟩ | ⟨bs, ⟨pc, hi⟩, _⟩ | ⟨o, n, ⟨pc, hi⟩⟩
    all_goals exact ⟨_, hi⟩
  | async i p =>
    obtain ⟨-, hf⟩ := he
    exact footprint_issuer hf

/-- A footprint, including a pending effect, has an actual issuing event. -/
theorem AsyncCovers.issuer_lt {i : EvId} {p : Part} {l : Loc}
    (hc : AsyncCovers X i p l) : i.2 < (X.tr i.1).length := by
  obtain ⟨a,w,hi,_⟩ := hc
  obtain ⟨e,he⟩ := intent_issuer hi
  exact len_of_get he

theorem asyncPresent_source (hv : EffectValidity L X) {i : EvId} {p : Part}
    (hp : X.AsyncPresent i p) : ∃ ev, X.get i = some ev ∧ ev.kind.isTma = true := by
  have ht := hv.tma
  have copyOrigin (hn : nonempty (X.async.copies i)) :
      ∃ ev, X.get i = some ev ∧ ev.kind.isTma = true := by
    obtain ⟨s, hs, _⟩ := ht.1 i hn
    cases hg : X.get i with
    | none => simp [issuedBy, hg] at hs
    | some ev =>
      refine ⟨ev, rfl, ?_⟩
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp_all [issuedBy, Kind.isTma]
  have mmaOrigin (hs : X.async.mmaStarted i = true) :
      ∃ ev, X.get i = some ev ∧ ev.kind.isTma = true := by
    rcases ht.2.1.1 i hs with
      ⟨d, spec, accum, mask, operands, ⟨pc, hm⟩, _⟩ | ⟨c, operands, ⟨pc, hm⟩, _⟩ |
      ⟨s, operands, ⟨pc, hm⟩, _⟩ <;> exact ⟨_, hm, rfl⟩
  have tensorOrigin {o : TensorCopy.Observation} (ho : X.tensor i = some o) :
      ∃ ev, X.get i = some ev ∧ ev.kind.isTma = true := by
    obtain ⟨addr, pc, hi⟩ := (hv.tensor i o ho).1
    exact ⟨_, hi, rfl⟩
  have storeOrigin {o : TensorStore.Observation} (ho : X.tensorStores i = some o) :
      ∃ ev, X.get i = some ev ∧ ev.kind.isTma = true := by
    obtain ⟨addr, pc, hi⟩ := (hv.store i o ho).1
    exact ⟨_, hi, rfl⟩
  have clcOrigin (hn : (X.clc i).resolved.isSome ∨ (X.clc i).written.Nonempty ∨
      (X.clc i).notified.Nonempty) : ∃ ev, X.get i = some ev ∧ ev.kind.isTma = true := by
    obtain ⟨s, targets, pc, hi⟩ := hv.clc.2.2.1 i hn
    exact ⟨_, hi, rfl⟩
  cases p with
  | readCopy => exact copyOrigin ⟨.read .copy, hp⟩
  | writeCopy => exact copyOrigin ⟨.write .copy, hp⟩
  | notifyCopy => exact copyOrigin ⟨.notify .copy, hp⟩
  | writeElem j => exact copyOrigin ⟨.write (.elem j), hp⟩
  | oldElem j => exact copyOrigin ⟨.old (.elem j), hp⟩
  | mmaDone => exact mmaOrigin (ht.2.1.2 i hp)
  | readLoad x y k | notifyLoad => obtain ⟨o, ho, _⟩ := hp; exact tensorOrigin ho
  | writeLoad x y k => obtain ⟨o, slot, value, ho, _⟩ := hp; exact tensorOrigin ho
  | readStore x y k | writeStore x y k | oldStore x y k | readsDone | fullDone =>
    obtain ⟨o, ho, _⟩ := hp; exact storeOrigin ho
  | readCta | readElem j | oldCopy | oldLoad | oldCta | readPrefetch | writePrefetch |
      oldPrefetch => exact hp.elim
  | resolve => exact clcOrigin (.inl hp)
  | writeCta c => exact clcOrigin (.inr (.inl ⟨c, hp⟩))
  | notifyCta c => exact clcOrigin (.inr (.inr ⟨c, hp⟩))
  | tcNotify r =>
    obtain ⟨⟨s, m, ⟨pc, hi⟩, _⟩, _⟩ := hv.tcCommit i r hp
    exact ⟨_, hi, rfl⟩
  | mmaRead b k =>
    obtain ⟨l, byte, hf, -⟩ := hp
    rcases hf with ⟨_, _, _, _, ⟨pc, hm⟩, _⟩ | ⟨_, _, _, ⟨pc, hm⟩, _, _, _, _⟩
    · exact ⟨_, hm, rfl⟩
    · exact ⟨_, hm, rfl⟩
  | arriveOn =>
    obtain ⟨⟨m, noinc, pc, hi⟩, _⟩ := ht.2.2.2 i hp
    exact ⟨_, hi, rfl⟩

theorem asyncPresent_issuer (hv : EffectValidity L X) {i : EvId} {p : Part}
    (hp : X.AsyncPresent i p) : X.RefPresent (.thread i) := by
  obtain ⟨ev, he, _⟩ := asyncPresent_source hv hp
  exact ⟨ev, he⟩

theorem objectAction_present {m : Loc} {e : Ref} {a : MBarrier.Action}
    (h : objectAction X X.async m e = some a) : X.RefPresent e := by
  cases e with
  | thread i =>
    cases hg : X.get i with
    | none => simp [objectAction, hg] at h
    | some ev => exact ⟨ev, hg⟩
  | async i p =>
    cases p <;> simp only [objectAction, reduceCtorEq] at h
    case notifyCopy =>
      cases hs : issuedBy X i with
      | none => simp [hs] at h
      | some spec =>
        simp only [hs, bind, Option.bind] at h
        split_ifs at h with hn
        exact hn.2
    case notifyLoad =>
      cases hg : X.get i with
      | none => simp [hg] at h
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [hg, bind, Option.bind, reduceCtorEq] at h
        case tensorIssue address spec =>
          cases ho : X.tensor i with
          | none => simp [ho] at h
          | some o =>
            simp only [ho] at h
            split_ifs at h with hn
            exact ⟨o, ho, hn.2⟩
    case tcNotify rank =>
      cases hg : X.get i with
      | none => simp [hg] at h
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [hg, reduceCtorEq] at h
        case tc tc =>
          cases tc <;> simp only [reduceCtorEq] at h
          split_ifs at h with hn
          exact hn.2
    case notifyCta c =>
      cases hg : X.get i with
      | none => simp [hg] at h
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [hg, reduceCtorEq] at h
        case clcIssue spec targets =>
          split_ifs at h with hn
          exact hn.2.1
    case arriveOn =>
      cases hg : X.get i with
      | none => simp [hg] at h
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [hg, reduceCtorEq] at h
        case asyncArrive m' noinc =>
          split_ifs at h with hn
          exact hn.2

theorem objectAction_thread_not_access {m : Loc} {e : EvId} {a : MBarrier.Action}
    (h : objectAction X X.async m (.thread e) = some a) : (X.get e).bind Event.acc = none := by
  cases hg : X.get e with
  | none => simp [objectAction, hg] at h
  | some ev =>
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> simp_all [objectAction, Event.acc]

/-- The history cannot mention a synthetic thread or an unperformed notification. -/
theorem object_record_present (ht : TmaOk X) {m : Loc} {rec : MBarrier.Record Ref}
    (hr : rec ∈ X.objects m) : X.RefPresent rec.id :=
  objectAction_present ((ht.2.2.1 m).2.1 rec hr).1

/-- A thread event of an object's history is an mbarrier operation. -/
theorem object_record_not_access (ht : TmaOk X) {m : Loc} {rec : MBarrier.Record Ref}
    (hr : rec ∈ X.objects m) {e : EvId} (hid : rec.id = .thread e) :
    (X.get e).bind Event.acc = none := by
  have h := ((ht.2.2.1 m).2.1 rec hr).1
  rw [hid] at h
  exact objectAction_thread_not_access h

/-- Every thread event of one side of an ordering edge exists. -/
private theorem memWrites_present {e : EvId} {a : Acc} {bs : List Byte}
    (h : X.MemWrites (.thread e) a bs) : X.RefPresent (.thread e) := by
  rcases h with ⟨pc, hi⟩ | ⟨old, pc, hi⟩
  · exact ⟨_, hi⟩
  · exact ⟨_, hi⟩

/-- Every thread event of one side of an ordering edge exists. -/
private theorem memReads_present {e : EvId} {a : Acc} {bs : List (Option Byte)}
    (h : X.MemReads (.thread e) a bs) : X.RefPresent (.thread e) := by
  rcases h with ⟨pc, hi⟩ | ⟨new, pc, hi⟩
  · exact ⟨_, hi⟩
  · exact ⟨_, hi⟩

/-- Both ends of a stage edge are the present stages of their operations. -/
private theorem stageEdge_present {e f : Ref} (h : StageEdge X e f) :
    X.RefPresent e ∧ X.RefPresent f := by
  have stages : ∀ {p q : Part} {i j : EvId}, StageEdge X (.async i p) (.async j q) →
      X.RefPresent (.async i p) ∧ X.RefPresent (.async j q) := by
    intro p q i j h
    cases p <;> cases q <;> simp only [StageEdge] at h
    all_goals first
      | exact ⟨h.2.2.1, h.2.2.2⟩
      | exact ⟨h.2.1, h.2.2⟩
  cases e with
  | thread i =>
    cases f with
    | thread j => simp only [StageEdge] at h
    | async j q => simp only [StageEdge] at h
  | async i p =>
    cases f with
    | thread j => simp only [StageEdge] at h
    | async j q => exact stages h

/-- Both ends of a fence synchronization are events of their threads. -/
private theorem fenceSync_present {e f : EvId} (h : FenceSync L X e f) :
    X.RefPresent (.thread e) ∧ X.RefPresent (.thread f) := by
  have event {r : EvId} {k : Kind} (h : ∃ pc, X.get r = some ⟨pc, k⟩) :
      X.RefPresent (.thread r) := by
    obtain ⟨pc, hg⟩ := h
    exact ⟨_, hg⟩
  have readEvent {r : EvId} {b : Acc} {cs : List (Option Byte)} (h : X.Reads r b cs) :
      X.RefPresent (.thread r) := event h
  have rmwEvent {r : EvId} {b : Acc} {cs : List (Option Byte)} {n : Option (List Byte)}
      (h : X.Rmw r b cs n) : X.RefPresent (.thread r) := event h
  have fenceEvent {r : EvId} {sem : FenceSem} {s : MbarScope} (h : X.ThreadFence r sem s) :
      X.RefPresent (.thread r) := event h
  have strongRead {r : EvId} {b : Acc} {cs : List (Option Byte)}
      (h : StrongRead X r b cs) : X.RefPresent (.thread r) := by
    rcases h with h | h
    · exact readEvent h.1
    · obtain ⟨n, hr, -⟩ := h; exact rmwEvent hr
  have head {w : EvId} {a : Acc} {bs : List Byte} {se : MbarScope}
      (hw : X.MemWrites (.thread w) a bs) (h : ReleaseHead X e w a se) :
      X.RefPresent (.thread e) := by
    rcases h with h | h
    · rw [h.1]; exact memWrites_present hw
    · obtain ⟨sem, hf, _, _, _⟩ := h; exact fenceEvent hf
  have tail {r : EvId} {b : Acc} {cs : List (Option Byte)} {sf : MbarScope}
      (hr : StrongRead X r b cs) (h : AcquireTail X r f b sf) :
      X.RefPresent (.thread f) := by
    rcases h with h | h
    · rw [h.1]; exact strongRead hr
    · obtain ⟨sem, hf, _, _, _⟩ := h; exact fenceEvent hf
  rcases h with h | h
  · obtain ⟨w, r, a, b, bs, cs, se, sf, hw, -, hsr, hrel, hacq, -⟩ := h
    exact ⟨head hw hrel, tail hsr hacq⟩
  · obtain ⟨hsc, -⟩ := h
    obtain ⟨s, s', he, hf, -⟩ := hsc
    exact ⟨fenceEvent he, fenceEvent hf⟩

/-- A witness of an event's return is an event of the thread that needs it. -/
private theorem witness_present {x : Ref} {j : EvId} (h : Witness L X x j) :
    X.RefPresent (.thread j) := by
  obtain ⟨fills, hn, _, _⟩ := h
  cases hg : X.get j with
  | none => simp [Needs, hg] at hn
  | some ev => exact ⟨ev, hg⟩

/-- All sources and targets of a dependency exist, including asynchronous/object nodes. -/
theorem waits_present (hv : EffectValidity L X) {v w : Ref × Bool} (h : Waits L X v w) :
    X.RefPresent v.1 ∧ X.RefPresent w.1 := by
  have atIndex {i : EvId} (hi : i.2 < (X.tr i.1).length) : X.RefPresent (.thread i) :=
    ⟨(X.tr i.1)[i.2], List.getElem?_eq_getElem hi⟩
  have pairMember {w : Tmem.Pair.WarpRequest} {group : CtaGroup} (hw : w.Valid L X group)
      {e : EvId} (he : Tmem.Pair.Participates L w e) : X.RefPresent (.thread e) := by
    obtain ⟨lane, rfl⟩ := he
    exact ⟨_, hw.2.2.1 lane⟩
  have regRequest {e f : EvId} (h : SetMaxNReg.SameRequest L X e f) :
      X.RefPresent (.thread e) ∧ X.RefPresent (.thread f) := by
    obtain ⟨_, _, pc, inc, n, einst, finst, he, hf⟩ := h
    exact ⟨⟨_, he⟩, ⟨_, hf⟩⟩
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨he, _, _, hp⟩ := h; exact ⟨hp, he ▸ hp⟩
  · obtain ⟨_, _, i, j, hi, hj, hij, hstep, hjl⟩ := h
    rw [hi, hj]
    exact ⟨atIndex (by rw [hij]; omega), atIndex hjl⟩
  · obtain ⟨i, j, hi, hj, hp, hq, _⟩ := h
    rw [hi, hj]; exact ⟨hp, hq⟩
  · obtain ⟨_, _, i, j, hi, hj, _, k, his, hjs⟩ := h
    rw [hi, hj]; exact ⟨atIndex his.lt, atIndex hjs.lt⟩
  · obtain ⟨_, _, i, j, hi, hj, _, k, his, hjs⟩ := h
    rw [hi, hj]; exact ⟨atIndex his.lt, atIndex hjs.lt⟩
  · obtain ⟨hb, -, hs⟩ := h
    rcases hs with ⟨-, hfalse, -⟩ | ⟨-, -, hef⟩
    · rw [hb] at hfalse; cases hfalse
    · exact stageEdge_present hef
  · obtain ⟨_, _, m, i, j, ri, rj, hri, hie, hrj, hje, _⟩ := h
    rw [← hie, ← hje]
    exact ⟨object_record_present hv.tma (List.mem_of_getElem? hri),
      object_record_present hv.tma (List.mem_of_getElem? hrj)⟩
  · obtain ⟨i, j, hi, hj, hp, hq, _⟩ := h
    rw [hi, hj]; exact ⟨hp, hq⟩
  · obtain ⟨-, -, j, hf, hwit⟩ := h
    rw [hf]
    obtain ⟨fills, hneed, hpres, hfill⟩ := hwit
    exact ⟨hpres, witness_present ⟨fills, hneed, hpres, hfill⟩⟩
  · obtain ⟨-, -, i, j, hi, hj, _, mask, inst, ⟨pc, he⟩, ⟨pc', hf⟩⟩ := h
    rw [hi, hj]; exact ⟨⟨_, he⟩, ⟨_, hf⟩⟩
  · obtain ⟨-, -, i, j, hi, hj, a, b, bs, cs, hw, hr, -⟩ := h
    rw [hi, hj]; exact ⟨memWrites_present hw, memReads_present hr⟩
  · obtain ⟨i, j, hi, hj, -, -, hp⟩ := h
    rw [hi, hj]; exact regRequest hp
  · obtain ⟨-, -, i, j, hi, hj, cta, hp⟩ := h
    rw [hi, hj]
    obtain ⟨k, l, x, y, hx, hy, -, he, hf⟩ := hp
    exact ⟨pairMember ((hv.tmemPair.1 cta).1 x (List.mem_of_getElem? hx)).2.2 he,
      pairMember ((hv.tmemPair.1 cta).1 y (List.mem_of_getElem? hy)).2.2 hf⟩
  · obtain ⟨-, -, i, j, hi, hj, hs⟩ := h
    rw [hi, hj]; exact fenceSync_present hs
  · obtain ⟨-, -, his⟩ := h
    obtain ⟨-, -, i, p, hi, hf, hp, hq, -⟩ := his
    rw [hf]
    exact ⟨hi ▸ hp, hq⟩

/-- Ordinary instructions cannot be the issuer of an async stage. -/
theorem plain_no_async (hv : EffectValidity L X) {i : EvId} {ev : Event}
    (hi : X.get i = some ev) (hk : ev.kind.isTma = false) (p : Part) :
    ¬ X.AsyncPresent i p := by
  intro hp
  obtain ⟨ev', he, ht⟩ := asyncPresent_source hv hp
  rw [hi] at he
  cases he
  rw [hk] at ht
  cases ht

theorem plain_no_objectAction {i : EvId} {ev : Event}
    (hi : X.get i = some ev) (hk : ev.kind.isTma = false) (m : Loc) :
    objectAction X X.async m (.thread i) = none := by
  obtain ⟨pc, kind⟩ := ev
  cases kind <;> simp_all [Kind.isTma, objectAction]

theorem plain_no_object_before (ht : TmaOk X) {i : EvId} {ev : Event}
    (hi : X.get i = some ev) (hk : ev.kind.isTma = false) (m : Loc) (f : Ref) :
    ¬ MBarrier.Before (X.objects m) (.thread i) f := by
  rintro ⟨a, b, ra, rb, ha, hid, _⟩
  have ho := ((ht.2.2.1 m).2.1 ra (List.mem_of_getElem? ha)).1
  rw [hid, plain_no_objectAction hi hk] at ho
  cases ho

end
end
end PTX
