-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.AsyncMBarrier
public import Lemmas.MBarrier.MBarrierHistory
public import Mathlib.Tactic.SplitIfs
public import Lemmas.Async.AsyncCopy

@[expose] public section

/-! # The source of an object record

A proof tool. Every record of an mbarrier object comes from an actual event that names the
object: an initialization, invalidation, arrival, pending-count increment or poll of a thread,
the arrive-on of a `cp.async.mbarrier.arrive`, or the notification of a tensor copy, linear copy,
Tensor Core commit or cluster launch control request issued by a thread (`record_source`).
Protocol proofs classify an object's records with this, then use what the thread layer says about
each kind of event. -/

namespace PTX.AsyncCopy

noncomputable section

/-- The issuing event of a record, with the action it performs. -/
inductive RecordSource (X : Execution) (m : Loc) (r : MBarrier.Record Ref) : Prop
  | init {g j pc c : Nat} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .mbInit m c⟩) (ha : r.action = .init c)
  | inval {g j pc : Nat} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .mbInval m⟩) (ha : r.action = .inval)
  | arrive {g j pc tx c : Nat} {rel : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .arrive m tx c rel sc⟩) (ha : r.action = .arrive c tx)
  | wait {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait m p ok acq sc⟩) (ha : r.action = .pollParity p ok)
  | increment {g j pc : Nat} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .asyncArrive m false⟩) (ha : r.action = .increment)
  | tensor {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec} (hid : r.id = .async i (.notify .load))
      (he : X.get i = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = m)
      (ha : r.action = .completeTx (TensorTransfer.bytes sp.descriptor))
  | arriveOn {i : EvId} {pc : Nat} {m' : Loc} {noinc : Bool}
      (hid : r.id = .async i .arriveOn) (he : X.get i = some ⟨pc, .asyncArrive m' noinc⟩)
      (hm : m' = m) (hn : X.async.arrived i = true) (ha : r.action = .arrive 1 0)
  | bulk {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}
      (hid : r.id = .async i (.notify .copy)) (he : X.get i = some ⟨pc, .copy s⟩)
      (hc : s.completion = .mbarrier m) (hn : (X.async.copies i).notified = true)
      (ha : r.action = .completeTx s.dst.size)
  | commit {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
      (hid : r.id = .async i (.tcNotify rank)) (he : X.get i = some ⟨pc, .tc (.commit sp)⟩)
      (ht : TcCommit.target sp rank = some m) (ha : r.action = .arrive 1 0)
  | clc {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat} {c : Nat}
      (hid : r.id = .async i (.notify (.cta c))) (he : X.get i = some ⟨pc, .clcIssue sp tg⟩)
      (hm : m = { sp.mbar with cta := c }) (htg : c ∈ tg) (ha : r.action = .completeTx 16)

/-- An action of a reference names its source. -/
theorem objectAction_source {X : Execution} {m : Loc} {r : MBarrier.Record Ref}
    (ha : objectAction X X.async m r.id = some r.action) : RecordSource X m r := by
  obtain ⟨id, action, reply, fault⟩ := r
  simp only at ha ⊢
  cases id with
  | thread i =>
    obtain ⟨g, j⟩ := i
    cases he : X.get (g, j) with
    | none => simp [objectAction, he] at ha
    | some ev =>
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp only [objectAction, he, reduceCtorEq] at ha
      case mbInit loc c =>
        split_ifs at ha with hm
        subst loc
        exact .init rfl he (Option.some.inj ha).symm
      case mbInval loc =>
        split_ifs at ha with hm
        subst loc
        exact .inval rfl he (Option.some.inj ha).symm
      case arrive loc tx c rel sc =>
        split_ifs at ha with hm
        subst loc
        exact .arrive rfl he (Option.some.inj ha).symm
      case wait loc p ok acq sc =>
        split_ifs at ha with hm
        subst loc
        exact .wait rfl he (Option.some.inj ha).symm
      case asyncArrive loc noinc =>
        cases noinc <;> simp only [reduceCtorEq] at ha
        split_ifs at ha with hm
        subst loc
        exact .increment rfl he (Option.some.inj ha).symm
  | async i part =>
    cases part <;> simp only [objectAction, reduceCtorEq] at ha
    case notifyLoad =>
      cases he : X.get i with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [he, bind, Option.bind, reduceCtorEq] at ha
        case tensorIssue a sp =>
          cases ho : X.tensor i with
          | none => simp [ho] at ha
          | some obs =>
            simp only [ho] at ha
            split_ifs at ha with hc
            exact .tensor rfl he hc.1 (Option.some.inj ha).symm
    case notifyCopy =>
      cases hs : issuedBy X i with
      | none => simp [hs, bind, Option.bind] at ha
      | some spec =>
        simp only [hs, bind, Option.bind] at ha
        simp only [issuedBy] at hs
        cases he : X.get i with
        | none => simp [he] at hs
        | some ev =>
          obtain ⟨pc, kind⟩ := ev
          cases kind <;> simp only [he, reduceCtorEq] at hs
          case copy s =>
            simp only [Option.some.injEq] at hs
            subst hs
            split_ifs at ha with hc
            exact .bulk rfl he hc.1 hc.2 (Option.some.inj ha).symm
    case arriveOn =>
      cases he : X.get i with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [he, reduceCtorEq] at ha
        case asyncArrive m' noinc =>
          split_ifs at ha with hc
          exact .arriveOn rfl he hc.1 hc.2 (Option.some.inj ha).symm
    case tcNotify rank =>
      cases he : X.get i with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [he, reduceCtorEq] at ha
        case tc k =>
          cases k <;> simp only [reduceCtorEq] at ha
          case commit sp =>
            split_ifs at ha with hc
            exact .commit rfl he hc.1 (Option.some.inj ha).symm
    case notifyCta c =>
      cases he : X.get i with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [he, reduceCtorEq] at ha
        case clcIssue sp tg =>
          split_ifs at ha with hc
          exact .clc rfl he hc.2.2 hc.1 (Option.some.inj ha).symm

/-- Every record of an object in a consistent history has a source. -/
theorem record_source {X : Execution} (ho : ObjectsOk X) {m : Loc} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects m) : RecordSource X m r :=
  objectAction_source ((ho m).2.1 r hr).1

/-- An execution with no `mbarrier.inval` event has single-lifetime object histories. -/
theorem objects_noInval {X : Execution} (ho : ObjectsOk X) (h : ∀ e m, ¬ X.MbInval e m)
    (m : Loc) : MBarrier.NoInval (X.objects m) := by
  intro r hr ha
  cases record_source ho hr with
  | inval hid he _ => exact h _ _ ⟨_, he⟩
  | init _ _ ha' | arrive _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | commit _ _ _ ha'
  | clc _ _ _ _ ha' | increment _ _ ha' | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' =>
    rw [ha] at ha'; cases ha'

end
end PTX.AsyncCopy
