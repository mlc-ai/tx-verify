-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarRow
import Lemmas.Flow.EventCont
import Lemmas.Flow.TensorIssue
import Lemmas.Flow.Next

@[expose] public section
namespace PTX.MbarRow
open PTX PTX.Flow

/-- The class of event emitted at a checked site if the lane continues. -/
def Emits : Shape → Event → Prop
  | .wait _, e => ∃ l q ok acq sc, e.kind = .wait l q ok acq sc
  | .arrive _, e => ∃ l tx c rel sc, e.kind = .arrive l tx c rel sc
  | .commit, e => ∃ s, e.kind = .tc (.commit s)
  | .issue _, e => ∃ a s, e.kind = .tensorIssue a s
  | .init _, e => ∃ l c, e.kind = .mbInit l c

variable {L : Launch} {A : List Assumption} {g : Nat} {t u : TState} {e : Event} {op : Op}

theorem emits_wait {p : Opnd} (hs : (Shape.wait p).ok op)
    (hf : Fires t.pc (eventTmpl A L g t op) e (some u)) : Emits (.wait p) e := by
  cases op <;> try contradiction
  obtain ⟨l,q,ok,sc,he,_⟩ := fires_wait hf
  exact ⟨l,q,ok,_,sc,congrArg Event.kind he⟩

theorem emits_arrive {p : Opnd} (hs : (Shape.arrive p).ok op)
    (hf : Fires t.pc (eventTmpl A L g t op) e (some u)) : Emits (.arrive p) e := by
  cases op <;> try contradiction
  obtain ⟨_,l,tx,c,r,sc,he,_⟩ := fires_arrive_state hf
  exact ⟨l,tx,c,r,sc,he⟩

theorem emits_issue {mode : TensorMode} (hs : (Shape.issue mode).ok op)
    (hf : Fires t.pc (eventTmpl A L g t op) e (some u)) : Emits (.issue mode) e := by
  cases op <;> try contradiction
  case cpTensor _ _ _ _ _ _ _ _ mask _ _ =>
    cases mask with
    | some _ => simp [Shape.ok] at hs
    | none =>
      obtain ⟨a,s,he,_⟩ := fires_cpTensor_issue hf
      exact ⟨a,s,congrArg Event.kind he⟩

theorem emits_commit (hs : Shape.commit.ok op)
    (hf : Fires t.pc (eventTmpl A L g t op) e (some u)) : Emits .commit e := by
  cases op <;> try contradiction
  case tcCommit group base off mask =>
    cases mask with
    | some _ => simp [Shape.ok] at hs
    | none =>
      by_cases hg : g < L.threads
      · cases hm : mbarClusterLoc L g t base off with
        | error => simp [eventTmpl, tcCommitTmpl, hg, hm, ofExec, Fires, bind, Except.bind] at hf
        | ok m =>
          cases hr : TcCommit.resolve L group (g / L.block) m
            (BitVec.ofNat 16 (2 ^ L.rankOfCta m.cta))
          <;> simp [eventTmpl, tcCommitTmpl, hg, hm, hr, ofExec, Fires, bind, Except.bind,
            pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hf
          obtain ⟨rfl,_⟩ := hf
          exact ⟨_,rfl⟩
      · simp [eventTmpl, tcCommitTmpl, hg, ofExec, Fires, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at hf

end PTX.MbarRow
