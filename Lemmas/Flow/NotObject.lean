-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWait
public import Lemmas.Flow.NotArrive
public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.Events

@[expose] public section

/-! # Events that use an mbarrier object

A proof tool. An mbarrier object's history records only events of these instructions: its
initialization, invalidation, arrivals, polls, tensor loads and asynchronous copies (bulk copies,
`st.async`/`red.async` and `cp.async`, which may complete on it), `cp.async.mbarrier.arrive`,
Tensor Core commits notifying it, and cluster launch control requests. `objectOp` names these
instructions; every other instruction fires no event that uses an object (`fires_notObject`). A
poll and an initialization address an object of the thread's own CTA (`fires_wait_local`,
`mbarLoc_local`). Protocol proofs attribute an object's records to their issuers with
these, checking only the sites whose instruction is an object instruction. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- Event kinds that can make a record of an mbarrier object. -/
def ObjectKind : Kind → Prop
  | .mbInit .. | .mbInval .. | .arrive .. | .wait .. | .tensorIssue .. | .copy _
  | .asyncArrive .. | .clcIssue .. => True
  | .tc (.commit _) => True
  | _ => False

/-- A template whose event uses no mbarrier object. -/
def NotObject : Tmpl → Prop
  | .mbInit .. | .mbInval .. | .arrive .. | .wait .. | .tensorIssue .. | .copy .. | .asyncArrive ..
  | .clcIssue .. => False
  | .tc (.commit _) _ => False
  | _ => True

/-- Instructions whose events can use an mbarrier object. -/
def objectOp : Op → Bool
  | .mbarInit .. | .mbarInval .. | .mbarArrive .. | .mbarWait .. | .cpTensor .. | .cpBulk ..
  | .asyncStore .. | .cpAsync .. | .cpAsyncArrive .. | .tcCommit .. | .clcTryCancel .. => true
  | _ => false

theorem ofExec_notObject {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotObject r) :
    NotObject (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notObject {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotObject m) :
    NotObject (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive => exact h.elim)
      | (case wait => exact h.elim)
  · exact h

/-- The template of an instruction's local rule, or its `noRule` fault, uses no object. -/
theorem ruleTmpl_notObject {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotObject (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · rename_i r _
    cases r <;> simp only [localSregTmpl, sregTmpl, NotObject]
  · simp only [NotObject]

theorem ite_notObject {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotObject a)
    (hb : NotObject b) : NotObject (if c then a else b) := by
  split <;> assumption

/-- Every instruction other than an object instruction fires no event that uses an object. -/
theorem eventTmpl_notObject {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : objectOp op = false) : NotObject (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notObject (op := .int i)
  case move m => exact ruleTmpl_notObject (op := .move m)
  case cvt c => exact ruleTmpl_notObject (op := .cvt c)
  all_goals simp only [objectOp, Bool.true_eq_false] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notObject
       simp only [tmaTmpl]
       trivial)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl,
        tcTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notObject)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notObject)
         | split)
    | trivial

/-- A template that uses no object fires no event that uses one. -/
theorem fires_notObject {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : NotObject m)
    (hf : Fires pc m e o) : ¬ ObjectKind e.kind := by
  intro hk
  cases m
  case tc k t =>
    obtain ⟨rfl, -⟩ := hf
    cases k <;> simp only [NotObject] at hm <;> exact hk
  all_goals simp only [NotObject] at hm
  all_goals simp only [Fires] at hf
  all_goals first
    | (obtain ⟨rfl, -⟩ := hf; exact hk)
    | (obtain ⟨_, rfl, -⟩ := hf; exact hk)
    | (obtain ⟨_, _, rfl, -⟩ := hf; exact hk)

/-- An instruction that is not an object instruction fires no event that uses an object. -/
theorem notObject_of_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hop : objectOp op = false)
    (hf : Fires pc (eventTmpl A L g t op) e o) : ¬ ObjectKind e.kind :=
  fires_notObject (eventTmpl_notObject hop) hf

/-- A shared address read without cluster addressing is in the thread's own CTA. -/
theorem readSharedAddress_local {L : Launch} {g : Nat} {t : TState} {w : Nat} {gen : Bool}
    {a : Opnd} {loc : Loc} (h : readSharedAddress L g t w gen false a = .ok loc) :
    loc.space = .shared ∧ loc.cta = g / L.block := by
  unfold readSharedAddress at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    Bool.false_eq_true, false_or] at h
  repeat' (first | split at h | (cases h; done))
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals (constructor <;> first | rfl | (dsimp only; omega))

/-- A shared address computed without cluster addressing is in the thread's own CTA. -/
theorem sharedEffAddr_local {L : Launch} {g : Nat} {t : TState} {base : Nat} {off : Int}
    {m : Loc} (h : sharedEffAddr L g t false base off = .ok m) :
    m.space = .shared ∧ m.cta = g / L.block := by
  unfold sharedEffAddr at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (first | split at h | (cases h; done))
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  · rename_i v hl
    have h' := readSharedAddress_local hl
    exact h'
  · exact ⟨rfl, rfl⟩

/-- An mbarrier addressed without cluster addressing is in the thread's own CTA. -/
theorem mbarLoc_local {L : Launch} {g : Nat} {t : TState} {base : Nat} {off : Int} {m : Loc}
    (h : mbarLoc L g t base off = .ok m) : m.space = .shared ∧ m.cta = g / L.block := by
  unfold mbarLoc effAddr at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | split at h | (cases h; done))
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals (rename_i hl _; exact sharedEffAddr_local hl)

/-- A poll is on an mbarrier of the thread's own CTA. -/
theorem fires_wait_local {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait m p ok acq sc) :
    m.space = .shared ∧ m.cta = g / L.block := by
  by_cases hop : ∃ q b off par a s, op = .mbarWait q b off par a s
  · obtain ⟨q, b, off, par, a, s, rfl⟩ := hop
    cases hm : mbarLoc L g t b off with
    | error f =>
      simp only [eventTmpl, tmaTmpl, hm, bind, Except.bind, ofExec] at hf
      simp only [widenMbarScope, ite_self, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok m' =>
      cases hq : readBits L g t 32 par with
      | error f =>
        simp only [eventTmpl, tmaTmpl, hm, hq, bind, Except.bind, ofExec] at hf
        simp only [widenMbarScope, ite_self, Fires] at hf
        rw [hf.1] at hk
        cases hk
      | ok q' =>
        cases o with
        | none =>
          simp only [eventTmpl, tmaTmpl, hm, hq, bind, Except.bind, pure, Except.pure, ofExec,
            widenMbarScope] at hf
          split at hf <;> (try split at hf) <;> simp [Fires] at hf
        | some u =>
          obtain ⟨ok', acq', sc', he, -⟩ := fires_wait_at hm hq hf
          rw [he] at hk
          cases hk
          exact mbarLoc_local hm
  · push Not at hop
    exact absurd hk (fires_notWait (eventTmpl_notWait hop) hf _ _ _ _ _)

/-- An event that stops the thread uses no object. -/
theorem fires_none_notObject {pc : Nat} {m : Tmpl} {e : Event} (hf : Fires pc m e none) :
    ¬ ObjectKind e.kind := by
  intro hk
  cases m <;> simp only [Fires] at hf
  all_goals first
    | (obtain ⟨rfl, -⟩ := hf; exact hk)
    | simp_all

/-- A poll instruction fires a poll or an undefined behaviour. -/
theorem fires_mbarWait_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {p b : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} {pc : Nat} {e : Event}
    {o : Option TState} (hf : Fires pc (eventTmpl A L g t (.mbarWait p b off par acq sc)) e o) :
    (∃ m q ok acq' sc', e.kind = .wait m q ok acq' sc') ∨ ∃ f, e.kind = .ub f := by
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hm : mbarLoc L g t b off with
  | error f =>
    simp only [hm, ofExec, widenMbarScope, ite_self, Fires] at hf
    exact .inr ⟨f, by rw [hf.1]⟩
  | ok m =>
    cases hq : readBits L g t 32 par with
    | error f =>
      simp only [hm, hq, ofExec, widenMbarScope, ite_self, Fires] at hf
      exact .inr ⟨f, by rw [hf.1]⟩
    | ok q =>
      simp only [hm, hq, ofExec] at hf
      left
      cases acq <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
      · obtain ⟨ok, he, -⟩ := hf
        exact ⟨_, _, ok, _, _, by rw [he]⟩

/-- A poll is on the object its address evaluates to. -/
theorem fires_wait_loc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} {pc : Nat}
    {e : Event} {o : Option TState} {m : Loc} (hm : mbarLoc L g t base off = .ok m)
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base off par acq sc)) e o) :
    ∀ m' q ok acq' sc', e.kind = .wait m' q ok acq' sc' → m' = m := by
  intro m' q ok acq' sc' hk
  simp only [eventTmpl, tmaTmpl, hm, bind, Except.bind, pure, Except.pure] at hf
  cases hq : readBits L g t 32 par with
  | error f =>
    simp only [hq, ofExec, widenMbarScope, ite_self, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok q' =>
    simp only [hq, ofExec] at hf
    cases acq <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
    · obtain ⟨ok', he, -⟩ := hf
      rw [he] at hk
      cases hk
      rfl

/-- An arrival is on the object its address evaluates to. -/
theorem fires_arrive_loc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster rel : Bool} {sc : MbarScope}
    {dst : Option Nat} {pc : Nat} {e : Event} {o : Option TState} {m : Loc}
    (hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) = .ok m)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count cluster rel sc dst)) e o) :
    ∀ m' tx' c' rel' sc', e.kind = .arrive m' tx' c' rel' sc' → m' = m := by
  intro m' tx' c' rel' sc' hk
  have hm' : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) =
      .ok m := hm
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm' hf <;> rw [hm'] at hf <;>
  cases hb : readBits L g t 32 tx with
  | error f =>
    simp only [hb, ofExec, widenMbarScope, ite_self, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok bytes =>
    cases hn : readBits L g t 32 count with
    | error f =>
      simp only [hb, hn, ofExec, widenMbarScope, ite_self, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok n =>
      simp only [hb, hn, ofExec] at hf
      cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
      · rw [hf.1] at hk
        cases hk
        rfl

/-- An arrival instruction fires an arrival or an undefined behaviour. -/
theorem fires_mbarArrive_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster rel : Bool} {sc : MbarScope}
    {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count cluster rel sc)) e o) :
    (∃ m tx' c' rel' sc', e.kind = .arrive m tx' c' rel' sc') ∨ ∃ f, e.kind = .ub f := by
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) with
  | error f =>
    cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
      simp only [Bool.false_eq_true, ↓reduceIte, hm, ofExec, widenMbarScope, ite_self,
        Fires] at hf <;> exact .inr ⟨f, by rw [hf.1]⟩
  | ok m =>
    cases hb : readBits L g t 32 tx with
    | error f =>
      cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
        simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, ofExec, widenMbarScope, ite_self,
          Fires] at hf <;> exact .inr ⟨f, by rw [hf.1]⟩
    | ok bytes =>
      cases hn : readBits L g t 32 count with
      | error f =>
        cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, hn, ofExec, widenMbarScope,
            ite_self, Fires] at hf <;> exact .inr ⟨f, by rw [hf.1]⟩
      | ok n =>
        left
        cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, hn, ofExec] at hf <;>
          cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
          exact ⟨_, _, _, _, _, by rw [hf.1]⟩

/-- A cluster launch control request instruction fires a request or an undefined behaviour. -/
theorem fires_clcTryCancel_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {mc : Bool} {dst mb : Nat} {doff moff : Int} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.clcTryCancel mc dst doff mb moff)) e o) :
    (∃ sp targets, e.kind = .clcIssue sp targets) ∨ ∃ f, e.kind = .ub f := by
  simp only [eventTmpl, clcTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hd : effAddr L g t .shared dst doff with
  | error f =>
    simp only [hd, ofExec, Fires] at hf
    exact .inr ⟨f, by rw [hf.1]⟩
  | ok d =>
    cases hm : mbarLoc L g t mb moff with
    | error f =>
      simp only [hd, hm, ofExec, Fires] at hf
      exact .inr ⟨f, by rw [hf.1]⟩
    | ok m =>
      simp only [hd, hm] at hf
      split at hf
      · simp only [ofExec, Fires] at hf
        exact .inl ⟨_, _, by rw [hf.1]⟩
      · simp only [ofExec, Fires] at hf
        exact .inr ⟨_, by rw [hf.1]⟩

end
end PTX.Flow
