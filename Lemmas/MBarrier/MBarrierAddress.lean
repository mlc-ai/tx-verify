-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierPhase
public import Core.Thread.Run
public import Mathlib.Tactic.SplitIfs

@[expose] public section

section
/-! An actual phase observation orders every operation of that completed phase
before the observer. This works independently for every successful observer; no
global alternating-poll enumeration is required. -/
namespace PTX.MBarrier

variable {ι : Type}

/-- A successful wait that names completed phase `phase` runs in the next logical
phase of the object, including after any number of parity wraparounds. -/
theorem CheckedLog.observed_phase {log : List (Record ι)} (h : CheckedLog log)
    {j phase : Nat} {w : Record ι} (hj : log[j]? = some w)
    (hw : w.reply.waited = some true) (ho : observedAt log j = some phase) :
    ∃ st, stateBefore log j = some st ∧ st.phase = phase+1 := by
  obtain ⟨st,parity,hs,-,-,hcompleted⟩ := h.okPoll hj hw
  simp only [observedAt,hj,Option.bind_some,hcompleted] at ho
  by_cases hpos : 0 < st.phase
  · rw [ite_eq_left hpos] at ho
    have heq : st.phase-1=phase := Option.some.inj ho
    exact ⟨st,hs,by omega⟩
  · rw [ite_eq_right hpos] at ho
    cases ho

/-- Any point in the completed phase precedes the successful observation. In
particular, this excludes an update appearing after a wait for that same phase. -/
theorem CheckedLog.phase_before_observation {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    {i j phase : Nat} {w : Record ι} (hi : i ≤ log.length)
    (hp : phaseAt log i = some phase) (hj : log[j]? = some w)
    (hw : w.reply.waited = some true) (ho : observedAt log j = some phase) : i < j := by
  obtain ⟨waitState,hwait,hphase⟩ := h.observed_phase hj hw ho
  cases hs : stateBefore log i with
  | none => simp [phaseAt,hs] at hp
  | some updateState =>
    have hupdate : updateState.phase = phase := by
      simpa only [phaseAt,hs,Option.map_some,Option.some.injEq] using hp
    by_contra hn
    have hji : j ≤ i := Nat.le_of_not_gt hn
    obtain ⟨st,hst,hle⟩ := h.phase_mono hni hji hi hwait
    rw [hs] at hst
    cases hst
    omega

end PTX.MBarrier
end

section
/-! Run-ahead bounds for one selected observer of a reusable mbarrier.
Other observers may poll successfully arbitrarily often. The arrival gate below
is a protocol premise for these derived lemmas, not an additional object rule. -/
namespace PTX.MBarrier

variable {ι : Type}

/-- A selected successful record contributes one observer observation. -/
def observerIncrement (selected : ι → Bool) (r : Record ι) : Nat :=
  if selected r.id = true ∧ r.reply.waited = some true then 1 else 0

theorem observerIncrement_success (selected : ι → Bool) (r : Record ι)
    (hs : selected r.id = true) (hw : r.reply.waited = some true) :
    observerIncrement selected r = 1 := by
  simp [observerIncrement,hs,hw]

def selectedCount (selected : ι → Bool) : List (Record ι) → Nat
  | [] => 0
  | r :: rest => observerIncrement selected r + selectedCount selected rest

def selectedBefore (selected : ι → Bool) (log : List (Record ι)) (j : Nat) : Nat :=
  selectedCount selected (log.take j)

theorem selectedCount_append (selected : ι → Bool) (xs ys : List (Record ι)) :
    selectedCount selected (xs ++ ys) = selectedCount selected xs + selectedCount selected ys := by
  induction xs with
  | nil => simp [selectedCount]
  | cons r xs ih => simp only [List.cons_append,selectedCount,ih,Nat.add_assoc]

theorem selectedBefore_succ (selected : ι → Bool) {log : List (Record ι)} {j : Nat}
    {r : Record ι} (hj : log[j]? = some r) :
    selectedBefore selected log (j+1) =
      selectedBefore selected log j + observerIncrement selected r := by
  have ht : log.take (j+1) = log.take j ++ [r] := by
    rw [List.take_add_one,hj]
    rfl
  simp only [selectedBefore,ht,selectedCount_append,selectedCount,Nat.add_zero]

/-- Only selected successful polls are required to alternate parity. The other
observers' successful polls are deliberately unconstrained by this predicate. -/
def SelectedAlternates (selected : ι → Bool) (log : List (Record ι)) (δ : Nat) : Prop :=
  ∀ j r p ok, log[j]? = some r → r.action = .pollParity p ok →
    selected r.id = true → r.reply.waited = some true →
      p % 2 = (selectedBefore selected log j + δ) % 2

theorem selectedBefore_zero (selected : ι → Bool) (log : List (Record ι)) :
    selectedBefore selected log 0 = 0 := by
  simp [selectedBefore,selectedCount]

/-- Locate the selected successful poll that made the selected count `c+1`. -/
theorem previous_selected_success (selected : ι → Bool) {log : List (Record ι)} {j c : Nat}
    (hc : selectedBefore selected log j = c+1) :
    ∃ i r, i < j ∧ log[i]? = some r ∧ selected r.id = true ∧
      r.reply.waited = some true ∧ selectedBefore selected log i = c := by
  induction j with
  | zero => rw [selectedBefore_zero] at hc; cases hc
  | succ j ih =>
    cases hr : log[j]? with
    | none =>
      have hlen : log.length ≤ j := List.getElem?_eq_none_iff.mp hr
      have heq : selectedBefore selected log (j+1) = selectedBefore selected log j := by
        simp [selectedBefore,List.take_of_length_le hlen,
          List.take_of_length_le (by omega : log.length ≤ j+1)]
      obtain ⟨i,q,hi,hq,hs,hw,hb⟩ := ih (heq ▸ hc)
      exact ⟨i,q,by omega,hq,hs,hw,hb⟩
    | some r =>
      rw [selectedBefore_succ selected hr] at hc
      unfold observerIncrement at hc
      by_cases hs : selected r.id = true ∧ r.reply.waited = some true
      · rw [ite_eq_left hs] at hc
        exact ⟨j,r,by omega,hr,hs.1,hs.2,by omega⟩
      · rw [ite_eq_right hs] at hc
        obtain ⟨i,q,hi,hq,hs',hw,hb⟩ := ih (by simpa using hc)
        exact ⟨i,q,by omega,hq,hs',hw,hb⟩


end PTX.MBarrier
end

section
/-! Ordinary shared mbarrier waits retain the issuing CTA's address ownership,
including failed and unselected polls and symbolic shared pointers. -/
namespace PTX
noncomputable section

private theorem readSharedAddress_owner {L : Launch} {g w : Nat} {t : TState}
    {generic : Bool} {a : Opnd} {l : Loc}
    (h : readSharedAddress L g t w generic false a=.ok l) : l.cta=g/L.block := by
  by_cases hw : w=32 ∨ w=64
  · cases hv : readValue L g t w a with
    | error f =>
      simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
        throw,throwThe,MonadExceptOf.throw] at h
    | ok v =>
      cases v with
      | ptr vw vg tg voff =>
        cases tg with
        | shared issuer cta =>
          simp only [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,pure,Except.pure,
            throw,throwThe,MonadExceptOf.throw] at h
          split_ifs at h with htype hissuer hcl hcta hoff
          all_goals try cases h
          rcases hcta.2.2.2 with hbad | heq
          · cases hbad
          · exact heq
        | param name =>
          simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
            throw,throwThe,MonadExceptOf.throw] at h
        | «local» owner =>
          simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
            throw,throwThe,MonadExceptOf.throw] at h
        | const =>
          simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
            throw,throwThe,MonadExceptOf.throw] at h
      | bits vw x =>
        simp only [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,pure,Except.pure,
          throw,throwThe,MonadExceptOf.throw] at h
        split_ifs at h
        all_goals try cases h
        simp_all
      | float fmt x =>
        simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
          throw,throwThe,MonadExceptOf.throw] at h
      | pred b =>
        simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
          throw,throwThe,MonadExceptOf.throw] at h
      | clc response =>
        simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
          throw,throwThe,MonadExceptOf.throw] at h
      | policy =>
        simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
          throw,throwThe,MonadExceptOf.throw] at h
      | nan fmt =>
        simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
          throw,throwThe,MonadExceptOf.throw] at h
      | pair lo hi =>
        simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
          throw,throwThe,MonadExceptOf.throw] at h
      | slice whole offset size =>
        simp [readSharedAddress,ite_eq_left hw,hv,bind,Except.bind,
          throw,throwThe,MonadExceptOf.throw] at h
  · simp [readSharedAddress,hw,bind,Except.bind,
      throw,throwThe,MonadExceptOf.throw] at h

/-- A CTA shared effective address keeps its owner for both raw offsets and
symbolic pointers. Address arithmetic changes only the byte offset. -/
theorem sharedEffAddr_owner {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {l : Loc}
    (h : sharedEffAddr L g t false base off=.ok l) : l.cta=g/L.block := by
  cases hr : readReg t base with
  | error f => simp [sharedEffAddr,hr,bind,Except.bind] at h
  | ok v =>
    cases v with
    | ptr vw vg tg voff =>
      cases tg with
      | shared issuer cta =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases ha : readSharedAddress L g t vw false false (.reg base) with
        | error f => simp [ha] at h
        | ok loc =>
          simp only [ha] at h
          cases h
          exact readSharedAddress_owner (l := loc) ha
      | param name =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
      | «local» owner =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
      | const =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
    | bits vw x =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
    | float fmt x =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
    | pred b =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
    | clc response =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
    | policy =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
    | nan fmt =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
    | pair lo hi =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl
    | slice whole offset size =>
        simp only [sharedEffAddr,hr,bind,Except.bind,pure,Except.pure] at h
        cases hb : readBits L g t 32 (.reg base) with
        | error f => simp [hb] at h
        | ok bits => simp only [hb] at h; cases h; rfl

/-- In particular, mbarWait's CTA address calculation cannot access a peer. -/
theorem mbarLoc_owner {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {l : Loc} (h : mbarLoc L g t base off=.ok l) :
    l.cta=g/L.block := by
  unfold mbarLoc at h
  cases ha : effAddr L g t .shared base off with
  | error f => simp [ha,bind,Except.bind] at h
  | ok loc =>
    simp only [ha,bind,Except.bind] at h
    split_ifs at h
    · cases h
      exact sharedEffAddr_owner ha

private theorem widened_wait_location {A : List Assumption} {pc site parity q : Nat}
    {m loc : Loc} {k : Bool → TState} {ok acquire sourceAcquire : Bool}
    {scope sourceScope : MbarScope} {o : Option TState}
    (h : Fires pc (widenMbarScope A site (.wait loc q k sourceAcquire sourceScope))
      ⟨pc,.wait m parity ok acquire scope⟩ o) : m=loc := by
  unfold widenMbarScope at h
  split at h
  · cases sourceAcquire <;> cases sourceScope <;> obtain ⟨answer,he,_⟩ := h <;> cases he <;> rfl
  · obtain ⟨answer,he,_⟩ := h
    cases he
    rfl

/-- Both polling replies retain the address owner; scope widening changes no
location and supplies no source-role or successful-wait premise. -/
theorem mbarWait_fires_owner {A : List Assumption} {L : Launch} {g pc parity : Nat}
    {t : TState} {predicate base : Nat} {off : Int} {phase : Opnd}
    {m : Loc} {ok acquire sourceAcquire : Bool} {scope sourceScope : MbarScope}
    {o : Option TState}
    (h : Fires pc (eventTmpl A L g t
      (.mbarWait predicate base off phase sourceAcquire sourceScope))
      ⟨pc,.wait m parity ok acquire scope⟩ o) : m.cta=g/L.block := by
  change Fires pc (widenMbarScope A t.pc (tmaTmpl L g t
    (.mbarWait predicate base off phase sourceAcquire sourceScope)))
    ⟨pc,.wait m parity ok acquire scope⟩ o at h
  have ub {f : Fault} : widenMbarScope A t.pc (.ub f)=.ub f := by
    unfold widenMbarScope
    split <;> rfl
  cases hm : mbarLoc L g t base off with
  | error f => simp only [tmaTmpl,hm,bind,Except.bind,ofExec,ub,Fires] at h; cases h.1
  | ok loc =>
    cases hq : readBits L g t 32 phase with
    | error f => simp only [tmaTmpl,hm,hq,bind,Except.bind,ofExec,ub,Fires] at h; cases h.1
    | ok q =>
      have hf : Fires pc (widenMbarScope A t.pc (.wait loc (q.toNat%2)
          (fun answer => next (setReg t predicate (.pred answer))) sourceAcquire sourceScope))
          ⟨pc,.wait m parity ok acquire scope⟩ o := by
        simpa only [tmaTmpl,hm,hq,bind,Except.bind,pure,Except.pure,ofExec] using h
      have he : m=loc := widened_wait_location hf
      rw [he]
      exact mbarLoc_owner hm

end
end PTX
end
