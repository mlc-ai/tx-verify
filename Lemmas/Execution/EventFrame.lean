-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.EventFrame
open PTX
noncomputable section

def WaitFrame (t : TState) (predicate : Nat) (acquire : Bool) : Tmpl → Prop
  | .wait _ _ k actualAcquire _ => actualAcquire=acquire ∧
      ∀ ok, (k ok).pc=t.pc+1 ∧ (k ok).regs predicate=some (.pred ok)
  | .ub _ => True
  | _ => False

theorem mbarWait_frame {L : Launch} {g : Nat} {t : TState}
    {predicate base : Nat} {off : Int} {par : Opnd} {acquire : Bool} {scope : MbarScope} :
    WaitFrame t predicate acquire
      (tmaTmpl L g t (.mbarWait predicate base off par acquire scope)) := by
  simp only [tmaTmpl]
  cases hm : mbarLoc L g t base off with
  | error f => simp [bind,Except.bind,ofExec,WaitFrame]
  | ok m =>
    cases hq : readBits L g t 32 par with
    | error f => simp [bind,Except.bind,ofExec,WaitFrame]
    | ok q =>
      simp [bind,Except.bind,pure,Except.pure,ofExec,WaitFrame,next,setReg]

theorem widen_wait_frame {A : List Assumption} {t : TState}
    {predicate : Nat} {acquire : Bool} {site : Nat} {m : Tmpl}
    (h : WaitFrame t predicate acquire m) :
    WaitFrame t predicate acquire (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> try exact h
    case arrive loc tx u count release scope =>
      cases release <;> cases scope <;> exact h
    case wait loc parity k actualAcquire scope =>
      cases actualAcquire <;> cases scope <;> exact h
  · exact h

/-- A real mbarrier wait returns its actual Boolean in the instruction's own
predicate register and advances once. Scope widening changes neither fact. -/
theorem mbarWait_fires {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {predicate base : Nat} {off : Int} {par : Opnd} {acquire : Bool} {scope : MbarScope}
    {e : Event}
    (hf : Fires t.pc (eventTmpl A L g t (.mbarWait predicate base off par acquire scope)) e
      (some u)) :
    ∃ m parity ok effectiveScope,
      e=⟨t.pc,.wait m parity ok acquire effectiveScope⟩ ∧
      u.pc=t.pc+1 ∧ u.regs predicate=some (.pred ok) := by
  have hm : WaitFrame t predicate acquire
      (eventTmpl A L g t (.mbarWait predicate base off par acquire scope)) :=
    widen_wait_frame mbarWait_frame
  generalize hevent : eventTmpl A L g t (.mbarWait predicate base off par acquire scope)=m at hm hf
  cases m <;> simp only [WaitFrame,Fires] at hm hf
  case wait loc parity k actualAcquire effectiveScope =>
    obtain ⟨ok,he,ho⟩ := hf
    have hu : u=k ok := Option.some.inj ho
    subst u
    exact ⟨loc,parity,ok,effectiveScope,hm.1 ▸ he,hm.2 ok⟩
  case ub => cases hf.2


end
end PTX.EventFrame
