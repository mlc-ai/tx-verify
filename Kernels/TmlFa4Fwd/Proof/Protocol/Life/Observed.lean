-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.SharedLifetime
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Exit
import Lemmas.Kernel.ExitChain
import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # An observed stage ends before the observing lane's exit

A stage that a successful poll of a lane of an exited CTA observes ends before the lane's exit: the
poll is a canonical spin (`of_observed`). A recorded stage is present (`observed_notified`,
`observed_load`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hX : Consistent L kernel Assumptions.all m X)
include hX

/-- **A stage that a lane of an exited CTA observes ends before the lane's exit.** -/
theorem of_observed {i : EvId} {q : Part} {c h j pc par : Nat} {l : Loc} {acq acq' : Bool}
    {sc sc' : MbarScope} (hr : X.RefPresent (.async i q))
    (hh : h < L.threads) (hc : h / L.block = c)
    (hw : X.get (h, j) = some ⟨pc, .wait l par true acq sc⟩)
    (hobs : WaitObserves X (.async i q) (h, j) l acq' sc')
    (hx : CtaExited L X c) :
    SharedFinished L kernel Assumptions.all X (.async i q) c := by
  obtain ⟨pch, hxh⟩ := exit_of_exited hx hh hc
  obtain ⟨hk, hl⟩ := before_exit hw (by simp) hxh
  obtain ⟨ex, hspin⟩ := poll_spin hX _ _ _ _ _ _ hw
  have hres : Resumes kernel X (h, j) (h, (X.tr h).length - 1) :=
    Resumes.of_spin hw hspin rfl hk hl
  exact SharedFinished.of_completedBefore (finish := (h, (X.tr h).length - 1)) hr
    ⟨hh, hc, pch, hxh⟩
    (CompletedBefore.of_before hobs.before (.single (DepStep.of_resumes L hres)))

/-- An observed commit notification is present, of its target. -/
theorem observed_notified {i w : EvId} {r : Fin 16} {l : Loc} {acq : Bool} {sc : MbarScope}
    (h : WaitObserves X (.async i (.tcNotify r)) w l acq sc) : r ∈ X.tcNotified i ∧
      ∃ pc s, X.get i = some ⟨pc, .tc (.commit s)⟩ ∧ TcCommit.target s r = some l := by
  obtain ⟨_, _, a, _, ha, hid, _⟩ := h.before
  have hm := ((hX.tma.2.2.1 l).2.1 a (List.mem_of_getElem? ha)).1
  rw [hid] at hm
  simp only [objectAction] at hm
  cases he : X.get i with
  | none => simp [he] at hm
  | some ev =>
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> simp only [he, reduceCtorEq] at hm
    case tc k =>
      cases k <;> simp only [reduceCtorEq] at hm
      case commit s =>
        split at hm
        · rename_i hh
          exact ⟨hh.2, pc, s, rfl, hh.1⟩
        · cases hm

/-- An observed tensor load has notified. -/
theorem observed_load {i w : EvId} {l : Loc} {acq : Bool} {sc : MbarScope}
    (h : WaitObserves X (.async i (.notify .load)) w l acq sc) :
    ∃ o, X.tensor i = some o ∧ o.effects.notified = true := by
  obtain ⟨_, _, a, _, ha, hid, _⟩ := h.before
  have hm := ((hX.tma.2.2.1 l).2.1 a (List.mem_of_getElem? ha)).1
  rw [hid] at hm
  simp only [objectAction] at hm
  cases he : X.get i with
  | none => simp [he] at hm
  | some ev =>
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> simp only [he, reduceCtorEq] at hm
    case tensorIssue a s =>
      cases ht : X.tensor i with
      | none => simp [ht] at hm
      | some o =>
        refine ⟨o, rfl, ?_⟩
        simp only [ht, Option.bind_eq_bind, Option.bind_some] at hm
        split at hm
        · rename_i hh
          exact hh.2
        · cases hm

end

end PTX.Kernels.TmlFa4Fwd.Proof.Life
