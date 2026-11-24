-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Kernels.TmlFa4Fwd.Proof.Top.Register
public import Lemmas.Kernel.Progress.Issue
public import Lemmas.Kernel.Progress.TcSt
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Lemmas.Kernel.Progress.IssueU
import Lemmas.Tmem.Tmem1Protocol
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A released lane at a register request or at a `cp.async` operation steps

Shared by the roles' progress classes: every role's first instruction is its register request
(`reg_rel`, the lane's first by `no_reentry`), and the loader warps' row copies, their commits and
arrivals are issued without waiting (`cpAsync_rel`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

theorem wfStepAll : Assumption.WfStep (fun _ => true) L kernel m Assumptions.all :=
  fun X Y hX hle hord hr =>
    Assumptions.wfStep X Y hX hle (fun e r h1 h2 j pc sp hj _ hlt hno =>
      hord e r h1 h2 j pc sp hj rfl hlt hno) hr

theorem role_ne {X : Execution} {g : Nat} {i : Role} {d : (frag p L g i).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨i, d⟩, n))) :
    X.tr g ≠ [] := by
  intro h0
  rw [show (X.tr g).length = 0 by rw [h0]; rfl, Frame.stateAt_zero] at hσ
  simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ

/-- The instruction at a position, read from the slice of the code at an anchor before it: a check
of many positions walks to each anchor once. -/
def codeFrom (b n : Nat) : Option Instr := (kernel.code.drop b)[n - b]?

theorem codeFrom_eq {b n : Nat} (h : b ≤ n) : codeFrom b n = kernel.code[n]? := by
  rw [codeFrom, List.getElem?_drop, Nat.add_sub_cancel' h]

/-- An instruction `site_rel` steps (`e`: at the role's entry). -/
def insOk (e : Bool) : Option Instr → Bool
  | some ins => !(Descent.opKind ins.op).Rest || decide (Descent.opKind ins.op = .warp) ||
      Sched.cpAsyncOp ins.op || Sched.allocOp ins.op || Sched.tcStoreOp ins.op ||
      (Sched.regOp ins.op && e)
  | none => true

/-- What the instruction at a role's site is, with a check of it at the site's position (`w`: a
wait, the class's other file proves it; `e`: the role's entry). -/
def siteOk (pc : Nat) (w e : Bool) : Bool :=
  w || insOk e kernel.code[pc]?

/-- **A released lane at its role's entry steps**: it makes its register request. -/
theorem reg_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m fun g σ => ∃ i d n, σ = (.inr ⟨i, d⟩, n) ∧ IsEntry i d ∧
      ∀ ins, kernel.code[(thread p L g).pc σ]? = some ins → Sched.regOp ins.op = true := by
  rintro X hmax g _ hpd hrel hσ ⟨i, d, n, rfl, hE, hk⟩
  have hX := hmax.1
  refine Sched.reg_next_stepsU wfStepAll hmax (Sched.safe_noUb (hs.2 X hX))
    (fun g hg => thread_sound hp hg) hpd hσ (role_ne hσ) hrel hk fun j pc inc nn inst he => ?_
  obtain ⟨-, i', d', n', hσ', hE'⟩ := req_at hp hX (launchFollow hp hX) he
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨i'', d'', n'', heq, hne⟩ := no_reentry hσ' _ hj le_rfl _ hσ
  simp only [Prod.mk.injEq, Sum.inr.injEq] at heq
  obtain ⟨heq, -⟩ := heq
  cases heq
  exact hne hE

/-- **A released lane at a `cp.async` operation of its role steps.** -/
theorem cpAsync_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m fun g σ => ∃ i d n, σ = (.inr ⟨i, d⟩, n) ∧
      ∀ ins, kernel.code[(thread p L g).pc σ]? = some ins → Sched.cpAsyncOp ins.op = true := by
  rintro X hmax g _ hpd hrel hσ ⟨i, d, n, rfl, hk⟩
  exact Sched.cpAsync_next_stepsU wfStepAll hmax (Sched.safe_noUb (hs.2 X hmax.1))
    (fun g hg => thread_sound hp hg) hpd hσ (role_ne hσ) hrel hk

/-- **A released lane at an allocation of its role steps.** -/
theorem alloc_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m fun g σ => ∃ i d n, σ = (.inr ⟨i, d⟩, n) ∧
      ∀ ins, kernel.code[(thread p L g).pc σ]? = some ins → Sched.allocOp ins.op = true := by
  rintro X hmax g _ hpd hrel hσ ⟨i, d, n, rfl, hk⟩
  exact Sched.alloc_next_stepsU wfStepAll hmax (Sched.safe_noUb (hs.2 X hmax.1))
    (fun g hg => thread_sound hp hg) hpd hσ (role_ne hσ) hrel hk
    fun hr n col ha => (Tmem.One.alloc_zero hmax.1
      (tmem1Ops hp hmax.1 (launchFollow hp hmax.1)) hr n col ha).2

/-- **A released lane of a role steps** at a state in `Rest` that is no warp collective, when its
site is checked (`siteOk`) and no wait. -/
theorem site_rel (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m)
    {X : Execution} (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} {i : Role}
    {d : (frag p L g i).D} {n : Cls → Nat} (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g)
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨i, d⟩, n)))
    (hr : RestAt p L g (.inr ⟨i, d⟩, n)) (hc : ¬ CollAt p L g (.inr ⟨i, d⟩, n)) {e : Bool}
    (hok : siteOk ((thread p L g).pc (.inr ⟨i, d⟩, n)) false e = true)
    (he : e = true → IsEntry i d) : StepsAt p L m X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 (Sched.safe_noUb (hs.2 X hmax.1)) hpd
  rcases Frame.end_atU (fun g hg => thread_sound hp hg) hpd.1 hrun hσ with hsite | ⟨u,f,hl,ho⟩
  case inr => exact Descent.ub_steps_inOrder wfStepAll hmax.1 hpd.1 (role_ne hσ) hrel hrun hl ho
  obtain ⟨t1, ins, -, -, -, hins, -⟩ := hsite
  have one : ∀ ins', kernel.code[(thread p L g).pc (.inr ⟨i, d⟩, n)]? = some ins' → ins' = ins :=
    fun ins' h => by rw [hins] at h; exact (Option.some.inj h).symm
  simp only [siteOk, insOk, hins, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, Bool.and_eq_true] at hok
  rcases hok with ((((h | h) | h) | h) | h) | ⟨h, he'⟩
  · rw [hr ins hins] at h; cases h
  · exact absurd ⟨hr, fun ins' h' => by rw [one ins' h']; exact h⟩ hc
  · exact cpAsync_rel hp hs X hmax g _ hpd hrel hσ
      ⟨i, d, n, rfl, fun ins' h' => by rw [one ins' h']; exact h⟩
  · exact alloc_rel hp hs X hmax g _ hpd hrel hσ
      ⟨i, d, n, rfl, fun ins' h' => by rw [one ins' h']; exact h⟩
  · exact Sched.tcStore_next_stepsU wfStepAll hmax (Sched.safe_noUb (hs.2 X hmax.1))
      (fun g hg => thread_sound hp hg) hpd hσ (role_ne hσ) hrel
      (fun ins' h' => by rw [one ins' h']; exact h)
  · exact reg_rel hp hs X hmax g _ hpd hrel hσ
      ⟨i, d, n, rfl, he he', fun ins' h' => by rw [one ins' h']; exact h⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Top
