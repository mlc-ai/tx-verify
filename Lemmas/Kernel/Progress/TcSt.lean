-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Issue
public import Lemmas.Step.TcLoad
public import Lemmas.Flow.Hooks

@[expose] public section

/-! # Progress at a Tensor Memory store and its wait

A proof tool, generic over the kernel, beside `Lemmas/Kernel/Progress/Issue.lean`: a released
pending thread whose next instruction is a Tensor Memory store or a store wait performs it (the
store's delayed load wait first). -/

namespace PTX.Sched

open PTX PTX.Descent PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- A Tensor Memory store or a store wait. -/
def tcStoreOp : Op → Bool
  | .tcSt .. | .tcWaitSt => true
  | _ => false

/-- The template of such an operation: undefined behaviour, or a warp-collective event that is
neither a load nor an MMA. -/
def TcStTmpl (m : Tmpl) : Prop :=
  (∃ f, m = .ub f) ∨ ∃ k u, m = .tc k u ∧ (k = .waitLd ∨ k = .waitSt ∨ ∃ a v s, k = .st a v s)

private theorem ofExec_tcSt {r : Exec Tmpl} (h : ∀ m, r = .ok m → TcStTmpl m) :
    TcStTmpl (ofExec r) := by
  cases r with
  | error f => exact .inl ⟨f, rfl⟩
  | ok m => exact h m rfl

theorem tcSt_core {g : Nat} {t : TState} {ta : Nat} {ss : List Opnd} {sh : TcShape} :
    TcStTmpl (tcTmpl L g t (.tcSt ta ss sh)) := by
  cases sh <;> simp only [tcTmpl] <;> refine ofExec_tcSt fun m hm => ?_
  all_goals
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hm
    repeat' split at hm
    all_goals first
      | (cases hm; done)
      | (cases hm; exact .inr ⟨_, _, rfl, .inr (.inr ⟨_, _, _, rfl⟩)⟩)

theorem tcStore_tmpl {g : Nat} {t : TState} {op : Op} (h : tcStoreOp op = true) :
    TcStTmpl (eventTmpl A L g t op) := by
  cases op <;> simp only [tcStoreOp, Bool.false_eq_true] at h
  case tcSt ta ss sh =>
    exact tcStTmpl_pres (P := TcStTmpl) (fun t => .inr ⟨_, t, rfl, .inl rfl⟩) (.inl ⟨_, rfl⟩)
      fun u => tcSt_core
  case tcWaitSt =>
    simp only [eventTmpl, tcTmpl]
    refine ofExec_tcSt fun m hm => ?_
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hm
    repeat' split at hm
    all_goals first
      | (cases hm; done)
      | (cases hm; exact .inr ⟨_, _, rfl, .inr (.inl rfl)⟩)

/-- **A released pending thread at a Tensor Memory store or a store wait steps.** -/
theorem tcStore_next_steps (hA : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).Sound)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → tcStoreOp ins.op = true) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := Frame.end_at hC hp.1 hrun hσ
  rcases tcStore_tmpl (A := A) (L := L) (g := g) (t := t1) (hk ins hins) with
    ⟨f, hf⟩ | ⟨k, u, hf, hkk⟩
  · rw [hf] at hout
    exact ub_steps_inOrder hA hX hp.1 hne hrel hrun hl hout
  · rw [hf] at hout
    have hcoll : isTcColl ⟨t1.pc, .tc k⟩ = true := by
      rcases hkk with rfl | rfl | ⟨_, _, _, rfl⟩ <;> rfl
    refine .inl (Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
      ⟨_, hout, rfl, rfl⟩ hcoll (hX.tmemPairResult.snoc_not_wr ?_) (hX.tcRead_snoc_tc ?_)
      (hA.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl)))
    · rcases hkk with rfl | rfl | ⟨_, _, _, rfl⟩ <;> nofun
    · rcases hkk with rfl | rfl | ⟨_, _, _, rfl⟩ <;> nofun

end
end PTX.Sched
