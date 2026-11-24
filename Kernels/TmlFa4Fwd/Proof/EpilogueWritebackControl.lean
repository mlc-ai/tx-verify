-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue
public import Lemmas.Snoc.ControlEffect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX Proof

noncomputable section

/-- Every local step within the writeback stays in its instruction interval. The interval ends
before the exit scan, which can only be reached by the last release event. -/
abbrev WritebackPc (pc : Nat) : Prop := 2958 ≤ pc ∧ pc < 2986

private theorem tau_of_branch {l : Launch} {g : Nat} {t u : TState}
    {guard : Option (Nat × Bool)} {target : Nat} {uni : Bool}
    (hc : kernel.code[t.pc]? = some ⟨guard, .bra target uni⟩)
    (hr : Tau kernel [] l g t u) : u.pc = t.pc + 1 ∨ u.pc = target := by
  unfold Tau at hr
  simp only [out, hc] at hr
  split at hr <;> try contradiction
  split at hr <;> try contradiction
  next =>
    have hu := Out.tau.inj hr
    exact .inl (congrArg TState.pc hu).symm
  next =>
    change Out.tau { t with pc := target } = .tau u at hr
    exact .inr (congrArg TState.pc (Out.tau.inj hr)).symm

private theorem no_tau_of_event {l : Launch} {g : Nat} {t u : TState} {op : Op}
    (hc : kernel.code[t.pc]? = some ⟨none, op⟩) (hLocal : op.isLocal = false)
    (hr : Tau kernel [] l g t u) : False := by
  unfold Tau at hr
  cases h : t.fault <;> simp [out, hc, hLocal, h, guardHolds, pure, Except.pure] at hr

private theorem tau_of_next {l : Launch} {g : Nat} {t u : TState} {op : Op}
    (hc : kernel.code[t.pc]? = some ⟨none, op⟩)
    (hKind : controlOp op = true ∨ op = .addr (.cvta false .param 64 7868 (.reg 7290)))
    (hr : Tau kernel [] l g t u) : ∃ r v, u = next (setReg t r v) := by
  unfold Tau at hr
  have hf : t.fault = none := by
    cases h : t.fault
    · rfl
    · simp [out, h] at hr
  simp only [out, hf, hc, guardHolds, pure, Except.pure] at hr
  split at hr <;> try contradiction
  split at hr <;> try contradiction
  rename_i v he
  have hEq := Out.tau.inj hr
  subst u
  clear hr
  rcases hKind with hCtrl | rfl
  · rw [exec_controlEffect NoControlRule.nil hCtrl] at he
    cases h : controlEffect l g t op with
    | error f =>
      simp only [h, Except.map] at he
      cases he
    | ok dv =>
      simp only [h, Except.map] at he
      exact ⟨dv.1, dv.2, (Except.ok.inj he).symm⟩
  · rw [execLocalA_nil, execLocal_cvta rfl] at he
    simp only [execCvta, bind, Except.bind] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    split at he <;> try contradiction
    exact ⟨7868, _, (Except.ok.inj he).symm⟩

private inductive WritebackInstruction (pc : Nat) : Instr → Prop where
  | event (op : Op) (hLocal : op.isLocal = false) :
      WritebackInstruction pc ⟨none, op⟩
  | next (op : Op)
      (hKind : controlOp op = true ∨ op = .addr (.cvta false .param 64 7868 (.reg 7290)))
      (hNext : WritebackPc (pc + 1)) : WritebackInstruction pc ⟨none, op⟩
  | branch (guard : Option (Nat × Bool)) (target : Nat) (uni : Bool)
      (hNext : WritebackPc (pc + 1)) (hTarget : WritebackPc target) :
      WritebackInstruction pc ⟨guard, .bra target uni⟩

private theorem writebackInstruction (i : Fin 28) :
    ∃ ins, kernel.code[2958 + i.val]? = some ins ∧ WritebackInstruction (2958 + i.val) ins := by
  fin_cases i
  · exact ⟨_, Flow.code_2958, .event _ rfl⟩
  · exact ⟨_, Flow.code_2959, .branch _ _ _ (by decide) (by decide)⟩
  · exact ⟨_, Flow.code_2960, .branch _ _ _ (by decide) (by decide)⟩
  · exact ⟨_, Flow.code_2961, .next _ (.inr rfl) (by decide)⟩
  · exact ⟨_, Flow.code_2962, .next _ (.inl rfl) (by decide)⟩
  · exact ⟨_, Flow.code_2963, .event _ rfl⟩
  · exact ⟨_, Flow.code_2964, .next _ (.inl rfl) (by decide)⟩
  · exact ⟨_, Flow.code_2965, .event _ rfl⟩
  · exact ⟨_, Flow.code_2966, .next _ (.inl rfl) (by decide)⟩
  · exact ⟨_, Flow.code_2967, .event _ rfl⟩
  · exact ⟨_, Flow.code_2968, .next _ (.inl rfl) (by decide)⟩
  · exact ⟨_, Flow.code_2969, .event _ rfl⟩
  · exact ⟨_, Flow.code_2970, .event _ rfl⟩
  · exact ⟨_, Flow.code_2971, .next _ (.inl rfl) (by decide)⟩
  · exact ⟨_, Flow.code_2972, .event _ rfl⟩
  · exact ⟨_, Flow.code_2973, .branch _ _ _ (by decide) (by decide)⟩
  · exact ⟨_, Flow.code_2974, .branch _ _ _ (by decide) (by decide)⟩
  · exact ⟨_, Flow.code_2975, .next _ (.inl rfl) (by decide)⟩
  · exact ⟨_, Flow.code_2976, .event _ rfl⟩
  · exact ⟨_, Flow.code_2977, .event _ rfl⟩
  · exact ⟨_, Flow.code_2978, .event _ rfl⟩
  · exact ⟨_, Flow.code_2979, .event _ rfl⟩
  · exact ⟨_, Flow.code_2980, .event _ rfl⟩
  · exact ⟨_, Flow.code_2981, .event _ rfl⟩
  · exact ⟨_, Flow.code_2982, .next _ (.inl rfl) (by decide)⟩
  · exact ⟨_, Flow.code_2983, .event _ rfl⟩
  · exact ⟨_, Flow.code_2984, .event _ rfl⟩
  · exact ⟨_, Flow.code_2985, .event _ rfl⟩

private theorem tau_writeback_pc {l : Launch} {g : Nat} {t u : TState}
    (ht : WritebackPc t.pc) (h : Tau kernel [] l g t u) : WritebackPc u.pc := by
  let i : Fin 28 := ⟨t.pc - 2958, by have := ht.2; omega⟩
  have hi : 2958 + i.val = t.pc := by have := ht.1; dsimp [i]; omega
  obtain ⟨ins, hc, hs⟩ := writebackInstruction i
  rw [hi] at hc hs
  cases hs with
  | event op hLocal => exact (no_tau_of_event hc hLocal h).elim
  | next op hKind hNext =>
    obtain ⟨r, val, rfl⟩ := tau_of_next hc hKind h
    exact hNext
  | branch guard target uni hNext hTarget =>
    rcases tau_of_branch hc h with hp | hp
    · exact hp ▸ hNext
    · exact hp ▸ hTarget

/-- A local writeback path can be replayed under any assumptions that preserve `out` on it. -/
theorem writebackLiftLocal {A : List Assumption} {l : Launch} {g : Nat} {t u : TState}
    (hEq : ∀ {s : TState}, WritebackPc s.pc → out kernel A l g s = out kernel [] l g s)
    (ht : WritebackPc t.pc) (h : Relation.ReflTransGen (Tau kernel [] l g) t u) :
    Relation.ReflTransGen (Tau kernel A l g) t u := by
  suffices hBoth : WritebackPc u.pc ∧ Relation.ReflTransGen (Tau kernel A l g) t u from hBoth.2
  induction h with
  | refl => exact ⟨ht, .refl⟩
  | @tail v w hinit hstep ih =>
    refine ⟨tau_writeback_pc ih.1 hstep, ih.2.tail ?_⟩
    unfold Tau at hstep ⊢
    rwa [hEq ih.1]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
