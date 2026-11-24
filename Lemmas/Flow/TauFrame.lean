-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run
public import Lemmas.Register.RegisterFrame

@[expose] public section

namespace PTX.Proof

/-- A successful Core-only local step either skips its guard or has its decoded
instruction's register footprint and successor program counter. -/
theorem tau_core_frame {k : Kernel} {l : Launch} {g : Nat} {t u : TState}
    {ins : Instr} (hc : k.code[t.pc]? = some ins) (ht : Tau k [] l g t u) :
    u = skip t ∨ LocalFrame ins.op t u := by
  unfold Tau at ht
  cases hFault : t.fault with
  | some f => simp [out, hFault] at ht
  | none =>
    cases hg : guardHolds t ins.guard with
    | error f => simp [out, hFault, hc, hg] at ht
    | ok b =>
      cases b with
      | false =>
        exact .inl (Out.tau.inj (by simpa only [out, hFault, hc, hg] using ht)).symm
      | true =>
        cases hl : ins.op.isLocal with
        | false => simp [out, hFault, hc, hg, hl] at ht
        | true =>
          cases he : execLocalA [] l g t ins.op with
          | error f => simp [out, hFault, hc, hg, hl, he] at ht
          | ok a =>
            have hEq : a = u := Out.tau.inj (by simpa [out, hFault, hc, hg, hl, he] using ht)
            subst a
            exact .inr (execLocal_frame (show execLocal l g t ins.op = .ok u from he))

/-- A silent step has a decoded instruction at the starting PC. -/
theorem tau_core_has_code {k : Kernel} {l : Launch} {g : Nat} {t u : TState}
    (h : Tau k [] l g t u) : ∃ ins, k.code[t.pc]? = some ins := by
  cases hc : k.code[t.pc]? with
  | some ins => exact ⟨ins, rfl⟩
  | none =>
    cases hf : t.fault <;> simp [Tau, out, hc, hf] at h

/-- An unguarded event instruction cannot take a silent step. -/
theorem tau_core_not_event {k : Kernel} {l : Launch} {g : Nat} {t u : TState} {op : Op}
    (hc : k.code[t.pc]? = some ⟨none, op⟩) (he : op.isLocal = false)
    (h : Tau k [] l g t u) : False := by
  cases hf : t.fault <;> simp [Tau, out, hf, hc, guardHolds, he, pure, Except.pure] at h

/-- A successful local step preserves all registers outside its decoded write set. -/
theorem tau_core_regs {k : Kernel} {l : Launch} {g : Nat} {t u : TState}
    {ins : Instr} {r : Nat} (hc : k.code[t.pc]? = some ins) (ht : Tau k [] l g t u)
    (hr : r ∉ writesRegs ins.op) : u.regs r = t.regs r := by
  rcases tau_core_frame hc ht with rfl | h
  · rfl
  · exact h.regs r hr

/-- Two Core local steps with fallthrough successors preserve the registers outside
the two decoded write sets. -/
theorem run_two_core_frame {k : Kernel} {l : Launch} {g : Nat} {t u : TState}
    {i₁ i₂ : Instr} (hc₁ : k.code[t.pc]? = some i₁) (hc₂ : k.code[t.pc + 1]? = some i₂)
    (hp : nextPc i₁.op t.pc = t.pc + 1) (hb : ∀ pc, ¬ BrxTarget i₁.op pc)
    (hr : run k [] l g 2 t = some u) :
    ∀ r, r ∉ writesRegs i₁.op → r ∉ writesRegs i₂.op → u.regs r = t.regs r := by
  cases h₁ : tauStep k [] l g t with
  | none => simp only [run, h₁, Option.bind_none] at hr; cases hr
  | some v =>
    have h₂ : tauStep k [] l g v = some u := by
      cases hn : tauStep k [] l g v with
      | none => simp only [run, h₁, hn, Option.bind_some, Option.bind_none] at hr; cases hr
      | some w =>
        simp only [run, h₁, hn, Option.bind_some, Option.some.injEq] at hr
        rw [hr]
    have hTau₁ := tauStep_iff.mp h₁
    have hTau₂ := tauStep_iff.mp h₂
    have hv : v.pc = t.pc + 1 := by
      rcases tau_core_frame hc₁ hTau₁ with rfl | h
      · rfl
      · exact h.pc.elim (·.trans hp) (fun h' => absurd h' (hb _))
    rw [← hv] at hc₂
    intro r h₁r h₂r
    exact (tau_core_regs hc₂ hTau₂ h₂r).trans (tau_core_regs hc₁ hTau₁ h₁r)

/-- Matching step models at the two fallthrough PCs transport an evaluated local run. -/
theorem run_two_core_transport {k : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {t u : TState} {i : Instr} (hc : k.code[t.pc]? = some i)
    (hp : nextPc i.op t.pc = t.pc + 1) (hb : ∀ pc, ¬ BrxTarget i.op pc)
    (hModel : ∀ {s : TState}, s.pc = t.pc ∨ s.pc = t.pc + 1 → out k A l g s = out k [] l g s)
    (hr : run k [] l g 2 t = some u) : run k A l g 2 t = some u := by
  cases h₁ : tauStep k [] l g t with
  | none => simp [run, h₁] at hr
  | some v =>
    have hv : v.pc = t.pc + 1 := by
      rcases tau_core_frame hc (tauStep_iff.mp h₁) with rfl | h
      · rfl
      · exact h.pc.elim (·.trans hp) (fun h' => absurd h' (hb _))
    have hFirst : tauStep k A l g t = some v := by
      rw [tauStep, hModel (.inl rfl), ← tauStep, h₁]
    have hSecond : tauStep k A l g v = tauStep k [] l g v := by
      rw [tauStep, hModel (.inr hv), ← tauStep]
    simpa only [run, hFirst, h₁, Option.bind_some, hSecond] using hr

/-- Transport a local run through a region where the two models agree, while preserving
the registers specified by a per-step invariant for the Core run. -/
theorem run_core_region {k : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {n : Nat} {t u : TState} {region : Nat → Prop} {kept : Nat → Prop}
    (hModel : ∀ {s : TState}, region s.pc → out k A l g s = out k [] l g s)
    (hStep : ∀ {s s' : TState}, region s.pc → Tau k [] l g s s' →
      region s'.pc ∧ ∀ r, kept r → s'.regs r = s.regs r)
    (hr : run k [] l g n t = some u) (ht : region t.pc) :
    run k A l g n t = some u ∧ region u.pc ∧ ∀ r, kept r → u.regs r = t.regs r := by
  induction n generalizing t with
  | zero =>
    obtain rfl := Option.some.inj hr
    exact ⟨rfl, ht, fun _ _ => rfl⟩
  | succ n ih =>
    simp only [run] at hr ⊢
    cases h : tauStep k [] l g t with
    | none => simp [h] at hr
    | some v =>
      rw [h, Option.bind_some] at hr
      have hA : tauStep k A l g t = some v := by
        rw [tauStep, hModel ht, ← tauStep, h]
      obtain ⟨hv, hf⟩ := hStep ht (tauStep_iff.mp h)
      obtain ⟨hs, hu, hf'⟩ := ih hr hv
      exact ⟨by rw [hA, Option.bind_some, hs], hu, fun r hk => (hf' r hk).trans (hf r hk)⟩

end PTX.Proof
