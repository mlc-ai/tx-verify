-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Thread.Steps
public import Kernels.BlockSum.Proof.Thread.Start
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The thread's machine is sound

The obligations of the site machine (`Flow.Code.Sound`): the start reaches the input load, and
every site is an event instruction whose step reaches its successor or a dead state. No site has
an undefined-behaviour template (`tmplOk`): a thread performs undefined behaviour only after the
machine has stopped. -/

namespace PTX.Kernels.BlockSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {g : Nat}

/-- Each site is an unguarded event instruction. -/
theorem site_ok (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts A B L g d) ins.guard := by
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s with
  | input => exact ⟨_, Flow.code_load_0, rfl, trivial⟩
  | share => exact ⟨_, Flow.code_store_0, rfl, trivial⟩
  | bar => exact ⟨_, Flow.code_bar_0, rfl, trivial⟩
  | sum => exact ⟨_, Flow.code_load_1, rfl, trivial⟩
  | out => exact ⟨_, Flow.code_store_1, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

theorem of_cont {d : D} {e : Event} {u : TState} (h : Cont A B L g d e u) :
    ((code A B L g).next d e = some none ∨ ∃ d' t', (code A B L g).next d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ (code A B L g).Good (some d') t') ∨
    ((code A B L g).next d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) :=
      by
  rcases h with ⟨d', t', hn, hl, hat, hi⟩ | ⟨hn, hd⟩
  · exact .inl (.inr ⟨d', t', hn, hl, hat, hi⟩)
  · exact .inr ⟨hn, hd⟩

/-- **The thread's site machine is sound.** -/
theorem sound (hpre : Pre L A B x mem0) (hg : g < L.threads) : (code A B L g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := start hpre hg
    have hi : Inv { site := .input } := ⟨by simp, by simp, by simp⟩
    exact ⟨t, hr, ht, hi⟩
  steps := by
    intro d
    constructor
    · intro _
      exact site_ok d
    · intro t e u ins h hi hc hf
      have h' : At t d.site.pc (facts A B L g d) := h
      have hi' : Inv d := hi
      have hc' : kernel.code[d.site.pc]? = some ins := hc
      have hf' : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u) := hf
      apply of_cont
      rcases hs : d.site
      · exact step_input hpre hg hs h' hc' hf'
      · exact step_share hs hi' h' hc' hf'
      · exact step_bar hpre hs h' hc' hf'
      · exact step_sum hpre hg hs hi' h' hc' hf'
      · exact step_out hs h' hc' hf'
      · exfalso
        rw [hs] at hc' hf'
        obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_exit_0)
        exact absurd hf'.2 (by simp)

/-- No site has an undefined-behaviour template. -/
theorem tmplOk (hpre : Pre L A B x mem0) (hg : g < L.threads) : (code A B L g).TmplOk := by
  intro d t ins hat hi hc f
  have h : At t d.site.pc (facts A B L g d) := hat
  have hi' : Inv d := hi
  have hc' : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨s, v, i, acc, sm⟩ := d
  simp only at h hc' hi' ⊢
  cases s with
  | input =>
    obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_load_0)
    rw [tmpl_input hpre hg h]; simp
  | share =>
    obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_store_0)
    rw [tmpl_share hpre h, storeValue_of_bytes (hi'.share rfl)]; simp
  | bar =>
    obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_0)
    rw [tmpl_bar]; simp
  | sum =>
    obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_load_1)
    rw [tmpl_sum hpre (hi'.sum rfl).1 h]; simp
  | out =>
    obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_store_1)
    rw [tmpl_out hpre hg (hi'.out rfl).1 h]; simp
  | exit =>
    obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_exit_0)
    rw [tmpl_exit]; simp

end
end PTX.Kernels.BlockSum.Proof
