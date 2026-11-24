-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Thread.Machine
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # `copy_ldg`: a thread's events

The event a site performs (`SiteEvent`), and the run invariant of a thread (`RunFacts`): at
each state of the machine, the events so far. Both are proved from the machine's own steps
(`Code.run_inv`). -/

namespace PTX.Kernels.CopyLdg.Proof
open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {g : Nat}

/-- The event a site performs: the read of four bytes of `A[g]`, the write of the word to
`B[g]` or the fault of a store of a non-word, the exit. -/
def SiteEvent (A B g : Nat) : Site → Event → Prop
  | .load, e => ∃ bs, bs.length = 4 ∧ e = ncE A g bs
  | .store v, e => (v.bytes = 4 ∧ e = wrE B g v) ∨ (v.bytes ≠ 4 ∧ ∃ f, e = ⟨Flow.store_0, .ub f⟩)
  | .exit, e => e = exE

/-- The run invariant of a thread: the events before each site. Below `N` a thread reads, then
stores the word it read, then exits; the others exit at once. -/
def RunFacts (A B N g : Nat) : Site → List Event → Prop
  | .load, pre => pre = [] ∧ g < N
  | .store v, pre => ∃ bs, bs.length = 4 ∧ rebuild 3 bs = .ok v ∧ pre = [ncE A g bs] ∧ g < N
  | .exit, pre => (pre = [] ∧ N ≤ g) ∨
      ∃ bs v, bs.length = 4 ∧ rebuild 3 bs = .ok v ∧ v.bytes = 4 ∧ pre = [ncE A g bs, wrE B g v] ∧ g
        < N

theorem tmpl_load_eq (t : TState) : (code L A B N g).tmpl (some .load) t =
    eventTmpl Nc L g t (.mem ldAcc) := by
  simp only [Code.tmpl, code, Site.pc, Flow.code_load_0, ldAcc]

theorem tmpl_store_eq (v : Value) (t : TState) : (code L A B N g).tmpl (some (.store v)) t =
    eventTmpl Nc L g t (.mem stAcc) := by
  simp only [Code.tmpl, code, Site.pc, Flow.code_store_0, stAcc]

theorem tmpl_exit_eq (t : TState) : (code L A B N g).tmpl (some .exit) t = .exit := by
  simp only [Code.tmpl, code, Site.pc, Flow.code_exit_0, eventTmpl]

/-- The event of a state of a site. -/
theorem site_event (hpre : Pre L A B N x mem0) {s : Site} {t : TState} {e : Event}
    {o : Option TState} (h : (code L A B N g).Good (some s) t)
    (hf : Fires t.pc ((code L A B N g).tmpl (some s) t) e o) : SiteEvent A B g s e := by
  obtain ⟨h, hi⟩ := h
  have h : At t s.pc (facts A B N g s) := h
  have hpc := h.1
  cases s with
  | load =>
    have hgN : g < N := hi
    rw [tmpl_load_eq, hpc] at hf
    obtain ⟨bs, hl, he, -⟩ := fires_load hpre hgN h hf
    exact ⟨bs, hl, he⟩
  | store v =>
    have hgN : g < N := hi.1
    rw [tmpl_store_eq, hpc] at hf
    obtain ⟨he, -⟩ := fires_store hpre hgN hi.2 h hf
    exact .inl ⟨hi.2, he⟩
  | exit =>
    rw [tmpl_exit_eq, hpc] at hf
    exact hf.1

/-- Along a thread's run, `RunFacts` holds at each state. -/
theorem run_facts (hpre : Pre L A B N x mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L A B N g).toMachine.Trace (some (code L A B N g).init) es) :
    ∀ j d, (code L A B N g).toMachine.after (some (code L A B N g).init) (es.take j) = some (some d)
      →
      RunFacts A B N g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (fun d pre => RunFacts A B N g d pre) ?_ ?_
  · by_cases hgN : g < N
    · simp [code, hgN, RunFacts]
    · simp [code, hgN, RunFacts]; omega
  · intro d d' pre e t ins o hq hat hinv hc hf hn
    cases d with
    | load =>
      have hgN : g < N := hinv
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
      obtain ⟨bs, hl, rfl, -⟩ := fires_load hpre hgN hat hf
      obtain ⟨rfl, -⟩ := hq
      cases hv : rebuild 3 bs with
      | error f => simp [code, next, ncE, hv] at hn
      | ok v =>
        simp only [code, next, ncE, hv] at hn
        cases hn
        exact ⟨bs, hl, hv, rfl, hgN⟩
    | store v =>
      have hgN : g < N := hinv.1
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
      obtain ⟨bs, hl, hv, rfl, -⟩ := hq
      obtain ⟨rfl, -⟩ := fires_store hpre hgN hinv.2 hat hf
      simp only [code, next, wrE] at hn
      cases hn
      exact .inr ⟨bs, v, hl, hv, rebuild_bytes_of_length hv hl, rfl, hgN⟩
    | exit => simp [code, next] at hn

/-- An event into a dead state is the read of bytes that are no word: only the load stops the
machine on an event that continues the thread. -/
theorem fired_dead (hpre : Pre L A B N x mem0) {σ : Option Site} {e : Event} {u : TState}
    (hf : (code L A B N g).toMachine.Fired σ e (some u))
    (hn : (code L A B N g).toMachine.next σ e = none) :
    ∃ bs, σ = some .load ∧ bs.length = 4 ∧ (∀ v, rebuild 3 bs ≠ .ok v) ∧ e = ncE A g bs ∧ g < N :=
      by
  obtain ⟨t, hgood, hfires⟩ := hf
  cases σ with
  | none => simp [Code.toMachine] at hn
  | some d =>
    have hi := hgood.2
    obtain ⟨hat, -⟩ := hgood
    have hat : At t d.pc (facts A B N g d) := hat
    have hpc := hat.1
    have hfires : Fires t.pc ((code L A B N g).tmpl (some d) t) e (some u) := hfires
    cases d with
    | load =>
      have hgN : g < N := hi
      rw [tmpl_load_eq, hpc] at hfires
      obtain ⟨bs, hl, rfl, -⟩ := fires_load hpre hgN hat hfires
      refine ⟨bs, rfl, hl, fun v hv => ?_, rfl, hgN⟩
      simp [Code.toMachine, code, next, ncE, hv] at hn
    | store v =>
      have hgN : g < N := hi.1
      rw [tmpl_store_eq, hpc] at hfires
      obtain ⟨rfl, -⟩ := fires_store hpre hgN hi.2 hat hfires
      simp [Code.toMachine, code, next, wrE] at hn
    | exit =>
      rw [tmpl_exit_eq, hpc] at hfires
      cases hfires.2

/-- A position of a thread's trace at which the machine has stopped holds the undefined
behaviour after a read of bytes that are no word, and nothing else follows. -/
theorem dead_trace (hpre : Pre L A B N x mem0) {σ : (code L A B N g).toMachine.St}
    {es : List Event}
    (htr : (code L A B N g).toMachine.Trace σ es) :
    ∀ k e, es[k]? = some e → (code L A B N g).toMachine.after σ (es.take k) = none →
      σ = (some .load : Option Site) ∧ ∃ bs, bs.length = 4 ∧ (∀ v, rebuild 3 bs ≠ .ok v) ∧
        es.take k = [ncE A g bs] ∧ g < N := by
  induction htr with
  | nil σ => intro k e he; simp at he
  | @step σ σ' e es u hf hn _ ih =>
    intro k e' he' ha
    cases k with
    | zero => simp at ha
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some] at ha
      obtain ⟨hσ', -⟩ := ih j e' (by simpa using he') ha
      obtain ⟨t, hgood, hfires⟩ := hf
      cases σ with
      | none => subst hσ'; simp [Code.toMachine] at hn; cases hn
      | some d =>
        cases d <;> simp [Code.toMachine, code, next] at hn <;> (try split at hn) <;>
          (try split at hn) <;> simp_all
  | @last σ e hf =>
    intro k e' he' ha
    cases k with
    | zero => simp at ha
    | succ j => simp at he'
  | @dead σ e es u hf hn hlen hub =>
    intro k e' he' ha
    cases k with
    | zero => simp at ha
    | succ j =>
      obtain ⟨bs, hσ, hl, hv, rfl, hgN⟩ := fired_dead hpre hf hn
      have hj : j = 0 := by
        have := (List.getElem?_eq_some_iff.mp (by simpa using he' : es[j]? = some e')).1
        omega
      subst hj
      exact ⟨hσ, bs, hl, hv, by simp, hgN⟩

end
end PTX.Kernels.CopyLdg.Proof
