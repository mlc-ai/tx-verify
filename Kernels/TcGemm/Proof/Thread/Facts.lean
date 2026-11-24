-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Thread.Along
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # `tc_gemm`: the thread facts

At each site the instruction's template is its site's (`site_tmpl`), so its event is the site's
event (`site_event`). Along a thread's run its events so far are fixed by its state (`Along`, the
run invariant, proved by `Code.run_inv`). The machine never gives up (`tracked`); it stops only
after a read whose bytes give no column, after a store of a word that is not four bytes, and
after the exit, so an event after it stopped is undefined behaviour right after such a read
(`dead`). A pending thread fires its site's template (`fire`). `thread_facts` collects
`ThreadFacts`. -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}
  {X : Execution}

/-- The run invariant at the start. -/
theorem along_init : Along L A B D g (code L A B D g).init [] := by
  show Along L A B D g { site := if g / 32 = 0 then .alloc else .bar0 false, c := 0, vals := [] } []
  by_cases hw : g / 32 = 0
  · simp only [hw, ↓reduceIte]
    exact ⟨hw, rfl⟩
  · simp only [hw, ↓reduceIte]
    have hg0 : g ≠ 0 := by rintro rfl; exact hw rfl
    exact ⟨by simp [hg0], 0, by norm_num, by simp [headE, hg0, hw]⟩

/-- **The run invariant holds at every followed state.** -/
theorem along (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
    (hg : g < L.threads) {k : Nat} {d : ThreadD} (hσ : stateAt L A B D X g k = some (some d)) :
    Along L A B D g d ((X.tr g).take k) := by
  have htr := Frame.trace (C := code L A B D) (fun _ h => sound hpre h) hX hg
  refine Code.run_inv (sound hpre hg) htr (Along L A B D g) along_init ?_ k d hσ
  intro d d' pre e t ins o hJ hat hi hc hf hn
  exact along_step hpre hg hJ hat hi hc hf hn

/-- The machine never gives up a thread: a step continues in a state or stops. -/
theorem next_ne (d : ThreadD) (e : Event) : next g d e ≠ some none := by
  obtain ⟨s, c, vals⟩ := d
  cases s <;> simp only [next] <;> (repeat' split) <;> simp

/-- The machine follows every thread. -/
theorem tracked : Frame.Tracked (code L A B D) X :=
  Frame.tracked_of_next fun _ d e => next_ne d e

/-- **The event at a followed state** is its site's. -/
theorem event (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X) {k : Nat}
    {e : Event} {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : stateAt L A B D X g k = some (some d)) : SiteEvent L A B D g d e := by
  have hC : ∀ g < L.threads, (code L A B D g).Sound := fun _ h => sound hpre h
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := Frame.fired_site hC hX he hσ
  exact site_event hpre hg hat hi hc hf

/-- **An event after the machine stopped** is undefined behaviour right after a read whose bytes
give no column. -/
theorem dead (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X) {k : Nat}
    {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : stateAt L A B D X g k = none) : ∃ pc f bs, e = ⟨pc, .ub f⟩ ∧ 0 < k ∧
      X.get (g, k - 1) = some (rdE L.sharedBase bs) ∧ rdCol bs = none := by
  have hC : ∀ g < L.threads, (code L A B D g).Sound := fun _ h => sound hpre h
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨i, d, hi, hs, hs'⟩ := Frame.first_stop tracked hg hσ
  obtain ⟨ei, hei⟩ : ∃ ei, X.get (g, i) = some ei :=
    ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
  have hn : next g d ei = none := by
    rw [Frame.stateAt_succ hei, hs] at hs'
    exact hs'
  have hlast : ¬ Flow.Ends ei := fun hend => by
    have := end_last hX hei hend
    omega
  have hev := event hpre hX hg hei hs
  -- the stop is a read whose bytes give no column
  obtain ⟨bs, rfl, hbad⟩ : ∃ bs, ei = rdE L.sharedBase bs ∧ rdCol bs = none := by
    obtain ⟨s, c, vals⟩ := d
    cases s with
    | load z =>
      obtain ⟨bs, -, rfl⟩ := hev
      refine ⟨bs, rfl, ?_⟩
      cases hb : rdCol bs with
      | none => rfl
      | some c' => simp [next, rdE, hb] at hn
    | wait0 =>
      obtain ⟨ok, rfl⟩ := hev
      simp [next, wait0E] at hn
    | wait1 =>
      obtain ⟨ok, rfl⟩ := hev
      simp [next, wait1E] at hn
    | ld =>
      obtain ⟨vs, -, rfl⟩ := hev
      simp [next, ldE] at hn
    | st j =>
      rcases hev with ⟨-, rfl⟩ | ⟨-, f, rfl⟩
      · simp [next, stE] at hn
      · exact absurd (.inl ⟨f, rfl⟩) hlast
    | exit =>
      have hev : ei = exitE := hev
      subst hev
      exact absurd (.inr rfl) hlast
    | _ => simp [next] at hn
  -- the next event, at a dead state, is undefined behaviour, the last event
  have hi1 : i + 1 ≤ k := hi
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, i + 1) = some e1 :=
    ⟨_, List.getElem?_eq_getElem (show i + 1 < (X.tr g).length by omega)⟩
  obtain ⟨pc, f, rfl⟩ : ∃ pc f, e1 = ⟨pc, .ub f⟩ := by
    rcases Frame.fired hC hX he1 with ⟨σ, o, hσ1, -⟩ | ⟨-, h⟩
    · rw [hs'] at hσ1; cases hσ1
    · exact h
  have hend := end_last hX he1 (.inl ⟨f, rfl⟩)
  obtain rfl : k = i + 1 := by omega
  rw [he1] at he
  cases he
  exact ⟨pc, f, bs, rfl, by omega, by simpa using hei, hbad⟩

/-- **A pending thread fires its site's template** after local steps. -/
theorem fire (hpre : Pre L A B D a b mem0) {d : ThreadD} {t : TState} (hg : g < L.threads)
    (hσ : stateAt L A B D X g (X.tr g).length = some (some d))
    (hrun : Run kernel [] L g {} (X.tr g) (some t)) :
    ∃ t1 m, Relation.ReflTransGen (Tau kernel [] L g) t t1 ∧ t1.pc = d.site.pc ∧
      t1.sub = d.site.sub ∧ out kernel [] L g t1 = .ev m ∧ SiteTmpl L A B D g d m := by
  have hC : ∀ g < L.threads, (code L A B D g).Sound := fun _ h => sound hpre h
  obtain ⟨t1, ins, hl, hat, hi, hc, hout⟩ := Frame.end_at hC hg hrun hσ
  exact ⟨t1, _, hl, hat.1, hat.2.1, hout, site_tmpl hpre hg hat hi hc⟩

/-- **The thread facts of a consistent execution.** -/
theorem thread_facts (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X) :
    ThreadFacts L A B D X where
  sound := fun _ h => sound hpre h
  tracked := tracked
  event := fun hg he hσ => event hpre hX hg he hσ
  along := fun hg _ hσ => along hpre hX hg hσ
  dead := fun hg he hσ => dead hpre hX hg he hσ
  fire := fun hg hσ hrun => fire hpre hg hσ hrun

end
end PTX.Kernels.TcGemm.Proof
