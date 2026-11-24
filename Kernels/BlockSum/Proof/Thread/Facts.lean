-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Interface
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # The thread facts

Each event of a followed thread is its state's site event (`site_event`). Along a thread's run
one invariant holds (`RunFacts`): the state's invariant, the position of its event, that only
thread 0 of a CTA reduces, the loaded value of the input load, and the sum of the cells read so
far. `thread_facts` proves the interface's `ThreadFacts` from it. -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {g : Nat}

/-- **The event of a site.** -/
theorem site_event (hpre : Pre L A B x mem0) (hg : g < L.threads) {d : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hat : At t d.site.pc (facts A B L g d))
    (hi : Inv d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) : SiteEvent A B L g d e := by
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s with
  | input =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    rw [tmpl_input hpre hg hat] at hf
    obtain ⟨bs, -, rfl, -⟩ := hf
    exact ⟨bs, rfl⟩
  | share =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    rw [tmpl_share hpre hat, storeValue_of_bytes (hi.share rfl)] at hf
    exact hf.1
  | bar =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
    rw [tmpl_bar] at hf
    exact hf.1
  | sum =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_1)
    rw [tmpl_sum hpre (hi.sum rfl).1 hat] at hf
    obtain ⟨bs, -, rfl, -⟩ := hf
    exact ⟨bs, rfl⟩
  | out =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_1)
    rw [tmpl_out hpre hg (hi.out rfl).1 hat] at hf
    exact hf.1
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    rw [tmpl_exit] at hf
    exact hf.1

/-- The run invariant of a thread at abstract state `d` after events `es`. -/
def RunFacts (A : Nat) (g : Nat) (d : D) (es : List Event) : Prop :=
  Inv d ∧ es.length = d.idx g ∧ ((d.site = .sum ∨ d.site = .out) → g % 256 = 0) ∧
  (d.site ≠ .input → ∃ bs, es[0]? =
    some ⟨Flow.load_0, .rd { loc := gl (A + 4 * g), size := 4 } bs⟩ ∧ rebuild 3 bs = .ok d.v) ∧
  ((d.site = .sum ∨ d.site = .out) → d.s = ∑ j ∈ Finset.range d.i, rdVal es[3 + j]?)

theorem getElem?_snoc_lt {pre : List Event} {e : Event} {j : Nat} (h : j < pre.length) :
    (pre ++ [e])[j]? = pre[j]? :=
  List.getElem?_append_left h

/-- One step of the run invariant. -/
theorem runFacts_step (hpre : Pre L A B x mem0) (hg : g < L.threads) {d d' : D}
    {pre : List Event} {e : Event} {t : TState} {ins : Instr} {o : Option TState}
    (hJ : RunFacts A g d pre) (hat : At t d.site.pc (facts A B L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : next g d e = some (some d')) : RunFacts A g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hz, hin, hsum⟩ := hJ
  have hev := site_event hpre hg hat hi hc hf
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s with
  | input =>
    obtain ⟨bs, rfl⟩ := hev
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hlen
    subst hnil
    simp only [next] at hn
    cases hv : rebuild 3 bs with
    | error f => simp [hv] at hn
    | ok w =>
      simp only [hv] at hn
      split_ifs at hn with hw
      cases hn
      refine ⟨⟨fun _ => hw, by simp, by simp⟩, rfl, by simp, fun _ => ⟨bs, rfl, hv⟩, by simp⟩
  | share =>
    cases hn
    refine ⟨⟨by simp, by simp, by simp⟩, by simp [hlen, D.idx], by simp, fun _ => ?_, by simp⟩
    obtain ⟨bs, h0, hv⟩ := hin (by simp)
    exact ⟨bs, by rw [getElem?_snoc_lt (by simp [hlen, D.idx])]; exact h0, hv⟩
  | bar =>
    simp only [next] at hn
    split_ifs at hn with hg0
    · cases hn
      refine ⟨⟨by simp, fun _ => ⟨by simp, readEReal_of_valFloat valFloat_zero⟩, by simp⟩,
        by simp [hlen, D.idx],
        fun _ => hg0, fun _ => ?_, fun _ => by simp⟩
      obtain ⟨bs, h0, hv⟩ := hin (by simp)
      exact ⟨bs, by rw [getElem?_snoc_lt (by simp [hlen, D.idx])]; exact h0, hv⟩
    · cases hn
      refine ⟨⟨by simp, by simp, by simp⟩, by simp [hlen, D.idx, hg0], by simp, fun _ => ?_,
        by simp⟩
      obtain ⟨bs, h0, hv⟩ := hin (by simp)
      exact ⟨bs, by rw [getElem?_snoc_lt (by simp [hlen, D.idx])]; exact h0, hv⟩
  | sum =>
    obtain ⟨hi256, hacc⟩ := hi.sum rfl
    simp only at hi256 hacc
    obtain ⟨bs, rfl⟩ := hev
    simp only [next] at hn
    cases hy : readVal bs with
    | none => simp [hy] at hn
    | some y =>
      simp only [hy] at hn
      cases hr : Assumption.addEReal sm y with
      | none => simp [hr] at hn
      | some r =>
        simp only [hr] at hn
        have hlen' : pre.length = 3 + i := hlen
        have hs' : r = ∑ j ∈ Finset.range (i + 1), rdVal (pre ++ [⟨Flow.load_1,
            .rd { loc := sh (g / 256) (L.sharedBase + 4 * i), size := 4 } bs⟩])[3 + j]? := by
          have hsr : r = sm + y := by
            have h2 : Assumption.addEReal sm y = some (sm + y) := by
              rw [Assumption.addEReal, ite_eq_right]
              intro hc
              rw [Assumption.addEReal, ite_eq_left hc] at hr
              cases hr
            rw [h2] at hr
            exact (Option.some.inj hr).symm
          have hsum' : sm = ∑ j ∈ Finset.range i, rdVal pre[3 + j]? := hsum (.inl rfl)
          rw [hsr, Finset.sum_range_succ, hsum']
          congr 1
          · refine Finset.sum_congr rfl fun j hj => ?_
            rw [getElem?_snoc_lt (by simp at hj; omega)]
          · rw [List.getElem?_append_right (by omega)]
            simp [hlen', rdVal, hy]
        have hin' : ∃ bs', (pre ++ [⟨Flow.load_1,
            .rd { loc := sh (g / 256) (L.sharedBase + 4 * i), size := 4 } bs⟩])[0]? =
            some ⟨Flow.load_0, .rd { loc := gl (A + 4 * g), size := 4 } bs'⟩ ∧
              rebuild 3 bs' = .ok v := by
          obtain ⟨bs', h0, hv⟩ := hin (by simp)
          exact ⟨bs', by rw [getElem?_snoc_lt (by omega)]; exact h0, hv⟩
        split_ifs at hn with hlt
        · cases hn
          exact ⟨⟨by simp, fun _ => ⟨hlt, readEReal_erealValue r⟩, by simp⟩,
            by simp [hlen', D.idx]; omega, fun _ => hz (.inl rfl), fun _ => hin',
            fun _ => hs'⟩
        · cases hn
          exact
            ⟨⟨by simp, by simp, fun _ => ⟨rfl, show i + 1 = 256 by omega⟩⟩,
              by simp [hlen', D.idx]; omega,
            fun _ => hz (.inl rfl), fun _ => hin', fun _ => hs'⟩
  | out =>
    cases hn
    have hg0 := hz (.inr rfl)
    refine ⟨⟨by simp, by simp, by simp⟩, by simp [hlen, D.idx, hg0], by simp, fun _ => ?_,
      by simp⟩
    obtain ⟨bs, h0, hv⟩ := hin (by simp)
    exact ⟨bs, by rw [getElem?_snoc_lt (by simp [hlen, D.idx])]; exact h0, hv⟩
  | exit => simp [next] at hn

variable {X : Execution}

/-- **The run invariant holds at every followed state.** -/
theorem run_facts (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {d : D} (hσ : stateAt A B L X g k = some (some d)) :
    RunFacts A g d ((X.tr g).take k) := by
  have htr := (sound hpre hg).machine.produces (hX.thr g hg)
  have h0 : RunFacts A g { site := .input } [] :=
    ⟨⟨by simp, by simp, by simp⟩, rfl, by simp, by simp, by simp⟩
  refine Code.run_inv (sound hpre hg) htr (RunFacts A g) h0 ?_ k d hσ
  intro d d' pre e t ins o hJ hat _ hc hf hn
  exact runFacts_step hpre hg hJ hat hc hf hn

/-- The machine never gives up a thread: a step continues in a state or stops. -/
theorem next_ne (g : Nat) (d : D) (e : Event) : next g d e ≠ some none := by
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s <;> simp only [next] <;> (repeat' split) <;> simp


/-- **No event of the kernel is an atomic read-modify-write**: every event is the event of a
site, or the undefined behaviour that follows a stopped machine. -/
theorem no_rmw (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    {e : EvId} {a : Acc} {old : List (Option Byte)} {new : Option (List Byte)} :
    ¬ X.Rmw e a old new := by
  rintro ⟨pc, he⟩
  have hg := Frame.lt_of_get hX he
  have htr := (sound hpre hg).machine.produces (hX.thr _ hg)
  rcases htr.fired he with ⟨τ, o, ha, -⟩ | ⟨-, hub⟩
  · cases τ with
    | none =>
      exact absurd ha (Frame.tracked_of_next (C := codes A B L)
        (fun g d e => next_ne g d e) e.1 e.2 hg)
    | some d =>
      have hσ : stateAt A B L X e.1 e.2 = some (some d) := ha
      obtain ⟨t, ins, o', hat, hinv, hc, hf⟩ :=
        Frame.fired_site (C := codes A B L) (fun _ => sound hpre) hX he hσ
      have hi := hinv
      obtain ⟨s, v, i, acc, sm⟩ := d
      cases s with
      | input =>
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
        rw [tmpl_input hpre hg hat] at hf
        obtain ⟨bs, -, hk, -⟩ := hf
        simp at hk
      | share =>
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
        rw [tmpl_share hpre hat, storeValue_of_bytes (hi.share rfl)] at hf
        obtain ⟨hk, -⟩ := hf
        simp at hk
      | bar =>
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
        rw [tmpl_bar] at hf
        obtain ⟨hk, -⟩ := hf
        simp at hk
      | sum =>
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_1)
        rw [tmpl_sum hpre (hi.sum rfl).1 hat] at hf
        obtain ⟨bs, -, hk, -⟩ := hf
        simp at hk
      | out =>
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_1)
        rw [tmpl_out hpre hg (hi.out rfl).1 hat] at hf
        obtain ⟨hk, -⟩ := hf
        simp at hk
      | exit =>
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
        rw [tmpl_exit] at hf
        obtain ⟨hk, -⟩ := hf
        simp at hk
  · obtain ⟨pc', f, hk⟩ := hub
    cases hk

/-- **The thread facts of a consistent execution.** -/
theorem thread_facts (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X) :
    ThreadFacts A B L X := by
  have hC : ∀ g < L.threads, (codes A B L g).Sound := fun g hg => sound hpre hg
  have ht : Frame.Tracked (codes A B L) X := Frame.tracked_of_next fun g d e => next_ne g d e
  refine ⟨ht, fun hg hσ => (run_facts hpre hX hg hσ).1, ?_, ?_,
    fun hg hσ => (run_facts hpre hX hg hσ).2.2.1, ?_, ?_, ?_, ?_⟩
  · intro g k e d hg he hσ
    obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hC hX he hσ
    exact site_event hpre hg hat hinv hc hf
  · intro g k d hg hk hσ
    have h := (run_facts hpre hX hg hσ).2.1
    rwa [List.length_take, Nat.min_eq_left hk] at h
  · intro g k d hg hσ hne
    obtain ⟨-, hlen, -, hin, -⟩ := run_facts hpre hX hg hσ
    obtain ⟨bs, h0, hv⟩ := hin hne
    have hk : 0 < k := by
      have : 0 < d.idx g := by
        obtain ⟨s, v, i, acc, sm⟩ := d
        cases s <;> simp [D.idx] at hne ⊢
        split <;> omega
      rw [List.length_take] at hlen
      omega
    refine ⟨bs, ?_, hv⟩
    rw [List.getElem?_take, ite_eq_left hk] at h0
    exact h0
  · intro g k d hg hσ hs
    obtain ⟨hi, hlen, -, -, hsum⟩ := run_facts hpre hX hg hσ
    rw [hsum hs]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < d.i := Finset.mem_range.mp hj
    have hlt : 3 + j < k := by
      rw [List.length_take] at hlen
      rcases hs with hs | hs
      · simp only [D.idx, hs] at hlen; omega
      · have := (hi.out hs).2
        simp only [D.idx, hs] at hlen; omega
    rw [List.getElem?_take, ite_eq_left hlt]
    rfl
  · intro g k hg hk hσ
    obtain ⟨j, d, hj, hσj, hσj'⟩ := Frame.first_stop ht hg hσ
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e :=
      ⟨_, List.getElem?_eq_getElem (show j < (X.tr g).length by omega)⟩
    refine ⟨j, d, e, hj, hσj, he, ?_⟩
    have hn : next g d e = none := by
      rw [Frame.stateAt_succ he, hσj] at hσj'
      exact hσj'
    obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hC hX he hσj
    have hev := site_event hpre hg hat hinv hc hf
    obtain ⟨s, v, i, acc, sm⟩ := d
    cases s with
    | input =>
      obtain ⟨bs, rfl⟩ := hev
      refine .inr ⟨_, _, bs, rfl, .inl ⟨rfl, fun w hw hb => ?_⟩⟩
      simp [next, hw, hb] at hn
    | share => simp [next] at hn
    | bar => simp only [next] at hn; split_ifs at hn
    | sum =>
      obtain ⟨bs, rfl⟩ := hev
      refine .inr ⟨_, _, bs, rfl, .inr ⟨rfl, ?_⟩⟩
      intro y hy
      simp only [next, hy] at hn
      cases hr : Assumption.addEReal sm y with
      | none => rfl
      | some r =>
        simp only [hr] at hn
        split_ifs at hn
    | out => simp [next] at hn
    | exit => exact .inl rfl
  · intro g k pc f hg he
    rcases Code.ub_stopped (hC g hg) (tmplOk hpre hg) (hX.thr g hg) he with h | h
    · exact h
    · exact absurd h (ht g k hg)

end
end PTX.Kernels.BlockSum.Proof
