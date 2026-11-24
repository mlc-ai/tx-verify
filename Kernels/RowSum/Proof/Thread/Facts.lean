-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Interface
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # `row_sum`: the thread facts of an execution

The run invariant of a thread: along its events, the counter of its state is the number of
events so far while it loads and stores, a thread of a row that exits has stored its accumulator
at position `K`, and when every read so far returned the launch content the accumulator is the
sum of the elements read. Every execution of the kernel has the facts the layers above use
(`ThreadFacts`). -/

namespace PTX.Kernels.RowSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The run invariant of a thread in state `d` after the events `pre`. -/
def RunFacts (A B M K : Nat) (x : Nat → ℝ) (g : Nat) (d : ThreadD) (pre : List Event) : Prop :=
  (d.site ≠ .exit → d.i = pre.length) ∧
  (d.site = .exit → g < M → d.i = K ∧ pre[K]? = some (wrE B g d.a)) ∧
  ((∀ j bs, pre[j]? = some (rdE A K g j bs) → bs = good x K g j) → d.a = accV x K g d.i)

theorem reads_of_snoc {pre : List Event} {e : Event}
    (h : ∀ j bs, (pre ++ [e])[j]? = some (rdE A K g j bs) → bs = good x K g j) :
    ∀ j bs, pre[j]? = some (rdE A K g j bs) → bs = good x K g j := by
  intro j bs hj
  apply h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]
  exact hj

theorem runFacts_init :
    RunFacts A B M K x g (code L A B M K g).init [] := by
  simp only [code]
  split_ifs with h1 h2
  · exact ⟨fun h => absurd rfl h, fun _ h => by omega, fun _ => by simp [accV]⟩
  · exact ⟨fun _ => rfl, fun h => by simp at h, fun _ => by simp [accV]⟩
  · exact ⟨fun _ => rfl, fun h => by simp at h, fun _ => by simp [accV]⟩

set_option maxHeartbeats 4000000 in
/-- Every event fired at a state keeps the run invariant at its successor. -/
theorem runFacts_step (hpre : Pre L A B M K x mem0) {d d' : ThreadD} {pre : List Event}
    {e : Event} {t : TState} {ins : Instr} {o : Option TState}
    (hq : RunFacts A B M K x g d pre) (hat : (code L A B M K g).AtD d t)
    (hinv : Inv M K g d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L A B M K g).next d e = some (some d')) :
    RunFacts A B M K x g d' (pre ++ [e]) := by
  have hev := site_event hpre hinv hat hc hf
  obtain ⟨s, i, a⟩ := d
  obtain ⟨hab, hl, hs⟩ := hinv
  cases s with
  | load =>
    obtain ⟨bs, rfl⟩ := hev
    obtain ⟨hi, hgM⟩ : i < K ∧ g < M := hl rfl
    have hip : i = pre.length := hq.1 (by simp)
    simp only [code, next, rdE] at hn
    cases hv : rebuild 3 bs with
    | error f => simp [hv] at hn
    | ok v =>
      cases ha : Assumption.readEReal .f32 a with
      | none => simp [hv, addAcc, ha] at hn
      | some ea =>
        cases ea with
        | error f => simp [hv, addAcc, ha] at hn
        | ok xr =>
          cases hb : Assumption.readEReal .f32 v with
          | none => simp [hv, addAcc, ha, hb] at hn
          | some eb =>
            cases eb with
            | error f => simp [hv, addAcc, ha, hb] at hn
            | ok y =>
              cases hr0 : Assumption.addEReal xr y with
              | none => simp [hv, addAcc, ha, hb, hr0] at hn
              | some r' =>
                simp only [hv, addAcc, ha, hb, hr0] at hn
                obtain rfl := Option.some.inj (Option.some.inj hn)
                refine ⟨fun _ => by simp [hip], fun h => ?_, fun hgood => ?_⟩
                · split_ifs at h
                · have hq3 : a = accV x K g i := hq.2.2 (reads_of_snoc hgood)
                  have hbs : bs = good x K g i := by
                    apply hgood i bs
                    rw [hip, List.getElem?_append_right (by omega)]
                    simp [rdE, gA]
                  have hx : xr = (S K x g i : EReal) := by
                    rw [hq3, readEReal_of_valFloat (valFloat_accV x K g i)] at ha
                    exact (Except.ok.inj (Option.some.inj ha)).symm
                  have hv1 : v = fl (x (K * g + i)) := by
                    rw [hbs, good_rebuild] at hv
                    exact (Except.ok.inj hv).symm
                  have hy : y = (x (K * g + i) : EReal) := by
                    rw [hv1, readEReal_of_valFloat (valFloat_fl _)] at hb
                    exact (Except.ok.inj (Option.some.inj hb)).symm
                  have hadd : Assumption.addEReal (S K x g i : EReal)
                      ((x (K * g + i) : ℝ) : EReal) =
                        some ((S K x g i + x (K * g + i) : ℝ) : EReal) := by
                    rw [Assumption.addEReal, ite_eq_right (by simp)]
                    push_cast
                    ring
                  have hval : Assumption.erealValue .f32
                      ((S K x g i + x (K * g + i) : ℝ) : EReal) =
                        .float .f32 (S K x g i + x (K * g + i)) := by
                    unfold Assumption.erealValue
                    rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
                      EReal.toReal_coe]
                  rw [hx, hy, hadd] at hr0
                  obtain rfl := Option.some.inj hr0
                  rw [hval]
                  simp only [accV, Nat.succ_ne_zero, ↓reduceIte, S_succ, fl]
  | store =>
    obtain rfl := hev
    obtain ⟨hiK, hgM⟩ : i = K ∧ g < M := hs rfl
    have hip : i = pre.length := hq.1 (by simp)
    simp only [code, next] at hn
    obtain rfl := Option.some.inj (Option.some.inj hn)
    refine ⟨fun h => absurd rfl h, fun _ _ => ⟨hiK, ?_⟩, fun hgood => ?_⟩
    · rw [List.getElem?_append_right (by omega), show K - pre.length = 0 by omega]
      rfl
    · refine hq.2.2 (reads_of_snoc hgood)
  | exit => simp [code, next] at hn

/-- **The run invariant holds along every run of a thread.** -/
theorem runFacts (hpre : Pre L A B M K x mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L A B M K g).toMachine.Trace (some (code L A B M K g).init) es) :
    ∀ j d, (code L A B M K g).toMachine.after (some (code L A B M K g).init) (es.take j) =
      some (some d) → RunFacts A B M K x g d (es.take j) :=
  Code.run_inv (sound hpre hg) htr (RunFacts A B M K x g) runFacts_init
    fun hq hat hinv hc hf hn => runFacts_step hpre hq hat hinv hc hf hn

/-! ### The facts of the interface -/

theorem next_ne (d : ThreadD) (e : Event) : (code L A B M K g).next d e ≠ some none := by
  obtain ⟨s, i, a⟩ := d
  cases s <;> simp only [code, next] <;> (try split) <;> (try split) <;> (try split) <;> simp

theorem tracked : Frame.Tracked (codes L A B M K) X :=
  Frame.tracked_of_next fun _ d e => next_ne d e

/-- The prefix of a trace holds the events before its end. -/
theorem take_get {es : List Event} {k j : Nat} {r : Event} (h : (es.take k)[j]? = some r) :
    es[j]? = some r := by
  rw [List.getElem?_take] at h
  split_ifs at h
  · exact h

/-- Before event `k` of a followed thread, the machine's counter and the events so far satisfy the
run invariant. -/
theorem state_facts (hpre : Pre L A B M K x mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {d : ThreadD}
    (hσ : stateAt L A B M K X g k = some (some d)) :
    RunFacts A B M K x g d ((X.tr g).take k) :=
  runFacts hpre hg (Frame.trace (fun _ hg => sound hpre hg) hX hg) k d hσ

/-- **A followed thread's event is its state's event.** -/
theorem event_at (hpre : Pre L A B M K x mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : stateAt L A B M K X g k = some (some d)) : EventAt A B M K g k d e := by
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site (fun g hg => sound hpre hg) hX he hσ
  have hev := site_event hpre hinv hat hc hf
  have hq := state_facts hpre hX hg hσ
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hlen : ((X.tr g).take k).length = k := by simp; omega
  obtain ⟨s, i, a⟩ := d
  obtain ⟨hab, hl, hs⟩ := hinv
  cases s with
  | load =>
    obtain ⟨bs, rfl⟩ := hev
    obtain ⟨hi, hgM⟩ : i < K ∧ g < M := hl rfl
    have hik : i = k := by rw [← hlen]; exact hq.1 (by simp)
    subst hik
    exact .inl ⟨rfl, hgM, hi, rfl, bs, rfl⟩
  | store =>
    obtain rfl := hev
    obtain ⟨hiK, hgM⟩ : i = K ∧ g < M := hs rfl
    have hik : i = k := by rw [← hlen]; exact hq.1 (by simp)
    exact .inr (.inl ⟨rfl, hgM, by omega, hiK, rfl⟩)
  | exit => exact .inr (.inr ⟨rfl, hev⟩)

/-- The machine of a thread stops only at a read. -/
theorem trace_dead_at {K' : Kernel} {A' : List Assumption} {L' : Launch} {g' : Nat}
    {M' : Machine K' A' L' g'} {σ : M'.St} {es : List Event} (h : M'.Trace σ es) {j : Nat}
    (hj : j < es.length) (hn : M'.after σ (es.take j) = none) :
    ∃ i τ e' u, i + 1 = j ∧ M'.after σ (es.take i) = some τ ∧ es[i]? = some e' ∧
      M'.Fired τ e' (some u) ∧ M'.next τ e' = none := by
  induction h generalizing j with
  | nil σ => simp at hj
  | @step σ σ' e es' u hf hn' _ ih =>
    cases j with
    | zero => simp at hn
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn', Option.bind_some] at hn
      obtain ⟨i, τ, e', u', hij, h1, h2, h3, h4⟩ := ih (by simpa using hj) hn
      refine ⟨i + 1, τ, e', u', by omega, ?_, ?_, h3, h4⟩
      · simp only [List.take_succ_cons, Machine.after_cons, hn', Option.bind_some, h1]
      · simpa using h2
  | @last σ e hf =>
    cases j with
    | zero => simp at hn
    | succ j => simp at hj
  | @dead σ e es' u hf hn' hlen hub =>
    cases j with
    | zero => simp at hn
    | succ j =>
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      exact ⟨0, σ, e, u, rfl, rfl, rfl, hf, hn'⟩

/-- **The machine stops only after a read of bytes that are not the launch content**, and the
thread's next event is its undefined behaviour. -/
theorem dead_facts (hpre : Pre L A B M K x mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : stateAt L A B M K X g k = none) :
    ∃ pc f j bs, e = ⟨pc, .ub f⟩ ∧ k = j + 1 ∧ X.get (g, j) = some (rdE A K g j bs) ∧
      bs ≠ good x K g j := by
  have hC : ∀ g < L.threads, (codes L A B M K g).Sound := fun g hg => sound hpre hg
  obtain ⟨pc, f, rfl⟩ : ∃ pc f, e = ⟨pc, .ub f⟩ := by
    rcases Frame.fired hC hX he with ⟨σ, o, h1, -⟩ | ⟨-, h⟩
    · have h1' : Frame.stateAt (codes L A B M K) X g k = none := hσ
      rw [h1'] at h1
      cases h1
    · exact h
  have htr := Frame.trace hC hX hg
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨i, τ, e', u, hik, h1, h2, hfired, h3⟩ := trace_dead_at htr hk hσ
  cases τ with
  | none => simp [Code.toMachine] at h3
  | some d =>
    obtain ⟨t, ins, hat, hinv, hc, hf⟩ := Frame.fired_site_of hC hg hfired
    have hev := site_event hpre hinv hat hc hf
    have hq := runFacts hpre hg htr i d h1
    have hlen : ((X.tr g).take i).length = i := by simp; omega
    obtain ⟨s, i', a⟩ := d
    obtain ⟨⟨hab, s0, hs0⟩, hl, hs⟩ := hinv
    cases s with
    | load =>
      obtain ⟨bs, rfl⟩ := hev
      have hii : i' = i := by rw [← hlen]; exact hq.1 (by simp)
      subst hii
      refine ⟨pc, f, i', bs, rfl, by omega, h2, fun hb => ?_⟩
      subst hb
      change next K ⟨.load, i', a⟩ (rdE A K g i' (good x K g i')) = none at h3
      have hne : addAcc a (fl (x (K * g + i'))) ≠ none := by
        rw [addAcc, hs0, readEReal_of_valFloat (valFloat_fl _)]
        rcases s0 with _ | _ | s0 <;> simp [Assumption.addEReal]
      simp only [next, rdE, good_rebuild] at h3
      cases hacc : addAcc a (fl (x (K * g + i'))) with
      | none => exact hne hacc
      | some a' => rw [hacc] at h3; simp at h3
    | store =>
      change next K ⟨.store, i', a⟩ e' = none at h3
      simp [next] at h3
    | exit =>
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
      simp [eventTmpl, Fires] at hf

/-- **The accumulator of a followed thread** is the sum of the elements it has read. -/
theorem value_facts (hpre : Pre L A B M K x mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hσ : stateAt L A B M K X g k = some (some d))
    (hreads : ∀ j bs, X.get (g, j) = some (rdE A K g j bs) → bs = good x K g j) :
    d.a = accV x K g d.i :=
  (state_facts hpre hX hg hσ).2.2 fun j bs h => hreads j bs (take_get h)

/-- The exit of a thread of a row follows its store at position `K`. -/
theorem exit_write_facts (hpre : Pre L A B M K x mem0) (hX : Consistent L kernel Prod mem0 X)
    {g : Nat} (hg : g < L.threads) (hgM : g < M) (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩)
      :
    ∃ a, X.get (g, K) = some (wrE B g a) ∧
      ((∀ j bs, X.get (g, j) = some (rdE A K g j bs) → bs = good x K g j) → a = accV x K g K) := by
  obtain ⟨pc, hl⟩ := hex
  rw [List.getLast?_eq_getElem?] at hl
  have hp : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := hl
  have hσ : ∃ d, stateAt L A B M K X g ((X.tr g).length - 1) = some (some d) := by
    cases hs : stateAt L A B M K X g ((X.tr g).length - 1) with
    | none =>
      obtain ⟨pc', f, -, -, he, -⟩ := dead_facts hpre hX hg hp hs
      simp at he
    | some σ =>
      cases σ with
      | none => exact absurd hs (tracked _ _ hg)
      | some d => exact ⟨d, rfl⟩
  obtain ⟨d, hd⟩ := hσ
  have hq := state_facts hpre hX hg hd
  rcases event_at hpre hX hg hp hd with ⟨-, -, -, -, bs, he⟩ | ⟨-, -, -, -, he⟩ | ⟨hsite, -⟩
  · simp [rdE] at he
  · simp [wrE] at he
  obtain ⟨hiK, hw⟩ := hq.2.1 hsite hgM
  refine ⟨d.a, take_get hw, fun hreads => ?_⟩
  have := hq.2.2 fun j bs h => hreads j bs (take_get h)
  rw [hiK] at this
  exact this

/-- The first instruction of every thread is not a barrier. -/
theorem init_not_bar (g : Nat) :
    ∀ ins, kernel.code[(codes L A B M K g).pc (codes L A B M K g).init]? = some ins →
      ins.op.isBar = false := by
  intro ins h
  change kernel.code[(code L A B M K g).init.site.pc]? = some ins at h
  simp only [code] at h
  split_ifs at h
  · obtain rfl := Option.some.inj (h.symm.trans Flow.code_exit_0); rfl
  · obtain rfl := Option.some.inj (h.symm.trans Flow.code_store_0); rfl
  · obtain rfl := Option.some.inj (h.symm.trans Flow.code_load_0); rfl

/-- **Every execution of the kernel has the thread facts.** -/
theorem threadFacts (hpre : Pre L A B M K x mem0) (hX : Consistent L kernel Prod mem0 X) :
    ThreadFacts L A B M K x X where
  tracked := tracked
  event := fun hg he hs => event_at hpre hX hg he hs
  dead := fun hg he hs => dead_facts hpre hX hg he hs
  value := fun hg hs hr => value_facts hpre hX hg hs hr
  exit_write := fun hg hgM hex => exit_write_facts hpre hX hg hgM hex

/-- **The machines of a launch satisfying the precondition.** -/
theorem codeFacts (hpre : Pre L A B M K x mem0) : CodeFacts L A B M K where
  sound := fun _ hg => sound hpre hg
  init_not_bar := init_not_bar

end
end PTX.Kernels.RowSum.Proof
