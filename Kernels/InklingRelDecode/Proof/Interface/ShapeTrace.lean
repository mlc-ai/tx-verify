-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.All

@[expose] public section

/-!
# Walking a thread's trace

Generic facts about `Frame.stateAt`, the abstract state of a thread before its `k`-th event.

* `stateAt_pred`: a state that is not the machine's first state has a predecessor: an earlier index
  `k0 < k`, the event `e` of the trace at `k0`, the state `s0` before it, and `next s0 e` is the
  state. The index `k` may lie beyond the end of the trace (`stateAt` is then the last state), the
  predecessor is then the last event.
* `fired_cont`: an event at a followed state that is not an exit fires with a continuation (it is
  not undefined behaviour, `ThreadFacts.ub_stop`); `fired_of_followed`: so does every event that
  has a later event of the thread (an exit or a dead state's undefined behaviour is last).
* `next_ret_none`, `next_epiExit_none`: the thread machine's successor at the two exit states is
  `none`, so `Safety.Protocol.faultFree` as written (`next s e ≠ none` at every followed event) is
  false at an execution's exit events: it has to be restricted to events with a later event.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- **A state that is not the first has a predecessor.** -/
theorem stateAt_pred {k : Nat} {s : TSt} (h : St Q L X g k = some (some s))
    (hinit : s ≠ (code L Q g).init) :
    ∃ (k0 : Nat) (e : Event) (s0 : TSt), k0 < k ∧ (X.tr g)[k0]? = some e ∧
      St Q L X g k0 = some (some s0) ∧ (threadCode L g Q).next s0 e = some (some s) := by
  have key : ∀ k, k ≤ (X.tr g).length → St Q L X g k = some (some s) →
      ∃ (k0 : Nat) (e : Event) (s0 : TSt), k0 < k ∧ (X.tr g)[k0]? = some e ∧
        St Q L X g k0 = some (some s0) ∧ (threadCode L g Q).next s0 e = some (some s) := by
    intro k hk hs
    cases k with
    | zero =>
      rw [St, Frame.stateAt_zero] at hs
      exact absurd (Option.some.inj (Option.some.inj hs)).symm hinit
    | succ k0 =>
      obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      refine ⟨k0, e, ?_⟩
      have hs' := hs
      rw [St, Frame.stateAt_succ he] at hs'
      cases hk0 : St Q L X g k0 with
      | none => simp [St] at hk0 hs'; simp [hk0] at hs'
      | some σ =>
        cases σ with
        | none =>
          have : Frame.stateAt (code L Q) X g k0 = some none := hk0
          rw [this] at hs'
          simp [Code.toMachine] at hs'
        | some s0 =>
          have : Frame.stateAt (code L Q) X g k0 = some (some s0) := hk0
          rw [this] at hs'
          exact ⟨s0, by omega, he, rfl, hs'⟩
  by_cases hk : k ≤ (X.tr g).length
  · exact key k hk h
  · have h2 : St Q L X g (X.tr g).length = some (some s) := by
      exact (Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k) (by omega)).symm.trans h
    obtain ⟨k0, e, s0, hlt, he, hs0, hn⟩ := key _ le_rfl h2
    exact ⟨k0, e, s0, by omega, he, hs0, hn⟩

/-! ### An event of a followed state continues the thread -/

/-- The states that fire an exit: the epilogue's `ret` and the exit role's `ret`. -/
def ExitState : TSt → Prop
  | .d (.epi d) => d.site = .exit
  | .w (.exit x) => x.site = .ret
  | _ => False

/-- An event at a followed state that is not an exit continues the thread, when undefined
behaviour comes only after the machine stopped and an exit is fired from an exit state. -/
theorem fired_cont_of (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hX : Consistent L kernel asms mem0 X) {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) (hs : ¬ ExitState s)
    (hub : ∀ {pc f}, e = ⟨pc, .ub f⟩ → St Q L X g k = none ∨ St Q L X g k = some none)
    (hex : ∀ {pc}, e = ⟨pc, .exit⟩ → ExitState s) :
    ∃ u, (threadCode L g Q).toMachine.Fired (some s) e (some u) := by
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨o, hF⟩ := (Frame.trace hS hX hg).fired_at he' hσ
  cases o with
  | some u => exact ⟨u, hF⟩
  | none =>
    exfalso
    obtain ⟨t', -, hf'⟩ := hF
    obtain ⟨pc, kd⟩ := e
    rcases fires_none_ends hf' with ⟨fl, hu⟩ | hx
    · simp only at hu
      subst hu
      rcases hub rfl with h | h <;> rw [hσ] at h <;> cases h
    · simp only at hx
      subst hx
      exact hs (hex rfl)

/-- **An event at a followed state that is not an exit continues the thread.** The event is not
undefined behaviour (it comes only after the machine stopped), so it fired with a continuation. -/
theorem fired_cont (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some s)) (hs : ¬ ExitState s) :
    ∃ u, (threadCode L g Q).toMachine.Fired (some s) e (some u) :=
  fired_cont_of hf.sound hX hg he hσ hs (fun h => by subst h; exact hf.ub_stop hg he)
    (fun h => by
      subst h
      rcases exit_event_state hX hf.sound hf.tracked he with ⟨d', h, hd⟩ | ⟨x, h, hx⟩ <;>
        rw [hσ] at h <;> cases h <;> assumption)

/-! ### The last event of a thread -/

/-- **An event followed by another event continues the thread.** In a run of a machine, an event
that has a later event fired with a continuation (a `last` event is the last, and the events
after a dead state are only its undefined behaviour). -/
theorem _root_.PTX.Flow.Machine.Trace.fired_of_followed {K : Kernel} {A : List Assumption}
    {L : Launch} {g : Nat} {M : Machine K A L g} {σ : M.St} {es : List Event} (h : M.Trace σ es) :
    ∀ {j : Nat} {e e' : Event}, es[j]? = some e → es[j + 1]? = some e' →
      ∃ (τ : M.St) (u : TState), M.after σ (es.take j) = some τ ∧ M.Fired τ e (some u) := by
  induction h with
  | nil σ => intro j e e' hj; simp at hj
  | step hf hn _ ih =>
    intro j e e' hj hj1
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨_, _, rfl, hf⟩
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some]
      exact ih (by simpa using hj) (by simpa using hj1)
  | last hf =>
    intro j e e' hj hj1
    simp at hj1
  | dead hf hn hl _ =>
    intro j e e' hj hj1
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨_, _, rfl, hf⟩
    | succ j =>
      exfalso
      have h2 := (List.getElem?_eq_some_iff.mp (by simpa using hj1)).1
      omega

/-- **A followed event of a thread fired with a continuation.** If the thread has a later event,
its machine's state `s` before the event fires it with a continuation `u` (no undefined behaviour,
no exit: those events are last or after a stopped machine). -/
theorem fired_of_followed (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hX : Consistent L kernel asms mem0 X) {g k : Nat} {e e' : Event} {s : TSt}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (he' : (X.tr g)[k + 1]? = some e')
    (hσ : St Q L X g k = some (some s)) :
    ∃ u, (threadCode L g Q).toMachine.Fired (some s) e (some u) := by
  obtain ⟨τ, u, hτ, hF⟩ := (Frame.trace hS hX hg).fired_of_followed he he'
  have : τ = some s := Option.some.inj (hτ.symm.trans hσ)
  subst this
  exact ⟨u, hF⟩

/-- The thread-machine's `next` at the exit states is `none`: an exit event is the one followed
event after which no state follows, so a statement "`next ≠ none` at every followed event" is false
at it (`Safety.Protocol.faultFree` has to exclude it). -/
theorem next_ret_none {g : Nat} (P : Loader.Pro) (e : Event) :
    (threadCode L g Q).next (.w (.exit ⟨.ret, P⟩)) e = none := rfl

theorem next_epiExit_none {g : Nat} (d : Epi.D) (h : d.site = .exit) (e : Event) :
    (threadCode L g Q).next (.d (.epi d)) e = none := by
  rw [next_d]
  have : Epi.next d e = none := by
    unfold Epi.next
    rw [h]
  show ((Epi.next d e).map (Option.map DComp.St.epi)).map (Option.map TSt.d) = none
  rw [this]
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
