-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code
public import Lemmas.Flow.NotWait
public import Lemmas.Order.CausalThreadCount

@[expose] public section

/-! # Counting a thread's successful polls and arrivals

A proof tool. The successful polls and the arrivals a thread has made on one mbarrier
object, counted along its events, and how an event of a code machine's run changes the
counts. Protocol proofs match these counts with the counters of the object's records. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- Whether event `e` is a successful poll on `m`. -/
abbrev okPoll (m : Loc) (e : Event) : Bool := sourceWaitSuccess m e

/-- The successful polls on `m` among the events `es`. -/
def okPolls (m : Loc) (es : List Event) : Nat := es.countP (okPoll m)

theorem okPolls_snoc (m : Loc) (es : List Event) (e : Event) :
    okPolls m (es ++ [e]) = okPolls m es + if okPoll m e then 1 else 0 := by
  simp only [okPolls, List.countP_append, List.countP_singleton]

theorem okPoll_notWait {m : Loc} {e : Event} (h : ∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc) :
    okPoll m e = false := by
  unfold okPoll sourceWaitSuccess
  split
  · rename_i heq; exact absurd heq (h _ _ _ _ _)
  · rfl

theorem okPoll_wait {m l : Loc} {e : Event} {pc p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : e = ⟨pc, .wait l p ok acq sc⟩) : okPoll m e = (ok && decide (l = m)) := by
  subst he
  cases ok <;> simp [okPoll, sourceWaitSuccess]


/-- Whether event `e` is an arrival on `m`. -/
abbrev arrivesOn (m : Loc) (e : Event) : Bool := sourceArrive m e

/-- The arrivals on `m` among the events `es`. -/
def arrivals (m : Loc) (es : List Event) : Nat := es.countP (arrivesOn m)

/-- A thread with a successful poll on `m` among its first `k` events has one at some index. -/
theorem exists_okPoll {X : Execution} {g k : Nat} {m : Loc}
    (h : 0 < okPolls m ((X.tr g).take k)) :
    ∃ j pc p acq sc, j < k ∧ X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ := by
  obtain ⟨e, he, hok⟩ := List.countP_pos_iff.mp h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  rw [List.length_take] at hj
  have hget : X.get (g, j) = some (X.tr g)[j] := by
    show (X.tr g)[j]? = _
    exact List.getElem?_eq_getElem (by omega)
  rw [List.getElem_take] at hok
  generalize (X.tr g)[j] = ev at hok hget
  obtain ⟨pc, kind⟩ := ev
  cases kind
  case wait target p ok acq sc =>
    cases ok
    · simp [okPoll, sourceWaitSuccess] at hok
    · simp only [okPoll, sourceWaitSuccess, decide_eq_true_eq] at hok
      subst hok
      exact ⟨j, pc, p, acq, sc, by omega, hget⟩
  all_goals simp [okPoll, sourceWaitSuccess] at hok

theorem arrivals_snoc (m : Loc) (es : List Event) (e : Event) :
    arrivals m (es ++ [e]) = arrivals m es + if arrivesOn m e then 1 else 0 := by
  simp only [arrivals, List.countP_append, List.countP_singleton]

theorem arrivesOn_arrive {m l : Loc} {e : Event} {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : e = ⟨pc, .arrive l tx c rel sc⟩) : arrivesOn m e = decide (l = m) := by
  subst he
  rfl

theorem arrivesOn_notArrive {m : Loc} {e : Event}
    (h : ∀ l tx c rel sc, e.kind ≠ .arrive l tx c rel sc) : arrivesOn m e = false := by
  unfold arrivesOn sourceArrive
  split
  · rename_i heq; exact absurd heq (h _ _ _ _ _)
  · rfl

/-- An event fired from a state of a sound code machine is fired by the instruction at the
state's site. -/
theorem Code.fired_site {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {C : Code K A L g} (hC : C.Sound) {d : C.D} {e : Event} {o : Option TState}
    (hf : C.toMachine.Fired (some d) e o) :
    ∃ t ins, C.AtD d t ∧ C.inv d ∧ K.code[C.pc d]? = some ins ∧
      Fires (C.pc d) (eventTmpl A L g t ins.op) e o := by
  obtain ⟨t, ⟨hat, hinv⟩, hfire⟩ := hf
  change Fires t.pc (C.tmpl (some d) t) e o at hfire
  obtain ⟨ins, hc, -, -⟩ := (hC.steps d).site hinv
  simp only [Code.tmpl, hc] at hfire
  rw [hat.1] at hfire
  exact ⟨t, ins, hat, hinv, hc, hfire⟩

/-- An instruction that is not a poll leaves every poll count unchanged. -/
theorem okPoll_of_notPoll {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} {pc : Nat} {e : Event} {o : Option TState} {m : Loc}
    (hop : ∀ p b off par a s, op ≠ .mbarWait p b off par a s)
    (hf : Fires pc (eventTmpl A L g t op) e o) : okPoll m e = false :=
  okPoll_notWait (fires_notWait (eventTmpl_notWait hop) hf)

/-- An instruction that is not a poll leaves every poll count unchanged (`waitOp`). -/
theorem okPoll_of_waitOp {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} {pc : Nat} {e : Event} {o : Option TState} {m : Loc}
    (hop : waitOp op = false) (hf : Fires pc (eventTmpl A L g t op) e o) : okPoll m e = false :=
  okPoll_of_notPoll (waitOp_ne hop) hf

/-- An event after which the thread stops (an exit or a fault) is not a poll. -/
theorem fires_none_notWait {pc : Nat} {m : Tmpl} {e : Event} (hf : Fires pc m e none) :
    ∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc := by
  intro l p ok acq sc he
  cases m <;> simp only [Fires] at hf <;> aesop

end
end PTX.Flow
