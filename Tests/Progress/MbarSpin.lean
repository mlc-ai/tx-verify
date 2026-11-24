-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Progress.Common
public import Lemmas.Kernel.Correct
public import Lemmas.MBarrier.MBarrierPhase
public import Lemmas.MBarrier.MBarrierInitOrder
public import Lemmas.Clc.ClcExecution

@[expose] public section

/-!
# Deadlock test: an mbarrier spin whose phase never completes (DEP-ORDER, OBJ-MBAR-HISTORY)

One thread initializes the mbarrier `M` with expected count 2, arrives on it once and spins on
it with `try_wait` for phase 0, which needs a second arrival that never comes:

```
add.u32 %r1, M, 0;
mbarrier.init.shared::cta.b64 [%r1], 2;
mbarrier.arrive.shared::cta.b64 _, [%r1];
L: mbarrier.try_wait.parity.shared::cta.b64 %p0, [%r1], 0;
@!%p0 bra L;
exit;
```

`spin_deadlock` proves that the program has a possible execution that cannot grow and is not
complete, which is how CORRECT-PROGRESS rejects it. Failed polls do not count towards the size of
an execution, so the bound of `deadlock_of_bound` holds: every trace is the initialization, the
arrival and the spin (`thread_trace`), with at most four counted events. No possible execution
has a successful poll (`no_ok_poll`): the poll's record follows the initialization in the
history of `M` (it is published by program order), so it does not fault, and the arrival
accounting of the history (`CheckedLog.accounted`) keeps the phase at 0 with one arrival unit
of the two the phase expects. So no possible execution reaches the exit.
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

namespace MbarSpin

/-- One CTA of one thread. -/
def L1 : Launch := { grid := 1, block := 1, params := fun _ => none }

/-- The program; register 1 holds the address of `M`, predicate register 0 the poll result. -/
def spinK : Kernel where
  name := "spin"
  params := []
  sharedBytes := 16
  code := [
    { op := .int ⟨.add, .int .u 32, false, [some 1], [.sharedSym 0, .imm 0]⟩ },
    { op := .mbarInit 1 0 (.imm 2) },
    { op := .mbarArrive 1 0 (.imm 0) },
    { op := .mbarWait 0 1 0 (.imm 0) },
    { guard := some (0, true), op := .bra 3 false },
    { op := .exit }]

/-- The mbarrier at shared offset 0. -/
def M : Loc := ⟨.shared, 0, 0⟩

/-- The state after a local step, and the continuations of the event templates. -/
def tauOf : Out → TState
  | .tau t => t
  | _ => {}
def evNext : Out → TState
  | .ev (.mbInit _ _ t) | .ev (.arrive _ _ t ..) => t
  | _ => {}
def pollK : Out → Bool → TState
  | .ev (.wait _ _ k ..) => k
  | _ => fun _ => {}

/-- The states of the thread before the initialization, the arrival and the first poll. -/
def t1 : TState := tauOf (out spinK [] L1 0 {})
def t2 : TState := evNext (out spinK [] L1 0 t1)
def t3 : TState := evNext (out spinK [] L1 0 t2)
/-- The state at the poll after one failed poll. -/
def s : TState := tauOf (out spinK [] L1 0 (pollK (out spinK [] L1 0 t3) false))

/-- A failed poll at `s` returns to `s`. -/
theorem s_fix : tauOf (out spinK [] L1 0 (pollK (out spinK [] L1 0 s) false)) = s := by
  have h1 : tauOf (out spinK [] L1 0 (pollK (out spinK [] L1 0 s) false)) =
      { s with regs := Function.update s.regs 0 (some (.pred false)) } := rfl
  rw [h1, show some (Value.pred false) = s.regs 0 from rfl, Function.update_eq_self]

/-! ## The traces of the thread -/

/-- The events of the thread. -/
def eInit : Event := ⟨1, .mbInit M 2⟩
def eArr : Event := ⟨2, .arrive M 0 1 true .cta⟩
def poll (ok : Bool) : Event := ⟨3, .wait M 0 ok true .cta⟩
def eExit : Event := ⟨5, .exit⟩

/-- The traces of the spin from the poll: failed polls, then possibly the successful poll and
the exit. -/
def LoopTrace (tr : List Event) : Prop :=
  ∃ n, tr = List.replicate n (poll false) ∨ tr = List.replicate n (poll false) ++ [poll true] ∨
    tr = List.replicate n (poll false) ++ [poll true, eExit]

theorem LoopTrace.mem {l : List Event} (h : LoopTrace l) {x : Event} (hx : x ∈ l) :
    ∃ ok, x = poll ok ∨ x = eExit := by
  have : x = poll false ∨ x = poll true ∨ x = eExit := by
    obtain ⟨n, rfl | rfl | rfl⟩ := h <;> simp [List.mem_replicate] at hx <;> tauto
  rcases this with h | h | h
  · exact ⟨false, .inl h⟩
  · exact ⟨true, .inl h⟩
  · exact ⟨true, .inr h⟩

theorem LoopTrace.cons {l : List Event} (h : LoopTrace l) : LoopTrace (poll false :: l) := by
  obtain ⟨n, h | h | h⟩ := h <;> refine ⟨n + 1, ?_⟩ <;> simp [h, List.replicate_succ]

/-- Every run from a poll of the spin, whose failure returns to the poll at `s` and whose
success leads to the exit, is a `LoopTrace`. -/
theorem loop (n : Nat) : ∀ (u : TState) (k : Bool → TState) (tr : List Event)
    (o : Option TState), tr.length ≤ n → u.pc = 3 →
    out spinK [] L1 0 u = .ev (.wait M 0 k true .cta) →
    out spinK [] L1 0 (k false) = .tau s →
    (∃ u', out spinK [] L1 0 (k true) = .tau u' ∧ out spinK [] L1 0 u' = .ev .exit ∧
      u'.pc = 5) →
    Run spinK [] L1 0 u tr o → LoopTrace tr := by
  induction n with
  | zero =>
    intro u k tr o hl _ _ _ _ _
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    exact ⟨0, .inl rfl⟩
  | succ n ih =>
    intro u k tr o hl hpc hev hf ht hr
    rcases tr with _ | ⟨e, l⟩
    · exact ⟨0, .inl rfl⟩
    obtain ⟨o', ⟨ok, rfl, rfl⟩, -, hrest⟩ := run_of_ev hev hr
    rw [hpc]
    cases ok
    · rcases l with _ | ⟨e', l'⟩
      · exact ⟨1, .inl rfl⟩
      · have hs : out spinK [] L1 0 (pollK (out spinK [] L1 0 s) false) =
            .tau (tauOf (out spinK [] L1 0 (pollK (out spinK [] L1 0 s) false))) := rfl
        rw [s_fix] at hs
        exact (ih s _ _ o (by simp at hl ⊢; omega) rfl rfl hs ⟨_, rfl, rfl, rfl⟩
          (run_of_tau hf (hrest _ rfl))).cons
    · obtain ⟨u', h1, h2, h3⟩ := ht
      rcases l with _ | ⟨e', l'⟩
      · exact ⟨0, .inr (.inl rfl)⟩
      · obtain ⟨rfl, rfl⟩ := run_exit h2 (run_of_tau h1 (hrest _ rfl))
        exact ⟨0, .inr (.inr (by rw [h3]; rfl))⟩

/-- The traces of the thread: the initialization, the arrival and the spin. -/
def ThreadTrace (tr : List Event) : Prop :=
  tr = [] ∨ tr = [eInit] ∨ ∃ l, tr = eInit :: eArr :: l ∧ LoopTrace l

theorem thread_trace {tr : List Event} {o : Option TState} (h : Run spinK [] L1 0 {} tr o) :
    ThreadTrace tr := by
  rcases tr with _ | ⟨e, l⟩
  · exact .inl rfl
  obtain ⟨o', ⟨rfl, rfl⟩, -, hr⟩ :=
    run_of_ev (show out spinK [] L1 0 t1 = .ev (.mbInit M 2 t2) from rfl) (run_of_tau rfl h)
  rcases l with _ | ⟨e2, l2⟩
  · exact .inr (.inl rfl)
  obtain ⟨o'', ⟨rfl, rfl⟩, -, hr2⟩ :=
    run_of_ev (show out spinK [] L1 0 t2 = .ev (.arrive M 0 t3) from rfl) (hr _ rfl)
  exact .inr (.inr ⟨l2, rfl, loop l2.length t3 _ l2 _ (Nat.le_refl _) rfl rfl rfl
    ⟨_, rfl, rfl, rfl⟩ (hr2 _ rfl)⟩)

section Consistent
variable {mem0 : Mem0} {Y : Execution}

theorem lt_L1 {g : Nat} (hg : g < L1.threads) : g = 0 := by
  simp [L1, Launch.threads] at hg; omega

theorem tr_shape (hY : Consistent L1 spinK [] mem0 Y) : ThreadTrace (Y.tr 0) :=
  thread_trace (hY.thr 0 (by decide)).choose_spec

/-- The events of a possible execution, with the positions of the initialization and the
arrival. -/
theorem kinds (hY : Consistent L1 spinK [] mem0 Y) {e : EvId} {pc : Nat} {k : Kind}
    (h : Y.get e = some ⟨pc, k⟩) :
    (e = (0, 0) ∧ k = .mbInit M 2) ∨ (e = (0, 1) ∧ k = .arrive M 0 1 true .cta) ∨
      (∃ ok, k = .wait M 0 ok true .cta) ∨ k = .exit := by
  obtain ⟨g, j⟩ := e
  rcases Nat.lt_or_ge g L1.threads with hg | hg
  · obtain rfl := lt_L1 hg
    simp only [Execution.get] at h
    rcases tr_shape hY with h0 | h0 | ⟨l, h0, hl⟩ <;> rw [h0] at h
    · simp at h
    · rcases j with _ | j <;> simp [eInit] at h
      exact .inl ⟨rfl, h.2.symm⟩
    all_goals
      rcases j with _ | _ | j
      · simp [eInit] at h; exact .inl ⟨rfl, h.2.symm⟩
      · simp [eArr] at h; exact .inr (.inl ⟨rfl, h.2.symm⟩)
      · simp only [List.getElem?_cons_succ] at h
        obtain ⟨ok, hx | hx⟩ := hl.mem (List.mem_of_getElem? h)
        · simp only [poll, Event.mk.injEq] at hx
          exact .inr (.inr (.inl ⟨ok, hx.2⟩))
        · simp only [eExit, Event.mk.injEq] at hx
          exact .inr (.inr (.inr hx.2))
  · simp [Execution.get, hY.outside g hg] at h

/-- The operations of the history of `M`: the initialization, the arrival of thread 0 and polls. -/
theorem action_cases (hY : Consistent L1 spinK [] mem0 Y) {q : MBarrier.Record AsyncCopy.Ref}
    (hq : q ∈ Y.objects M) :
    q.action = .init 2 ∨ (q.action = .arrive 1 0 ∧ q.id = .thread (0, 1)) ∨
      ∃ p ok, q.action = .pollParity p ok := by
  have ha := ((hY.tma.2.2.1 M).2.1 q hq).1
  cases hid : q.id with
  | thread e =>
    rw [hid] at ha
    cases hget : Y.get e with
    | none => simp [AsyncCopy.objectAction, hget] at ha
    | some ev =>
      obtain ⟨pc, k⟩ := ev
      rcases kinds hY hget with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ok, rfl⟩ | rfl <;>
        simp [AsyncCopy.objectAction, hget] at ha
      · exact .inl ha.symm
      · exact .inr (.inl ⟨ha.symm, rfl⟩)
      · exact .inr (.inr ⟨_, _, ha.symm⟩)
  | async i p =>
    rw [hid] at ha
    exfalso
    cases hget : Y.get i with
    | none =>
      cases p <;> (try rename_i x; cases x) <;>
        simp [AsyncCopy.objectAction, AsyncCopy.issuedBy, hget] at ha
    | some ev =>
      obtain ⟨pc, k⟩ := ev
      rcases kinds hY hget with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨ok, rfl⟩ | rfl <;> cases p <;>
        (try rename_i x; cases x) <;>
        simp [AsyncCopy.objectAction, AsyncCopy.issuedBy, hget] at ha

end Consistent

/-! ## The phase of `M` never completes -/

/-- Every object state of a history whose initializations all expect two arrivals expects two
arrivals. -/
theorem expected_two {s0 t : Option MBarrier.State}
    {xs : List (MBarrier.Record AsyncCopy.Ref)} (h : MBarrier.RecordedHistory s0 xs t)
    (hi : ∀ q ∈ xs, ∀ n, q.action = .init n → n = 2)
    (hs : ∀ st, s0 = some st → st.expected = 2) : ∀ st, t = some st → st.expected = 2 := by
  induction h with
  | nil => exact hs
  | @cons s r rest t hr _ ih =>
    apply ih (fun q hq => hi q (List.mem_cons_of_mem _ hq))
    intro st hst
    unfold MBarrier.RecordOk at hr
    split at hr
    · rename_i rep hp
      rw [hr.1] at hst
      have hn := hi r List.mem_cons_self
      cases s with
      | none =>
        cases ha : r.action <;> rw [ha] at hp hn <;>
          simp [MBarrier.perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
            MonadExceptOf.throw] at hp
        split_ifs at hp
        simp at hp
        subst hp
        simp at hst
        rw [← hst]
        exact hn _ rfl
      | some s1 =>
        have h1 := hs s1 rfl
        cases ha : r.action <;> rw [ha] at hp <;>
          simp [MBarrier.perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
            MonadExceptOf.throw] at hp <;>
          (try split_ifs at hp) <;> (try simp at hp) <;> (try subst hp) <;>
          simp [MBarrier.advance] at hst <;> (try split_ifs at hst) <;> (try subst hst) <;>
          simp_all
    · rw [hr.1] at hst
      exact hs st hst

theorem units_zero {xs : List (MBarrier.Record AsyncCopy.Ref)}
    (h : ∀ q ∈ xs, ∀ n tx, q.action ≠ .arrive n tx) : MBarrier.arrivalUnits xs = 0 := by
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    simp only [MBarrier.arrivalUnits, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    have := h r List.mem_cons_self
    split <;> simp_all

/-- A history with distinct identities whose only arrival operation is one arrival of thread 0
has at most one arrival unit. -/
theorem units_le_one {xs : List (MBarrier.Record AsyncCopy.Ref)}
    (hnd : (xs.map MBarrier.Record.id).Nodup)
    (h : ∀ q ∈ xs, ∀ n tx, q.action = .arrive n tx → q.id = .thread (0, 1) ∧ n = 1) :
    MBarrier.arrivalUnits xs ≤ 1 := by
  induction xs with
  | nil => simp [MBarrier.arrivalUnits]
  | cons r rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [MBarrier.arrivalUnits]
    by_cases ha : ∃ n tx, r.action = .arrive n tx
    · obtain ⟨n, tx, ha⟩ := ha
      obtain ⟨hid, rfl⟩ := h r List.mem_cons_self n tx ha
      rw [units_zero fun q hq n' tx' hq' => hnd.1 (by
        rw [hid, ← (h q (List.mem_cons_of_mem _ hq) n' tx' hq').1]
        exact List.mem_map_of_mem hq)]
      split <;> simp_all
    · have := ih hnd.2 fun q hq => h q (List.mem_cons_of_mem _ hq)
      split
      · rename_i n tx heq _; exact absurd ⟨n, tx, heq⟩ ha
      · omega

theorem increments_zero {xs : List (MBarrier.Record AsyncCopy.Ref)}
    (h : ∀ q ∈ xs, q.action ≠ .increment) : MBarrier.incrementUnits xs = 0 := by
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    simp only [MBarrier.incrementUnits, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    have := h r List.mem_cons_self
    split <;> simp_all

/-- **No poll succeeds.** The poll's record follows the initialization in the history of `M`,
so it does not fault; a successful poll of parity 0 needs a completed phase, but with two
expected arrivals and one arrival unit the phase stays 0. -/
theorem no_ok_poll {mem0 : Mem0} {Y : Execution} (hY : Consistent L1 spinK [] mem0 Y) {j : Nat}
    (h : Y.get (0, j) = some (poll true)) : False := by
  obtain ⟨hchk, hmatch, hcov⟩ := hY.tma.2.2.1 M
  have h00 : Y.get (0, 0) = some eInit := by
    rcases tr_shape hY with h0 | h0 | ⟨l, h0, -⟩ <;>
      simp only [Execution.get, h0] at h ⊢
    · simp at h
    · rcases j with _ | j <;> simp [eInit, poll] at h
    · rfl
  have hj0 : j ≠ 0 := by rintro rfl; rw [h00] at h; simp [eInit, poll] at h
  obtain ⟨i, r, hi, hid, hact, hrok, -⟩ := init_record_of_consistent hY (⟨1, h00⟩ :
    Y.MbInit (0, 0) M 2)
  have hpa : AsyncCopy.objectAction Y Y.async M (.thread (0, j)) = some (.pollParity 0 true) := by
    simp [AsyncCopy.objectAction, h, poll]
  obtain ⟨rp, hrp, hrpid⟩ := hcov _ _ hpa
  obtain ⟨jj, hjj⟩ := List.mem_iff_getElem?.mp hrp
  have hpact : rp.action = .pollParity 0 true := by
    have := (hmatch rp hrp).1
    rw [hrpid, hpa] at this
    exact (Option.some.inj this).symm
  have hpo : baseCausality L1 Y (0, 0) (0, j) :=
    .single (.inl ⟨rfl, Nat.pos_of_ne_zero hj0, (List.getElem?_eq_some_iff.mp h).1,
      fun hs => by simp [SameAccess, h, Event.acc, poll] at hs⟩)
  have hnb := object_not_before_of_baseCausality hY (id := .thread (0, j)) ⟨2, 1, h00⟩ hpo
  have hij : i < jj := by
    rcases lt_trichotomy i jj with h1 | rfl | h1
    · exact h1
    · rw [hi] at hjj
      cases hjj
      rw [hid] at hrpid
      cases hrpid
      exact absurd rfl hj0
    · exact absurd ⟨jj, i, rp, r, hjj, hrpid, hi, hid, h1⟩ hnb
  have hlen : jj < (Y.objects M).length := (List.getElem?_eq_some_iff.mp hjj).1
  have hcls := fun q hq => action_cases hY (q := q) hq
  have hni : MBarrier.NoInval (Y.objects M) := fun q hq ha => by
    rcases hcls q hq with h1 | ⟨h1, -⟩ | ⟨p, ok, h1⟩ <;> rw [ha] at h1 <;> cases h1
  -- The state after the initialization record is an object.
  have hs1 : ∃ s1, MBarrier.stateBefore (Y.objects M) (i + 1) = some s1 := by
    simp only [MBarrier.stateBefore, Nat.add_sub_cancel, hi, Option.bind_some,
      Nat.add_one_ne_zero, ite_false]
    unfold MBarrier.RecordOk at hrok
    rw [hact] at hrok
    split at hrok
    · rename_i rep hp
      rw [hrok.1]
      cases hb : MBarrier.stateBefore (Y.objects M) i <;> rw [hb] at hp <;>
        simp [MBarrier.perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw] at hp
      · split_ifs at hp; simp at hp; subst hp; exact ⟨_, rfl⟩
    · rw [hrok.1]
      cases hb : MBarrier.stateBefore (Y.objects M) i
      · rename_i e hp
        rw [hb] at hp
        simp [MBarrier.perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw] at hp
        split_ifs at hp with hv
        exact absurd (show MBarrier.validCount 2 by decide) hv
      · exact ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ := hs1
  obtain ⟨t, ht, -⟩ := hchk.phase_mono hni (by omega : i + 1 ≤ jj) hlen.le hs1
  -- The poll's record does not fault, so the poll observed a completed phase.
  have hfault : rp.fault = none := by
    have hr := hchk.at hjj
    rw [ht] at hr
    unfold MBarrier.RecordOk at hr
    rw [hpact] at hr
    split at hr
    · exact hr.2
    · rename_i e hp
      simp [MBarrier.perform, pure, Except.pure] at hp
  have hw := (hmatch rp hrp).2 0 true hpact hfault
  obtain ⟨st, p, hst, hact', hne, -⟩ := hchk.okPoll hjj hw
  rw [hpact] at hact'
  cases hact'
  -- The arrival accounting keeps the phase at 0.
  obtain ⟨hpend, hacc⟩ := (hchk.accounted hni hlen.le).2 st hst
  have hexp := expected_two (hchk.prefix hlen.le)
    (fun q hq n hn => by
      rcases hcls q (List.mem_of_mem_take hq) with h1 | ⟨h1, -⟩ | ⟨p, ok, h1⟩ <;>
        rw [hn] at h1 <;> cases h1
      rfl)
    (fun _ h => by cases h) st hst
  have hinc : MBarrier.incrementsBefore (Y.objects M) jj = 0 :=
    increments_zero fun q hq ha => by
      rcases hcls q (List.mem_of_mem_take hq) with h1 | ⟨h1, -⟩ | ⟨p, ok, h1⟩ <;>
        rw [ha] at h1 <;> cases h1
  have hunits : MBarrier.unitsBefore (Y.objects M) jj ≤ 1 := by
    refine units_le_one ?_ fun q hq n tx ha => ?_
    · rw [List.map_take]
      exact hchk.1.sublist (List.take_sublist _ _)
    · rcases hcls q (List.mem_of_mem_take hq) with h1 | ⟨h1, hq1⟩ | ⟨p, ok, h1⟩ <;>
        rw [ha] at h1 <;> cases h1
      exact ⟨hq1, rfl⟩
  rw [hexp, hinc] at hacc hpend
  omega

/-- **The spin deadlocks.** A possible execution that cannot grow and is not complete exists:
every possible execution has at most four counted events (the failed polls do not count), and
none is complete, since the thread exits only after a successful poll. -/
theorem spin_deadlock (mem0 : Mem0) :
    ∃ X, Maximal L1 spinK [] mem0 X ∧ ¬ Complete L1 X := by
  refine deadlock_of_bound (by decide) (by simp) 4 (fun Y hY g hg => ?_)
    (fun Y hY i s ⟨pc, h⟩ => ?_) (fun Y hY hc => ?_)
  · obtain rfl := lt_L1 hg
    have hz : ∀ n, (List.replicate n (poll false)).countP Event.counts = 0 := fun n =>
      List.countP_eq_zero.mpr fun x hx => by rw [List.eq_of_mem_replicate hx]; decide
    rcases tr_shape hY with h0 | h0 | ⟨l, h0, n, rfl | rfl | rfl⟩ <;> rw [h0] <;>
      simp only [List.countP_cons, List.countP_append, List.countP_nil, hz] <;> decide
  · rcases kinds hY h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨ok, h⟩ | h <;> cases h
  · rcases hc.1 0 (by decide) with ⟨-, req, ho⟩ | ⟨pc, hx⟩
    · obtain ⟨i, s, targets, -, ⟨pc, hi⟩, -⟩ := hY.clc.canceled_has_issue ho
      rcases kinds hY hi with ⟨-, h⟩ | ⟨-, h⟩ | ⟨ok, h⟩ | h <;> cases h
    · have hm := List.mem_of_getLast? hx
      rcases tr_shape hY with h0 | h0 | ⟨l, h0, n, rfl | rfl | rfl⟩ <;> rw [h0] at hm
      · simp at hm
      · simp [eInit] at hm
      · simp [List.mem_replicate, eInit, eArr, poll] at hm
      · simp [List.mem_replicate, eInit, eArr, poll] at hm
      · exact no_ok_poll hY (j := n + 2) (by
          simp [Execution.get, h0])

end MbarSpin

end

end PTX.Tests.Progress
