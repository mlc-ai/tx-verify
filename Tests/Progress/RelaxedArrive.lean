-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.NoAsync
public import Lemmas.Order.WaitOrderWaits

@[expose] public section

/-!
# Keep test: a relaxed mbarrier arrival completes a phase but publishes nothing

One CTA of two threads. Thread 0 initializes the mbarrier `M` with expected count 1, stores 1 to
the shared word `x` and arrives on `M` with `.relaxed` semantics; thread 1 polls `M` with an
`.acquire` `try_wait` and then loads `x`:

```
// thread 0                                  // thread 1
mbarrier.init.shared::cta.b64 [M], 1;        L: mbarrier.try_wait.parity.acquire.cta.shared::cta.b64
st.shared.u32 [x], 1;                              p, [M], 0;
mbarrier.arrive.relaxed.cta.shared::cta.b64     @!p bra L;
    _, [M];                                  ld.shared.u32 r, [x];
exit;                                        exit;
```

The execution `X false` has the poll succeed on its first try, observing the relaxed arrival, and
the load return the launch content of `x` instead of the store's 1.

* `poll_returns`: with either arrival, the history of `M` is a checked history, the poll
  returned (`Returned`), it observed the arrival (`MbarObserved`), every need of the poll is
  present (`Ready`), and every thread exited (`Complete`): a relaxed arrival completes the phase
  that the acquire poll waits for.
* `relaxed_weak_allowed`: the read axioms hold for the load of the launch content (`NoFuture`,
  `Hidden`): mbarrier synchronization (`MSync`) starts only at a `.release` arrival
  (`MbarRelease`), so nothing orders the store before the load.
* `release_weak_forbidden`: with a `.release` arrival (`X true`) the arrival synchronizes with the
  acquire poll (`MSync`), the store precedes the load in causality, and the same load outcome
  breaks `Hidden`.

The tests check the rules that decide these outcomes on the given executions; they do not prove
the whole of `Consistent` for them.
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

namespace RelaxedArrive

/-- One CTA of two threads. -/
def L2 : Launch := { grid := 1, block := 2, params := fun _ => none }

/-- The mbarrier `M` at shared offset 0 and the word `x` at shared offset 8 of CTA 0. -/
def M : Loc := ⟨.shared, 0, 0⟩
def xA : Acc := { loc := ⟨.shared, 0, 8⟩, size := 4 }
def one : List Byte := (Value.bits 32 1).toBytes
/-- The bytes of the launch content the load returns. -/
def zero : List (Option Byte) := (Value.bits 32 0).toBytes.map some

/-- The states of `M`: initialized with count 1, after the arrival, and after the successful
poll. -/
def st0 : MBarrier.State := ⟨0, 1, 1, 0, true⟩
def st1 : MBarrier.State := ⟨1, 1, 1, 0, false⟩
def st2 : MBarrier.State := ⟨1, 1, 1, 0, true⟩

/-- The history of `M`: the initialization, the arrival, the poll that observes phase 0. -/
def log : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (0, 0), .init 1, ⟨some st0, none, none⟩, none⟩,
  ⟨.thread (0, 2), .arrive 1 0, ⟨some st1, none, none⟩, none⟩,
  ⟨.thread (1, 0), .pollParity 0 true, ⟨some st2, some true, some 0⟩, none⟩]

/-- The traces, with a relaxed (`rel = false`) or a release (`rel = true`) arrival. -/
def trace (rel : Bool) : Nat → List Event
  | 0 => [⟨0, .mbInit M 1⟩, ⟨1, .wr xA one⟩, ⟨2, .arrive M 0 1 rel .cta⟩, ⟨3, .exit⟩]
  | 1 => [⟨4, .wait M 0 true true .cta⟩, ⟨5, .rd xA zero⟩, ⟨6, .exit⟩]
  | _ => []

def X (rel : Bool) : Execution where
  tr := trace rel
  rf _ _ := none
  objects m := if m = M then log else []

/-- The events of the execution. -/
theorem get_cases {rel : Bool} {e : EvId} {pc : Nat} {k : Kind}
    (h : (X rel).get e = some ⟨pc, k⟩) :
    (e = (0, 0) ∧ k = .mbInit M 1) ∨ (e = (0, 1) ∧ k = .wr xA one) ∨
      (e = (0, 2) ∧ k = .arrive M 0 1 rel .cta) ∨ (e = (1, 0) ∧ k = .wait M 0 true true .cta) ∨
      (e = (1, 1) ∧ k = .rd xA zero) ∨ k = .exit := by
  obtain ⟨g, i⟩ := e
  rcases g with _ | _ | g <;> rcases i with _ | _ | _ | _ | i <;>
    simp [Execution.get, X, trace] at h ⊢ <;> simp [← h]

/-- The history of `M` is a sequence of the object transitions of OBJ-MBAR-STATE. -/
theorem log_checked : MBarrier.CheckedLog log :=
  ⟨by decide, _, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _)))⟩

/-- The poll observes the phase that the arrival completed. -/
theorem update_before_wait (rel : Bool) :
    AsyncCopy.WaitObserves (X rel) (.thread (0, 2)) (1, 0) M true .cta :=
  ⟨⟨4, 0, rfl⟩, 1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
    fun k s h1 h2 => by omega⟩

/-- Closes a goal from an event of a kind that the execution does not have. -/
local macro "bad " h:ident : tactic =>
  `(tactic| (rcases get_cases $h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | h' <;>
    cases h'))

/-- No asynchronous operation is issued, so the execution is drained. -/
theorem complete (rel : Bool) : Complete L2 (X rel) := by
  refine ⟨fun g hg => .inr ?_, ?_, ?_⟩
  · rcases g with _ | _ | g
    · exact ⟨3, rfl⟩
    · exact ⟨6, rfl⟩
    · simp [L2, Launch.threads] at hg
  · intro i p hp
    obtain ⟨s, m, ⟨pc, h⟩, -, -⟩ | ⟨s, ⟨pc, h⟩, -, -⟩ | ⟨m, noinc, ⟨pc, h⟩, -⟩ |
      ⟨⟨_, _, _, _, pc, h⟩ | ⟨_, pc, h⟩ | ⟨_, pc, h⟩, -⟩ | ⟨s, t, c, ⟨pc, h⟩, -, -⟩ |
      ⟨a, s, ⟨pc, h⟩, -⟩ | ⟨a, s, ⟨pc, h⟩, -⟩ |
      ⟨s, r, m, ⟨pc, h⟩, -, -⟩ := hp
    all_goals bad h
  · intro i pc group dst action h
    bad h

/-- With either arrival the poll returns on its first try: it observed the arrival and its needs
are present, and the execution is complete. -/
theorem poll_returns (rel : Bool) :
    MBarrier.CheckedLog ((X rel).objects M) ∧ Returned (X rel) (1, 0) ∧
      MbarObserved (X rel) (.thread (0, 2)) (.thread (1, 0)) ∧ Ready L2 (X rel) (1, 0) ∧
      Complete L2 (X rel) := by
  refine ⟨by simpa [X] using log_checked, rfl, ⟨⟨_, rfl⟩, (1, 0), M, true, .cta, rfl,
    update_before_wait rel, fun r hr hid => ?_⟩, ?_, ?_⟩
  · simp only [X, ite_true, log, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp_all [CounterUpdate]
  · intro n hn
    simp only [Needs, show (X rel).get (1, 0) = some ⟨4, .wait M 0 true true .cta⟩ from rfl,
      KindNeeds, ite_true, pollNeeds, List.mem_flatMap] at hn
    obtain ⟨r, -, hn⟩ := hn
    rw [needsIf] at hn
    split_ifs at hn with ho
    · simp only [List.mem_singleton] at hn
      subst hn
      exact ⟨r.id, ho.1, rfl⟩
    · simp at hn
  · exact complete rel

/-- Without a release arrival, base causality stays in one thread. -/
theorem baseCausality_same {e f : EvId} (h : baseCausality L2 (X false) e f) : e.1 = f.1 := by
  have none : ∀ {e : EvId} {pc : Nat} {k : Kind}, (X false).get e = some ⟨pc, k⟩ →
      k ≠ .mbInit M 1 → k ≠ .wr xA one → k ≠ .arrive M 0 1 false .cta →
      k ≠ .wait M 0 true true .cta → k ≠ .rd xA zero → k ≠ .exit → False := by
    intro e pc k hk h1 h2 h3 h4 h5 h6
    rcases get_cases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | rfl <;>
      simp_all
  have step : ∀ e f, (po (X false) e f ∨ CtaBarSync L2 (X false) e f ∨ MSync L2 (X false) e f ∨
      ClusterSync L2 (X false) e f ∨ WarpBarSync L2 (X false) e f ∨
      synchronizesWith L2 (X false) e f ∨ FenceSync L2 (X false) e f) → e.1 = f.1 := by
    intro e f hs
    rcases hs with hp | hs | hs | hs | hs | hs | hs
    · exact hp.1
    · obtain ⟨-, key, i, j, hi, -⟩ := hs
      obtain ⟨idx, st, warp, count, lanes, g, hget, -⟩ := hi.2.2
      simp [X] at hget
    · obtain ⟨x, w, m, rs, as, ⟨tx, count, pc, ha⟩, -⟩ := hs
      exact (none ha (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).elim
    · obtain ⟨-, i, j, ⟨phase, ha, -⟩, -⟩ := hs
      simp [X, ClusterBarrier.ArrivalOf] at ha
    · obtain ⟨i, j, ⟨-, mask, inst, ⟨pc, hw⟩, -⟩, -⟩ := hs
      exact (none hw (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).elim
    · obtain ⟨a, b, bs, cs, hw, -, hrel, -⟩ := hs
      rcases hw with ⟨pc, hw⟩ | ⟨o, pc, hw⟩
      · rcases get_cases hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h <;>
          simp at h
        obtain ⟨rfl, -⟩ := h
        simp [xA] at hrel
      · exact (none hw (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).elim
    · exact absurd hs (not_fenceSync_of_noFence (fun e sem s ⟨pc, hf⟩ =>
        none hf (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) e f)
  induction h with
  | single hs => exact step _ _ hs
  | tail _ hs ih => exact ih.trans (step _ _ hs)

/-- With a relaxed arrival, the load of the launch content satisfies the read axioms. -/
theorem relaxed_weak_allowed :
    (X false).get (1, 1) = some ⟨5, .rd xA zero⟩ ∧ (X false).rf (.thread (1, 1)) 0 = none ∧
      NoFuture L2 (X false) ∧ Hidden L2 (X false) := by
  refine ⟨rfl, rfl, fun e a bs k w _ _ h => by simp [X] at h, ?_⟩
  intro e a bs k w a' bs' hr hk hw hc hmc
  cases e with
  | async i p =>
    rcases p with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ <;>
      (try rename_i s; cases s) <;>
      simp [Execution.MemReads, Execution.MmaRead, Execution.Copy, X] at hr
  | thread i =>
    cases w with
    | async j q =>
      rcases q with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ <;>
        (try rename_i s; cases s) <;> simp [Execution.MemWrites, Execution.Copy, X] at hw
      obtain ⟨s, t, ⟨pc, h⟩, -⟩ := hw
      bad h
    | thread j =>
      have hn : ∀ i d s accum mask, ¬ (X false).MmaIssue i d s accum mask := by
        rintro i d s accum mask ⟨pc, h⟩
        bad h
      have hc : ∀ i c, ¬ (X false).CpIssue i c := by
        rintro i c ⟨pc, h⟩
        bad h
      rcases (ByteCausality.direct_iff_of_no_operand hn hc).1 hmc with hmc | halloc
      swap
      · obtain ⟨_, _, _, _, halloc, _, _, _, _⟩ := halloc
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hget, _, _, _⟩ := halloc
        bad hget
      have hs := baseCausality_same hmc
      rcases hr with ⟨pc, hr⟩ | ⟨n, pc, hr⟩ <;> rcases hw with ⟨pc', hw⟩ | ⟨o, pc', hw⟩ <;>
        rcases get_cases hr with ⟨hi, h⟩ | ⟨hi, h⟩ | ⟨hi, h⟩ | ⟨hi, h⟩ | ⟨hi, h⟩ | h <;>
        rcases get_cases hw with ⟨hj, h'⟩ | ⟨hj, h'⟩ | ⟨hj, h'⟩ | ⟨hj, h'⟩ | ⟨hj, h'⟩ | h' <;>
        simp_all

/-- With a release arrival, the arrival synchronizes with the acquire poll, so the store precedes
the load in causality and the load of the launch content breaks `Hidden`. -/
theorem release_weak_forbidden : ¬ Hidden L2 (X true) := by
  intro h
  have hsync : MSync L2 (X true) (0, 1) (1, 1) :=
    ⟨(0, 2), (1, 0), M, .cta, .cta, ⟨0, 1, 2, rfl⟩, update_before_wait true,
      ⟨⟨by decide, by decide, rfl⟩, ⟨by decide, by decide, rfl⟩⟩, rfl, by decide, by decide, rfl,
      by decide⟩
  exact h (.thread (1, 1)) xA zero 0 (.thread (0, 1)) xA one (.inl ⟨5, rfl⟩) (by decide)
    (.inl ⟨1, rfl⟩) (by simp [xA, Acc.Covers, Loc.InRange, Loc.at])
    (.direct (.inl (.single (.inr (.inr (.inl hsync))))))

end RelaxedArrive

end

end PTX.Tests.Progress
