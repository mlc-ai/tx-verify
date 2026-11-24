-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingPrelude
public import Lemmas.Flow.Counted
public import Lemmas.Flow.TraceInduction
public import Lemmas.Flow.Polls
public import Lemmas.Flow.NotTensor
public import Lemmas.Tmem.PairProtocol
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section

/-! # The ghost ledger of a thread

A thread's counts of its own events by class: arrivals and successful polls on an mbarrier
object, tensor copies that signal an object, named-barrier events by id, full-mask votes,
register requests and Tensor Memory resource operations. The ledger machine is the thread's
machine with a ghost count per class (`Ledger.code`); a role states the closed forms of the counts
it needs as an invariant of its own states and the counts (its ledger), proves that its first
state satisfies it when the role's classes have no event yet, and that each of its followed steps
preserves it. `Ledger.wg0`, `tma`, `index`, `wg2` and `mma` then give the role's ledger at every
state of a run; the prologue, the warpgroup-1 head and the other roles are handled here once. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Ledger

open PTX PTX.Flow

noncomputable section

/-- The event classes of the ghost ledger. -/
inductive Cls where
  | arrive (m : Loc)
  | poll (m : Loc)
  | issue (m : Loc)
  | bar (id : Nat)
  | vote
  | request
  | tmem

/-- Whether an event is of a class. -/
def Cls.test : Cls → Event → Bool
  | .arrive m => arrivesOn m
  | .poll m => okPoll m
  | .issue m => issuesTo m
  | .bar id => Execution.isBarId id
  | .vote => fun e => (voteClass e.kind).any (·.mask == 2 ^ 32 - 1)
  | .request => SetMaxNReg.isRequest
  | .tmem => Tmem.Pair.isTmemOp

/-- The ledger machine: a thread's machine with a ghost count per class. -/
abbrev code (P : Params) (L : Launch) (g : Nat) : Code kernel Assumptions.all L g :=
  (Machine.code P L g).counted Cls.test

/-- The counts of the first `i` events of a list. -/
def count (es : List Event) (i : Nat) (c : Cls) : Nat := (es.take i).countP c.test

/-- The counts after one more event. -/
abbrev bump (n : Cls → Nat) (e : Event) : Cls → Nat := Code.bump Cls.test n e

@[simp] theorem bump_apply (n : Cls → Nat) (e : Event) (c : Cls) :
    bump n e c = n c + if c.test e then 1 else 0 := rfl

/-- No class has an event of a kind that none of them counts. -/
theorem test_shfl {e : Event} {mode : ShflMode} {a recv : Value} {b c' : Nat} {ok : Bool}
    (hk : e.kind = .shfl mode a b c' recv ok) (c : Cls) : c.test e = false := by
  cases c <;> simp [Cls.test, arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, issuesTo,
    Execution.isBarId, voteClass, SetMaxNReg.isRequest, Tmem.Pair.isTmemOp, hk]

/-- Counts that are zero for the classes `Z`. -/
def Quiet (Z : Cls → Prop) (n : Cls → Nat) : Prop := ∀ c, Z c → n c = 0

theorem Quiet.bump {Z : Cls → Prop} {n : Cls → Nat} {e : Event} (h : Quiet Z n)
    (he : ∀ c, Z c → c.test e = false) : Quiet Z (bump n e) := fun c hc => by
  simp [h c hc, he c hc]

variable {P : Params} {L : Launch} {g : Nat}

/-- The ring classes: arrivals, successful polls and tensor copies on an mbarrier object. -/
def Ring (c : Cls) : Prop := ∃ m, c = .arrive m ∨ c = .poll m ∨ c = .issue m

private def tensorlessAt (i : Nat) : Bool :=
  kernel.code[i]?.any (fun ins => !tensorOp ins.op)

set_option maxRecDepth 100000 in
private theorem prologue_tensorless (s : Site) : tensorlessAt s.pc = true := by
  cases s
  case init j => fin_cases j <;> decide +kernel
  case handoff wg => fin_cases wg <;> decide +kernel
  all_goals decide +kernel

/-- **No prologue event is of a ring class.** -/
theorem ring_prologue {s : Site} {e : Event} {o : Option TState} {c : Cls}
    (hf : (Machine.machine P L g).Fired (some (.prologue s)) e o) (hc : Ring c) :
    c.test e = false := by
  obtain ⟨m, rfl | rfl | rfl⟩ := hc
  · exact (RingPrelude.prologue_no_counts hf m m).1
  · exact (RingPrelude.prologue_no_counts hf m m).2
  · have hn := prologue_tensorless s
    unfold tensorlessAt at hn
    cases hc : kernel.code[s.pc]? with
    | none => simp [hc] at hn
    | some ins =>
      rw [hc] at hn
      have hop : tensorOp ins.op = false := by simpa using hn
      obtain ⟨t, _, hf⟩ := hf
      change Fires t.pc (match kernel.code[s.pc]? with
        | some ins => eventTmpl Assumptions.all L g t ins.op
        | none => .ub .pcOutOfRange) e o at hf
      rw [hc] at hf
      exact issuesTo_notTensor (fires_notTensor (eventTmpl_notTensor hop) hf)

/-- The thread invariant made of the roles' ledgers, quiet before the roles. -/
private def Lift (Z : Cls → Prop) (R0 : Wg0.D → (Cls → Nat) → Prop)
    (R1 : Wg1Tma.D → (Cls → Nat) → Prop) (R2 : Wg1Index.D → (Cls → Nat) → Prop)
    (R3 : Wg2.D → (Cls → Nat) → Prop) (R4 : Wg1Mma.D → (Cls → Nat) → Prop) :
    Machine.ThreadD → (Cls → Nat) → Prop
  | .prologue _, n | .head, n => Quiet Z n
  | .wg0 d, n => R0 d n
  | .tma d, n => R1 d n
  | .index d, n => R2 d n
  | .wg2 d, n => R3 d n
  | .mma d, n => R4 d n
  | _, _ => True

/-- A role's exit: into `done`, the idle loop, an unfollowed or a dead state. -/
local macro "exit_case" : tactic =>
  `(tactic| first | (cases ‹_ = _›) | (split_ifs at * <;> cases ‹_ = _› <;> trivial))

/-- The roles' ledgers at a state of a run. -/
private theorem lift_at {Z : Cls → Prop} {R0 : Wg0.D → (Cls → Nat) → Prop}
    {R1 : Wg1Tma.D → (Cls → Nat) → Prop} {R2 : Wg1Index.D → (Cls → Nat) → Prop}
    {R3 : Wg2.D → (Cls → Nat) → Prop} {R4 : Wg1Mma.D → (Cls → Nat) → Prop}
    (hpro : ∀ s e o c, (Machine.machine P L g).Fired (some (.prologue s)) e o → Z c →
      c.test e = false)
    (h0 : ∀ n, Quiet Z n → R0 (Wg0.init P L g) n)
    (h1 : ∀ n, Quiet Z n → R1 (Wg1Tma.init P L g) n)
    (h2 : ∀ n, Quiet Z n → R2 (Wg1Index.init P L g) n)
    (h3 : ∀ n, Quiet Z n → R3 (Wg2.init P L g) n)
    (h4 : ∀ n, Quiet Z n → R4 ⟨.elect, 0⟩ n)
    (s0 : ∀ d d' n e o, (Wg0.code P L g).toMachine.Fired (some d) e o →
      Wg0.next P L g d e = some (some d') → R0 d n → R0 d' (bump n e))
    (s1 : ∀ d d' n e o, (Wg1Tma.code P L g).toMachine.Fired (some d) e o →
      Wg1Tma.next P L g d e = some (some d') → R1 d n → R1 d' (bump n e))
    (s2 : ∀ d d' n e o, (Wg1Index.code P L g).toMachine.Fired (some d) e o →
      Wg1Index.next P L g d e = some (some d') → R2 d n → R2 d' (bump n e))
    (s3 : ∀ d d' n e o, (Wg2.code P L g).toMachine.Fired (some d) e o →
      Wg2.next P L g d e = some (some d') → R3 d n → R3 d' (bump n e))
    (s4 : ∀ d d' n e o, (Wg1Mma.code P L g).toMachine.Fired (some d) e o →
      Wg1Mma.next P L g d e = some (some d') → R4 d n → R4 d' (bump n e))
    {es : List Event} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    {i : Nat} {q : Machine.ThreadD}
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) = some (some q)) :
    Lift Z R0 R1 R2 R3 R4 q (count es i) := by
  refine Code.ledger (C := Machine.code P L g) (cls := Cls.test) (Lift Z R0 R1 R2 R3 R4)
    (fun c _ => rfl) ?_ ht hs
  intro q n e o q' hf hn hI
  change Machine.next P L g q e = some (some q') at hn
  cases q with
  | prologue s =>
    have hq := hI.bump fun c hc => hpro s e o c hf hc
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact hq
    · split at hn
      · rename_i w _
        split_ifs at hn <;> cases hn
        match w with
        | ⟨0, _⟩ => exact h0 _ hq
        | ⟨1, _⟩ => exact hq
        | ⟨2, _⟩ => exact h3 _ hq
      · cases hn
    · cases hn
  | head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    have hq := hI.bump fun c _ => test_shfl hk c
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
    · exact h4 _ hq
    · exact h1 _ hq
    · exact h2 _ hq
    · trivial
  | wg0 d =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact s0 d _ n e o hf (by assumption) hI
    all_goals exit_case
  | tma d =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact s1 d _ n e o hf (by assumption) hI
    all_goals exit_case
  | index d =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact s2 d _ n e o hf (by assumption) hI
    all_goals exit_case
  | wg2 d =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact s3 d _ n e o hf (by assumption) hI
    all_goals exit_case
  | mma d =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact s4 d _ n e o hf (by assumption) hI
    all_goals exit_case
  | idle s =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn
    all_goals trivial
  | done => cases hn

section
variable {Z : Cls → Prop}
  (hpro : ∀ s e o c, (Machine.machine P L g).Fired (some (.prologue s)) e o → Z c →
    c.test e = false)
  {es : List Event} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es) {i : Nat}
include hpro ht

/-- **The softmax role's ledger** at a state of a run. -/
theorem wg0 (R : Wg0.D → (Cls → Nat) → Prop) (h0 : ∀ n, Quiet Z n → R (Wg0.init P L g) n)
    (hstep : ∀ d d' n e o, (Wg0.code P L g).toMachine.Fired (some d) e o →
      Wg0.next P L g d e = some (some d') → R d n → R d' (bump n e)) {d : Wg0.D}
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) : R d (count es i) :=
  lift_at (R1 := fun _ _ => True) (R2 := fun _ _ => True) (R3 := fun _ _ => True)
    (R4 := fun _ _ => True) hpro h0 (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) hstep (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) ht hs

/-- **The raw-KV producer's ledger** at a state of a run. -/
theorem tma (R : Wg1Tma.D → (Cls → Nat) → Prop) (h0 : ∀ n, Quiet Z n → R (Wg1Tma.init P L g) n)
    (hstep : ∀ d d' n e o, (Wg1Tma.code P L g).toMachine.Fired (some d) e o →
      Wg1Tma.next P L g d e = some (some d') → R d n → R d' (bump n e)) {d : Wg1Tma.D}
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) : R d (count es i) :=
  lift_at (R0 := fun _ _ => True) (R2 := fun _ _ => True) (R3 := fun _ _ => True)
    (R4 := fun _ _ => True) hpro (fun _ _ => trivial) h0 (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) hstep
    (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) ht hs

/-- **The index role's ledger** at a state of a run. -/
theorem index (R : Wg1Index.D → (Cls → Nat) → Prop)
    (h0 : ∀ n, Quiet Z n → R (Wg1Index.init P L g) n)
    (hstep : ∀ d d' n e o, (Wg1Index.code P L g).toMachine.Fired (some d) e o →
      Wg1Index.next P L g d e = some (some d') → R d n → R d' (bump n e)) {d : Wg1Index.D}
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.index d))) : R d (count es i) :=
  lift_at (R0 := fun _ _ => True) (R1 := fun _ _ => True) (R3 := fun _ _ => True)
    (R4 := fun _ _ => True) hpro (fun _ _ => trivial) (fun _ _ => trivial) h0
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) hstep (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) ht hs

/-- **The dequantizer's ledger** at a state of a run. -/
theorem wg2 (R : Wg2.D → (Cls → Nat) → Prop) (h0 : ∀ n, Quiet Z n → R (Wg2.init P L g) n)
    (hstep : ∀ d d' n e o, (Wg2.code P L g).toMachine.Fired (some d) e o →
      Wg2.next P L g d e = some (some d') → R d n → R d' (bump n e)) {d : Wg2.D}
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) : R d (count es i) :=
  lift_at (R0 := fun _ _ => True) (R1 := fun _ _ => True) (R2 := fun _ _ => True)
    (R4 := fun _ _ => True) hpro (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) h0 (fun _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) hstep
    (fun _ _ _ _ _ _ _ _ => trivial) ht hs

/-- **The MMA role's ledger** at a state of a run. -/
theorem mma (R : Wg1Mma.D → (Cls → Nat) → Prop) (h0 : ∀ n, Quiet Z n → R ⟨.elect, 0⟩ n)
    (hstep : ∀ d d' n e o, (Wg1Mma.code P L g).toMachine.Fired (some d) e o →
      Wg1Mma.next P L g d e = some (some d') → R d n → R d' (bump n e)) {d : Wg1Mma.D}
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.mma d))) : R d (count es i) :=
  lift_at (R0 := fun _ _ => True) (R1 := fun _ _ => True) (R2 := fun _ _ => True)
    (R3 := fun _ _ => True) hpro (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) h0 (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) hstep ht hs

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Ledger
