-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The work left in a task

A rank on a thread's abstract states bounds its counted events (all but failed polls). Every role
runs one task per successful poll of its CTA's CLC response barrier, and the rank of a state counts
the events left until the next such poll, or until the exit: the prologue counts down its sites;
the loader the events left in its task (five per block, eight blocks per trip, sixteen trips) and
its tail; the MMA thread its response, the accumulator poll and the events left in its task (six
per slot, four slots per trip, thirty-two trips) and the accumulator commit; the scheduler its
request and response; a consumer its response, its loads and its epilogue (twenty-two events per
slice, eight slices). At a role's response wait the rank is below the exit, and a successful poll
there raises it by at most `resetBudget`: the work of one task. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Bound

open PTX PTX.Flow

/-- The rank a successful response poll may add: above the work of any task. -/
abbrev resetBudget : Nat := 1000

/-- The order of the prologue's sites along every run. -/
def prologueOrd : Prologue.Site → Nat
  | .shfl => 0 | .elect => 1 | .init i => 2 + i.val | .alloc => 20 | .allocWrite => 21
  | .warpBar => 22 | .fence => 23 | .fenceInit => 24 | .arrive => 25 | .wait => 26
  | .setMaxReg => 27 | .roleElect => 28

/-- The loader's counted events left before its next response poll or its exit: the rest of the
current block and trip and the trips after it, or after its response the next task. -/
def loaderRank (d : Loader.D) : Nat :=
  match d.site with
  | .wait b => 5 * (8 - b.val) + 40 * ((120 - d.q) / 8) + 1
  | .load b j => 4 - j.val + 5 * (7 - b.val) + 40 * ((120 - d.q) / 8) + 1
  | .arrive b => 1 + 5 * (7 - b.val) + 40 * ((120 - d.q) / 8) + 1
  | .clcWait => 0 | .clcLoad => 646 | .clcStatus => 645 | .clcFirst => 644 | .clcFence => 643
  | .ack => 642 | .drain i => 7 - i.val | .exitArrive => 3 | .exitWait => 2 | .exit => 1

/-- The MMA thread's counted events left before its next response poll or its exit. -/
def mmaRank (d : Mma.D) : Nat :=
  match d.site with
  | .elect => 780 | .clcWait => 4 | .clcLoad => 779 | .clcStatus => 778 | .clcFirst => 777
  | .clcFence => 776 | .ack => 775 | .accWait => 774
  | .full s => 6 * (4 - s.val) + 24 * ((124 - d.q) / 4) + 5
  | .mma s j => 6 * (3 - s.val) + 5 - j.val + 24 * ((124 - d.q) / 4) + 5
  | .commit s => 6 * (3 - s.val) + 1 + 24 * ((124 - d.q) / 4) + 5
  | .accCommit => 5 | .exitArrive => 3 | .exitWait => 2 | .exit => 1

/-- The scheduler's counted events left before its next response poll or its exit. -/
def schedRank (d : Scheduler.D) : Nat :=
  match d.site with
  | .elect => 8 | .ackWait => 7 | .tryCancel => 6 | .arriveTx => 5 | .clcWait => 4
  | .clcLoad => 12 | .clcStatus => 11 | .clcFirst => 10 | .clcFence => 9 | .ack => 8
  | .exitArrive => 3 | .exitWait => 2 | .exit => 1

/-- A consumer's counted events left before its next response poll or its exit. -/
def consRank (d : Consumer.D) : Nat :=
  match d.site with
  | .setMaxReg => 9 | .clcWait => 8 | .clcLoad => 224 | .clcStatus => 223 | .clcFirst => 222
  | .clcFence => 221 | .clcBar => 220 | .ack => 219 | .accWait => 218
  | .load j => 187 + 2 * (15 - j.val) | .loadWait j => 186 + 2 * (15 - j.val)
  | .accArrive => 185
  | .drain k => 22 * (7 - k.val) + 30 | .barA k => 22 * (7 - k.val) + 29
  | .store k i el => 22 * (7 - k.val) + 12 + 4 * (3 - i.val) + (4 - el.val)
  | .barB k => 22 * (7 - k.val) + 12 | .fence k => 22 * (7 - k.val) + 11
  | .tma k => 22 * (7 - k.val) + 10 | .commit k => 22 * (7 - k.val) + 9
  | .finalDrain => 7 | .exitArrive => 6 | .exitWait => 5 | .relinquish => 4 | .ldBase => 3
  | .dealloc => 2 | .exit => 1

/-- The rank of a thread's abstract state. -/
def rank : Option ThreadD → Nat
  | none => 0
  | some (.inl p) => 2000 - prologueOrd p.site
  | some (.inr (.loader l)) => loaderRank l
  | some (.inr (.mma m)) => mmaRank m
  | some (.inr (.sched s)) => schedRank s
  | some (.inr (.cons c)) => consRank c

/-- A poll counts exactly when it succeeds. -/
theorem counts_of_wait {e : Event} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait m p ok acq sc) : e.counts = ok := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  cases ok <;> rfl

end PTX.Kernels.Fp16Gemm8192.Proof.Bound
