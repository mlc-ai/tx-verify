-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcSites
public import Lemmas.Flow.Polls
public import Lemmas.Flow.NotCommit

@[expose] public section

/-! # The rank table: when each event happens in a sequential schedule

The progress proof ranks a pending thread by the time its next event takes in one fixed
sequential schedule of the whole cluster (`ThreadD.vtime`). The schedule runs the prologue,
then one block per task, then the exit. Block `n` runs, in this order: the scheduler's
acknowledgement poll, request and response (offsets 0–16); the MMA thread's response and
accumulator-empty poll (20–32); the consumers' response and group barrier (40–52); the input
ring, one step of 32 per k-block `j` (the loader's empty poll, loads and arrival at 0–8, the
MMA thread's full poll, MMAs and commit at 10–20); the accumulator commit (4160); the loader's
response and tail drain (4170–4196); the consumers' accumulator poll, loads and epilogue
(4200–4800). Every wait waits for an event earlier in this schedule, and consecutive events of
a thread are at least 2 apart, so a thread blocked after a collective event ranks between
that event and its next one.

A thread's block comes from a count along its own trace: a loader's successful empty polls
(`loaderCount`, one per k-block), an MMA thread's commits to the input empty barriers
(`mmaCount`, one per k-block), a consumer's successful accumulator-full polls
(`consCount`, one per task) and a scheduler's successful response polls (`schedCount`).
The exit stage (`ThreadD.exitOff`) is ranked above every other thread of the execution by the
progress layer. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Flow

/-- The span of one task's block. -/
abbrev blockSpan : Nat := 8192

/-- The start of block `n`; the prologue and the roles' first events come before block 0. -/
def blockAt (n : Nat) : Nat := 64 + blockSpan * n

/-- The start of input ring step `j` (k-block `j % 128` of task `j / 128`). -/
def ringAt (j : Nat) : Nat := blockAt (j / 128) + 64 + 32 * (j % 128)

/-- Input slot `s`'s empty barrier in CTA `cta`. -/
def inputEmpty (L : Launch) (cta : Nat) (s : Nat) : Loc := Bar.loc L cta ⟨.input, s, false⟩

/-- A loader's successful polls of its CTA's four input empty barriers. -/
def loaderCount (L : Launch) (g : Nat) (es : List Event) : Nat :=
  ∑ s : Fin 4, okPolls (inputEmpty L (g / L.block) s) es

/-- An MMA thread's commits to its CTA's four input empty barriers. -/
def mmaCount (L : Launch) (g : Nat) (es : List Event) : Nat :=
  ∑ s : Fin 4, es.countP (commitsTo (inputEmpty L (g / L.block) s))

/-- A consumer's successful polls of its CTA's two accumulator-full barriers. -/
def consCount (L : Launch) (g : Nat) (es : List Event) : Nat :=
  ∑ j : Fin 2, okPolls (Bar.loc L (g / L.block) ⟨.acc, j, true⟩) es

/-- A scheduler's successful polls of its CTA's response barrier. -/
def schedCount (L : Launch) (g : Nat) (es : List Event) : Nat :=
  okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) es

/-- The round-robin share of slot `s` after `N` blocks, when slot `r` takes the next block. -/
theorem rr_succ {N : Nat} {r : Fin 4} (hr : N % 4 = r.val) (s : Fin 4) :
    (N + 1 + 3 - s.val) / 4 = (N + 3 - s.val) / 4 + if r = s then 1 else 0 := by
  have hs := s.isLt
  split_ifs with h
  · subst h
    omega
  · have : r.val ≠ s.val := fun h' => h (Fin.ext h')
    omega

/-- A read is no successful poll. -/
theorem okPoll_of_rd {m : Loc} {e : Event} {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .rd a bs) : okPoll m e = false := by
  simp [okPoll, sourceWaitSuccess, hk]

/-- An event that is no successful poll of `m` leaves the successful polls on `m` unchanged. -/
theorem okPolls_snoc_zero {m : Loc} {pre : List Event} {e : Event} (h : okPoll m e = false) :
    okPolls m (pre ++ [e]) = okPolls m pre := by
  rw [okPolls_snoc, h]
  simp

namespace Prologue

def Site.vtime : Site → Nat
  | .shfl => 0 | .elect => 2 | .init i => 4 + 2 * i.val | .alloc => 40 | .allocWrite => 42
  | .warpBar => 44 | .fence => 46 | .fenceInit => 48 | .arrive => 50 | .wait => 52
  | .setMaxReg => 54 | .roleElect => 56

/-- A prologue state's time is at most 56. -/
theorem site_vtime_le (s : Site) : Site.vtime s ≤ 56 := by
  cases s with
  | init i =>
    have hi := i.isLt
    show 4 + 2 * i.val ≤ 56
    omega
  | _ => decide

end Prologue

namespace Loader

/-- The time of a loader's next event, after `K` successful empty polls. -/
def vtime (K : Nat) (d : D) : Nat :=
  match d.site with
  | .wait _ => ringAt K
  | .load _ j => ringAt (K - 1) + 2 + 2 * j.val
  | .arrive _ => ringAt (K - 1) + 8
  | .clcWait => blockAt (K / 128 - 1) + 4170
  | .clcLoad => blockAt (K / 128 - 1) + 4172
  | .clcStatus => blockAt (K / 128 - 1) + 4174
  | .clcFirst => blockAt (K / 128 - 1) + 4176
  | .clcFence => blockAt (K / 128 - 1) + 4178
  | .ack => blockAt (K / 128 - 1) + 4180
  | .drain i => blockAt (K / 128 - 1) + 4190 + 2 * i.val
  | .exitArrive | .exitWait | .exit => 0

def exitOff (d : D) : Option Nat :=
  match d.site with
  | .exitArrive => some 0 | .exitWait => some 2 | .exit => some 10
  | _ => none

end Loader

namespace Mma

/-- The time of an MMA thread's next event, after `D` commits to the input empty barriers. -/
def vtime (D : Nat) (d : Mma.D) : Nat :=
  match d.site with
  | .elect => 58
  | .clcWait => blockAt (D / 128) + 20
  | .clcLoad => blockAt (D / 128) + 22
  | .clcStatus => blockAt (D / 128) + 24
  | .clcFirst => blockAt (D / 128) + 26
  | .clcFence => blockAt (D / 128) + 28
  | .ack => blockAt (D / 128) + 30
  | .accWait => blockAt (D / 128) + 32
  | .full _ => ringAt D + 10
  | .mma _ j => ringAt D + 12 + 2 * j.val
  | .commit _ => ringAt D + 20
  | .accCommit => blockAt (D / 128 - 1) + 4160
  | .exitArrive | .exitWait | .exit => 0

def exitOff (d : Mma.D) : Option Nat :=
  match d.site with
  | .exitArrive => some 0 | .exitWait => some 2 | .exit => some 10
  | _ => none

end Mma

namespace Scheduler

/-- The time of a scheduler's next event, after `R` successful response polls. -/
def vtime (R : Nat) (d : Scheduler.D) : Nat :=
  match d.site with
  | .elect => 58
  | .ackWait => blockAt R
  | .tryCancel => blockAt R + 2
  | .arriveTx => blockAt R + 4
  | .clcWait => blockAt R + 6
  | .clcLoad => blockAt (R - 1) + 8
  | .clcStatus => blockAt (R - 1) + 10
  | .clcFirst => blockAt (R - 1) + 12
  | .clcFence => blockAt (R - 1) + 14
  | .ack => blockAt (R - 1) + 16
  | .exitArrive | .exitWait | .exit => 0

def exitOff (d : Scheduler.D) : Option Nat :=
  match d.site with
  | .exitArrive => some 0 | .exitWait => some 2 | .exit => some 10
  | _ => none

end Scheduler

namespace Consumer

/-- The time of a consumer's next event, after `T` successful accumulator-full polls. -/
def vtime (T : Nat) (d : Consumer.D) : Nat :=
  match d.site with
  | .setMaxReg => 58
  | .clcWait => blockAt T + 40
  | .clcLoad => blockAt T + 42
  | .clcStatus => blockAt T + 44
  | .clcFirst => blockAt T + 46
  | .clcFence => blockAt T + 48
  | .clcBar => blockAt T + 50
  | .ack => blockAt T + 52
  | .accWait => blockAt T + 4200
  | .load j => blockAt (T - 1) + 4202 + 4 * j.val
  | .loadWait j => blockAt (T - 1) + 4204 + 4 * j.val
  | .accArrive => blockAt (T - 1) + 4270
  | .drain k => blockAt (T - 1) + 4280 + 64 * k.val
  | .barA k => blockAt (T - 1) + 4282 + 64 * k.val
  | .store k i el => blockAt (T - 1) + 4284 + 64 * k.val + 2 * (4 * i.val + el.val)
  | .barB k => blockAt (T - 1) + 4316 + 64 * k.val
  | .fence k => blockAt (T - 1) + 4318 + 64 * k.val
  | .tma k => blockAt (T - 1) + 4320 + 64 * k.val
  | .commit k => blockAt (T - 1) + 4322 + 64 * k.val
  | .finalDrain => blockAt (T - 1) + 4800
  | .exitArrive | .exitWait | .relinquish | .ldBase | .dealloc | .exit => 0

def exitOff (d : Consumer.D) : Option Nat :=
  match d.site with
  | .exitArrive => some 0 | .exitWait => some 2 | .relinquish => some 4 | .ldBase => some 6
  | .dealloc => some 8 | .exit => some 10
  | _ => none

/-- **The time of a consumer's next event is below the next block.** At `T` successful accumulator
polls, when `T` is `n` plus the accumulator the consumer holds, its time plus one is below the
block after `n`. -/
theorem vtime_lt_block (c : Consumer.D) (n T : Nat) (hT : T = n + Consumer.holds c) :
    Consumer.vtime T c + 1 < blockAt (n + 1) + 32 := by
  simp only [Consumer.holds, Consumer.vtime] at hT ⊢
  cases hs : c.site <;> simp only [hs, blockAt, blockSpan] at hT ⊢ <;> omega

end Consumer

/-- The time of a thread's next event in the sequential schedule, from its own trace. -/
def ThreadD.vtime (L : Launch) (g : Nat) (es : List Event) : ThreadD → Nat
  | .inl p => p.site.vtime
  | .inr (.loader l) => Loader.vtime (loaderCount L g es) l
  | .inr (.mma m) => Mma.vtime (mmaCount L g es) m
  | .inr (.sched s) => Scheduler.vtime (schedCount L g es) s
  | .inr (.cons c) => Consumer.vtime (consCount L g es) c

/-- The offset of a thread's next event within the exit stage, if it is there. -/
def ThreadD.exitOff : ThreadD → Option Nat
  | .inl _ => none
  | .inr (.loader l) => Loader.exitOff l
  | .inr (.mma m) => Mma.exitOff m
  | .inr (.sched s) => Scheduler.exitOff s
  | .inr (.cons c) => Consumer.exitOff c

end PTX.Kernels.Fp16Gemm8192.Proof
