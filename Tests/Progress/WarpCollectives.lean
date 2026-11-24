-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Progress.Common
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Deadlock tests: warp collectives (DEP-ORDER, checklist rows A1, A3–A6, B11)

Each program runs in one warp. Lane 0 and the other lanes branch on `%tid.x` to two different
collective instructions over the same member mask, each followed by `exit`. Every collective
waits for the other lanes of its mask to execute the same instruction (same qualifiers and member
mask), so no lane gets past its collective: each test proves that the empty execution is
`Maximal` and not `Complete`, which is how CORRECT-PROGRESS rejects the program.

* `vote_deadlock` (A3): `vote.sync.all` against `vote.sync.any`, member mask 3, two lanes.
* `ballot_deadlock` (A3): `vote.sync.ballot` against `vote.sync.all`, full mask, 32 lanes.
* `redux_deadlock` (A5): `redux.sync.add.u32` against `redux.sync.min.u32`, member mask 3.
* `shfl_deadlock` (A1): `shfl.sync.up.b32` against `shfl.sync.down.b32`, full mask, 32 lanes.
* `match_deadlock` (A4): `match.any.sync.b32` against `match.all.sync.b32`, member mask 3.
* `elect_barWarp_deadlock` (A6, B11): `elect.sync` in lane 0 against `bar.warp.sync` in lane 1,
  member mask 3: each waits for the other lane to execute its own instruction.

A lane that exits after its own collective does not release the other lane: its exit follows
its own event of the class (`MaskExitK` counts it), and `elect.sync` and `bar.warp.sync` have no
exit clause at all.
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

/-- One CTA of two threads. -/
def L2 : Launch := { grid := 1, block := 2, params := fun _ => none }
/-- One CTA of one full warp. -/
def L32 : Launch := { grid := 1, block := 32, params := fun _ => none }

/-- `setp.eq.u32 %p1, %tid.x, 0; @%p1 bra 4; b; exit; a; exit`: thread 0 runs `a` at position
4, every other thread runs `b` at position 2. -/
def splitK (a b : Op) : Kernel where
  name := "split"
  params := []
  code := [
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 1], [.sreg ⟨.tid, some .x⟩, .imm 0]⟩ },
    { guard := some (1, false), op := .bra 4 false },
    { op := b }, { op := .exit }, { op := a }, { op := .exit }]

theorem warpLane_L2_0 : warpLane L2 0 1 = 1 := rfl
theorem warpLane_L2_1 : warpLane L2 1 0 = 0 := rfl
theorem warpLane_L32 {g : Nat} (hg : g < 32) : warpLane L32 g 0 = 0 := by
  simp [warpLane, laneOf, L32, Nat.mod_eq_of_lt hg]

theorem lt_L2 {g : Nat} (hg : g < L2.threads) : g = 0 ∨ g = 1 := by
  simp [L2, Launch.threads] at hg; omega

theorem lt_L32 {g : Nat} (hg : g < L32.threads) : g < 32 := by
  simpa [L32, Launch.threads] using hg

/-- The first event of a trace. -/
theorem get_first {Y : Execution} {g : Nat} {e : Event} {pcx : Nat}
    (h : Y.tr g = [e] ∨ Y.tr g = [e, ⟨pcx, .exit⟩]) : Y.get (g, 0) = some e := by
  rcases h with h | h <;> simp [Execution.get, h]

/-! ## `vote.sync` -/

def voteOp (m : VoteMode) : Op :=
  .warp ⟨.vote m false, some .pred, [some 2], [.reg 1], some (.imm 3)⟩
def voteK : Kernel := splitK (voteOp .all) (voteOp .any)

theorem vote_trace0 {tr : List Event} {o : Option TState} (h : Run voteK [] L2 0 {} tr o) :
    OneThenExit tr (fun e => ∃ a r, e = ⟨4, .voteMode .all 3 a r⟩) 5 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨r, rfl, rfl⟩ := hf; exact ⟨⟨_, r, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem vote_trace1 {tr : List Event} {o : Option TState} (h : Run voteK [] L2 1 {} tr o) :
    OneThenExit tr (fun e => ∃ a r, e = ⟨2, .voteMode .any 3 a r⟩) 3 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨r, rfl, rfl⟩ := hf; exact ⟨⟨_, r, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem vote_nil {mem0 : Mem0} (Y : Execution) (hY : Consistent L2 voteK [] mem0 Y) :
    ∀ g < L2.threads, Y.tr g = [] := by
  have t0 := vote_trace0 (hY.thr 0 (by decide)).choose_spec
  have t1 := vote_trace1 (hY.thr 1 (by decide)).choose_spec
  intro g hg
  rcases lt_L2 hg with rfl | rfl
  · rcases t0 with h | ⟨e, ⟨a, r, rfl⟩, htr⟩
    · exact h
    · exact (mask_blocked voteClass rfl hY.dependency (get_first htr) rfl (p := ⟨3, .all, a⟩)
        rfl (by simp [Returned, get_first htr, Kind.resume]) (l := 1) (by decide)
        (show (3 : Nat).testBit 1 = true by decide)
        (t1.mono fun e ⟨a, r, he⟩ =>
          ⟨⟨3, .any, a⟩, by rw [he]; rfl, rfl, show VoteMode.any ≠ .all by decide⟩)).elim
  · rcases t1 with h | ⟨e, ⟨a, r, rfl⟩, htr⟩
    · exact h
    · exact (mask_blocked voteClass rfl hY.dependency (get_first htr) rfl (p := ⟨3, .any, a⟩)
        rfl (by simp [Returned, get_first htr, Kind.resume]) (l := 0) (by decide)
        (show (3 : Nat).testBit 0 = true by decide)
        (t0.mono fun e ⟨a, r, he⟩ =>
          ⟨⟨3, .all, a⟩, by rw [he]; rfl, rfl, show VoteMode.all ≠ .any by decide⟩)).elim

/-- A3: `vote.sync.all` in lane 0 against `vote.sync.any` in lane 1 deadlocks. -/
theorem vote_deadlock (mem0 : Mem0) :
    Maximal L2 voteK [] mem0 .empty ∧ ¬ Complete L2 .empty :=
  empty_deadlock (by decide) (by simp) (by decide) (fun Y hY => vote_nil Y hY)

/-! ## `vote.sync.ballot` -/

def ballotOp : Op :=
  .warp ⟨.vote .ballot false, some (.int .b 32), [some 2], [.reg 1], some (.imm 0xffffffff)⟩
def allOp : Op :=
  .warp ⟨.vote .all false, some .pred, [some 2], [.reg 1], some (.imm 0xffffffff)⟩
def ballotK : Kernel := splitK ballotOp allOp

theorem ballot_trace0 {tr : List Event} {o : Option TState} (h : Run ballotK [] L32 0 {} tr o) :
    OneThenExit tr (fun e => ∃ a r, e = ⟨4, .vote 0xffffffff a r⟩) 5 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨r, rfl, rfl⟩ := hf; exact ⟨⟨_, r, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem ballot_trace {g : Nat} (hg : 0 < g) (hg' : g < 32) {tr : List Event}
    {o : Option TState} (h : Run ballotK [] L32 g {} tr o) :
    OneThenExit tr (fun e => ∃ a r, e = ⟨2, .voteMode .all 0xffffffff a r⟩) 3 := by
  interval_cases g <;>
  exact oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨r, rfl, rfl⟩ := hf; exact ⟨⟨_, r, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem ballot_nil {mem0 : Mem0} (Y : Execution) (hY : Consistent L32 ballotK [] mem0 Y) :
    ∀ g < L32.threads, Y.tr g = [] := by
  have t0 := ballot_trace0 (hY.thr 0 (by decide)).choose_spec
  intro g hg
  have hg32 := lt_L32 hg
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · rcases t0 with h | ⟨e, ⟨a, r, rfl⟩, htr⟩
    · exact h
    · have t1 := ballot_trace (g := 1) (by decide) (by decide) (hY.thr 1 (by decide)).choose_spec
      exact (mask_blocked voteClass rfl hY.dependency (get_first htr) rfl
        (p := ⟨0xffffffff, .ballot, a⟩) rfl (by simp [Returned, get_first htr, Kind.resume])
        (l := 1) (by decide) (show (0xffffffff : Nat).testBit 1 = true by decide)
        (t1.mono fun e ⟨a, r, he⟩ =>
          ⟨⟨0xffffffff, .all, a⟩, by rw [he]; rfl, rfl,
            show VoteMode.all ≠ .ballot by decide⟩)).elim
  · rcases ballot_trace hpos hg32 (hY.thr g hg).choose_spec with h | ⟨e, ⟨a, r, rfl⟩, htr⟩
    · exact h
    · refine (mask_blocked voteClass rfl hY.dependency (get_first htr) rfl (pcx := 5)
        (p := ⟨0xffffffff, .all, a⟩) rfl (by simp [Returned, get_first htr, Kind.resume])
        (l := 0) (by decide) (show (0xffffffff : Nat).testBit 0 = true by decide) ?_).elim
      rw [warpLane_L32 hg32]
      exact t0.mono fun e ⟨a, r, he⟩ =>
        ⟨⟨0xffffffff, .ballot, a⟩, by rw [he]; rfl, rfl, show VoteMode.ballot ≠ .all by decide⟩

/-- A3 (ballot): `vote.sync.ballot` in lane 0 against `vote.sync.all` in lanes 1–31 deadlocks. -/
theorem ballot_deadlock (mem0 : Mem0) :
    Maximal L32 ballotK [] mem0 .empty ∧ ¬ Complete L32 .empty :=
  empty_deadlock (by decide) (by simp) (by decide) (fun Y hY => ballot_nil Y hY)

/-! ## `redux.sync` -/

def reduxOp (op : ReduxOp) : Op :=
  .warp ⟨.redux op false false, some (.int .u 32), [some 2], [.imm 1], some (.imm 3)⟩
def reduxK : Kernel := splitK (reduxOp .add) (reduxOp .min)

theorem redux_trace0 {tr : List Event} {o : Option TState} (h : Run reduxK [] L2 0 {} tr o) :
    OneThenExit tr (fun e => ∃ a r, e = ⟨4, .redux .add false 3 a r⟩) 5 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨r, rfl, rfl⟩ := hf; exact ⟨⟨_, r, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem redux_trace1 {tr : List Event} {o : Option TState} (h : Run reduxK [] L2 1 {} tr o) :
    OneThenExit tr (fun e => ∃ a r, e = ⟨2, .redux .min false 3 a r⟩) 3 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨r, rfl, rfl⟩ := hf; exact ⟨⟨_, r, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem redux_nil {mem0 : Mem0} (Y : Execution) (hY : Consistent L2 reduxK [] mem0 Y) :
    ∀ g < L2.threads, Y.tr g = [] := by
  have t0 := redux_trace0 (hY.thr 0 (by decide)).choose_spec
  have t1 := redux_trace1 (hY.thr 1 (by decide)).choose_spec
  intro g hg
  rcases lt_L2 hg with rfl | rfl
  · rcases t0 with h | ⟨e, ⟨a, r, rfl⟩, htr⟩
    · exact h
    · exact (mask_blocked reduxClass rfl hY.dependency (get_first htr) rfl
        (p := ⟨3, (.add, false), a⟩) rfl (by simp [Returned, get_first htr, Kind.resume])
        (l := 1) (by decide) (show (3 : Nat).testBit 1 = true by decide)
        (t1.mono fun e ⟨a, r, he⟩ => ⟨⟨3, (.min, false), a⟩, by rw [he]; rfl, rfl,
          show ((ReduxOp.min, false) : ReduxOp × Bool) ≠ (.add, false) by decide⟩)).elim
  · rcases t1 with h | ⟨e, ⟨a, r, rfl⟩, htr⟩
    · exact h
    · exact (mask_blocked reduxClass rfl hY.dependency (get_first htr) rfl
        (p := ⟨3, (.min, false), a⟩) rfl (by simp [Returned, get_first htr, Kind.resume])
        (l := 0) (by decide) (show (3 : Nat).testBit 0 = true by decide)
        (t0.mono fun e ⟨a, r, he⟩ => ⟨⟨3, (.add, false), a⟩, by rw [he]; rfl, rfl,
          show ((ReduxOp.add, false) : ReduxOp × Bool) ≠ (.min, false) by decide⟩)).elim

/-- A5: `redux.sync.add.u32` in lane 0 against `redux.sync.min.u32` in lane 1 deadlocks. -/
theorem redux_deadlock (mem0 : Mem0) :
    Maximal L2 reduxK [] mem0 .empty ∧ ¬ Complete L2 .empty :=
  empty_deadlock (by decide) (by simp) (by decide) (fun Y hY => redux_nil Y hY)

/-! ## `shfl.sync` -/

def shflOp (m : ShflMode) : Op :=
  .warp ⟨.shfl m, some (.int .b 32), [some 2], [.imm 1, .imm 1, .imm 0], some (.imm 0xffffffff)⟩
def shflK : Kernel := splitK (shflOp .up) (shflOp .down)

theorem shfl_trace0 {tr : List Event} {o : Option TState} (h : Run shflK [] L32 0 {} tr o) :
    OneThenExit tr (fun e => ∃ a b c r ok, e = ⟨4, .shfl .up a b c r ok⟩) 5 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by
      obtain ⟨r, ok, rfl, rfl⟩ := hf; exact ⟨⟨_, _, _, r, ok, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem shfl_trace {g : Nat} (hg : 0 < g) (hg' : g < 32) {tr : List Event} {o : Option TState}
    (h : Run shflK [] L32 g {} tr o) :
    OneThenExit tr (fun e => ∃ a b c r ok, e = ⟨2, .shfl .down a b c r ok⟩) 3 := by
  interval_cases g <;>
  exact oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by
      obtain ⟨r, ok, rfl, rfl⟩ := hf; exact ⟨⟨_, _, _, r, ok, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem shfl_nil {mem0 : Mem0} (Y : Execution) (hY : Consistent L32 shflK [] mem0 Y) :
    ∀ g < L32.threads, Y.tr g = [] := by
  have t0 := shfl_trace0 (hY.thr 0 (by decide)).choose_spec
  intro g hg
  have hg32 := lt_L32 hg
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · rcases t0 with h | ⟨e, ⟨a, b, c, r, ok, rfl⟩, htr⟩
    · exact h
    · have t1 := shfl_trace (g := 1) (by decide) (by decide) (hY.thr 1 (by decide)).choose_spec
      exact (mask_blocked shflClass rfl hY.dependency (get_first htr) rfl
        (p := ⟨2 ^ 32 - 1, .up, a⟩) rfl (by simp [Returned, get_first htr, Kind.resume])
        (l := 1) (by decide) (show (2 ^ 32 - 1 : Nat).testBit 1 = true by decide)
        (t1.mono fun e ⟨a, b, c, r, ok, he⟩ =>
          ⟨⟨2 ^ 32 - 1, .down, a⟩, by rw [he]; rfl, rfl, show ShflMode.down ≠ .up by decide⟩)).elim
  · rcases shfl_trace hpos hg32 (hY.thr g hg).choose_spec with
      h | ⟨e, ⟨a, b, c, r, ok, rfl⟩, htr⟩
    · exact h
    · refine (mask_blocked shflClass rfl hY.dependency (get_first htr) rfl (pcx := 5)
        (p := ⟨2 ^ 32 - 1, .down, a⟩) rfl (by simp [Returned, get_first htr, Kind.resume])
        (l := 0) (by decide) (show (2 ^ 32 - 1 : Nat).testBit 0 = true by decide) ?_).elim
      rw [warpLane_L32 hg32]
      exact t0.mono fun e ⟨a, b, c, r, ok, he⟩ =>
        ⟨⟨2 ^ 32 - 1, .up, a⟩, by rw [he]; rfl, rfl, show ShflMode.up ≠ .down by decide⟩

/-- A1: `shfl.sync.up` in lane 0 against `shfl.sync.down` in lanes 1–31 deadlocks. -/
theorem shfl_deadlock (mem0 : Mem0) :
    Maximal L32 shflK [] mem0 .empty ∧ ¬ Complete L32 .empty :=
  empty_deadlock (by decide) (by simp) (by decide) (fun Y hY => shfl_nil Y hY)

/-! ## `match.sync` -/

def matchOp (all : Bool) : Op :=
  .warp ⟨.match_ all, some (.int .b 32), [some 2], [.imm 5], some (.imm 3)⟩
def matchK : Kernel := splitK (matchOp false) (matchOp true)

theorem match_trace0 {tr : List Event} {o : Option TState} (h : Run matchK [] L2 0 {} tr o) :
    OneThenExit tr (fun e => ∃ a r p, e = ⟨4, .match_ false false 3 a r p⟩) 5 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by
      obtain ⟨r, p, rfl, rfl⟩ := hf; exact ⟨⟨_, r, p, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem match_trace1 {tr : List Event} {o : Option TState} (h : Run matchK [] L2 1 {} tr o) :
    OneThenExit tr (fun e => ∃ a r p, e = ⟨2, .match_ true false 3 a r p⟩) 3 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by
      obtain ⟨r, p, rfl, rfl⟩ := hf; exact ⟨⟨_, r, p, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem match_nil {mem0 : Mem0} (Y : Execution) (hY : Consistent L2 matchK [] mem0 Y) :
    ∀ g < L2.threads, Y.tr g = [] := by
  have t0 := match_trace0 (hY.thr 0 (by decide)).choose_spec
  have t1 := match_trace1 (hY.thr 1 (by decide)).choose_spec
  intro g hg
  rcases lt_L2 hg with rfl | rfl
  · rcases t0 with h | ⟨e, ⟨a, r, p, rfl⟩, htr⟩
    · exact h
    · exact (mask_blocked matchClass rfl hY.dependency (get_first htr) rfl
        (p := ⟨3, (false, false), a⟩) rfl (by simp [Returned, get_first htr, Kind.resume])
        (l := 1) (by decide) (show (3 : Nat).testBit 1 = true by decide)
        (t1.mono fun e ⟨a, r, p, he⟩ => ⟨⟨3, (true, false), a⟩, by rw [he]; rfl, rfl,
          show ((true, false) : Bool × Bool) ≠ (false, false) by decide⟩)).elim
  · rcases t1 with h | ⟨e, ⟨a, r, p, rfl⟩, htr⟩
    · exact h
    · exact (mask_blocked matchClass rfl hY.dependency (get_first htr) rfl
        (p := ⟨3, (true, false), a⟩) rfl (by simp [Returned, get_first htr, Kind.resume])
        (l := 0) (by decide) (show (3 : Nat).testBit 0 = true by decide)
        (t0.mono fun e ⟨a, r, p, he⟩ => ⟨⟨3, (false, false), a⟩, by rw [he]; rfl, rfl,
          show ((false, false) : Bool × Bool) ≠ (true, false) by decide⟩)).elim

/-- A4: `match.any.sync` in lane 0 against `match.all.sync` in lane 1 deadlocks. -/
theorem match_deadlock (mem0 : Mem0) :
    Maximal L2 matchK [] mem0 .empty ∧ ¬ Complete L2 .empty :=
  empty_deadlock (by decide) (by simp) (by decide) (fun Y hY => match_nil Y hY)

/-! ## `elect.sync` against `bar.warp.sync` -/

def electOp : Op := .warp ⟨.elect, none, [none, some 2], [], some (.imm 3)⟩
def barWarpOp : Op := .warp ⟨.barWarp, none, [], [], some (.imm 3)⟩
def electK : Kernel := splitK electOp barWarpOp

theorem elect_trace0 {tr : List Event} {o : Option TState} (h : Run electK [] L2 0 {} tr o) :
    OneThenExit tr (fun e => ∃ inst leader, e = ⟨4, .elect 3 inst leader⟩) 5 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by
      obtain ⟨inst, leader, rfl, rfl⟩ := hf; exact ⟨⟨inst, leader, rfl⟩, _, rfl, rfl, rfl⟩) h

theorem elect_trace1 {tr : List Event} {o : Option TState} (h : Run electK [] L2 1 {} tr o) :
    OneThenExit tr (fun e => ∃ inst, e = ⟨2, .warpBar 3 inst⟩) 3 :=
  oneThenExit_of_run (fun _ _ _ h => run_of_tau rfl (run_of_tau rfl h)) rfl
    (fun e o hf => by obtain ⟨inst, rfl, rfl⟩ := hf; exact ⟨⟨inst, rfl⟩, _, rfl, rfl, rfl⟩) h

/-- No event of a trace that runs one event satisfying `P` and an exit satisfies `Q`, when no
event satisfying `P` does and an exit does not. -/
theorem oneThenExit_none {tr : List Event} {P Q : Event → Prop} {pcx : Nat}
    (h : OneThenExit tr P pcx) (hPQ : ∀ e, P e → ¬ Q e) (hx : ¬ Q ⟨pcx, .exit⟩) :
    ∀ e ∈ tr, ¬ Q e := by
  rcases h with rfl | ⟨e0, hP, rfl | rfl⟩
  · simp
  · simpa using hPQ e0 hP
  · simpa using ⟨hPQ e0 hP, hx⟩

theorem elect_nil {mem0 : Mem0} (Y : Execution) (hY : Consistent L2 electK [] mem0 Y) :
    ∀ g < L2.threads, Y.tr g = [] := by
  have t0 := elect_trace0 (hY.thr 0 (by decide)).choose_spec
  have t1 := elect_trace1 (hY.thr 1 (by decide)).choose_spec
  intro g hg
  rcases lt_L2 hg with rfl | rfl
  · rcases t0 with h | ⟨e, ⟨inst, leader, rfl⟩, htr⟩
    · exact h
    · exfalso
      have he := get_first htr
      have hn : Need.node (fun x => ∃ j pc leader, x = .thread (warpLane L2 0 1, j) ∧
          Y.get (warpLane L2 0 1, j) = some ⟨pc, .elect 3 inst leader⟩) ∈ Needs L2 Y (0, 0) := by
        simp only [Needs, he, KindNeeds]
        exact List.mem_map.mpr ⟨1, by decide, rfl⟩
      obtain ⟨x, -, j, pc, ld, rfl, hj⟩ :=
        hY.dependency.ready _ (by simp [Returned, he, Kind.resume]) _ hn
      rw [warpLane_L2_0] at hj
      exact oneThenExit_none t1 (Q := fun e => ∃ pc ld, e = ⟨pc, .elect 3 inst ld⟩)
        (fun e ⟨i, he⟩ ⟨pc, ld, he'⟩ => by rw [he] at he'; cases he') (by simp) _
        (List.mem_of_getElem? hj) ⟨pc, ld, rfl⟩
  · rcases t1 with h | ⟨e, ⟨inst, rfl⟩, htr⟩
    · exact h
    · exfalso
      have he := get_first htr
      have hn : Need.node (fun x => ∃ j, x = .thread (warpLane L2 1 0, j) ∧
          Y.WarpBar (warpLane L2 1 0, j) 3 inst) ∈ Needs L2 Y (1, 0) := by
        simp only [Needs, he, KindNeeds]
        exact List.mem_map.mpr ⟨0, by decide, rfl⟩
      obtain ⟨x, -, j, rfl, pc, hj⟩ :=
        hY.dependency.ready _ (by simp [Returned, he, Kind.resume]) _ hn
      rw [warpLane_L2_1] at hj
      exact oneThenExit_none t0 (Q := fun e => ∃ pc, e = ⟨pc, .warpBar 3 inst⟩)
        (fun e ⟨i, ld, he⟩ ⟨pc, he'⟩ => by rw [he] at he'; cases he') (by simp) _
        (List.mem_of_getElem? hj) ⟨pc, rfl⟩

/-- A6 and B11: `elect.sync` in lane 0 against `bar.warp.sync` in lane 1 deadlocks; each waits
for the other lane to execute its own instruction, and neither has an exit clause. -/
theorem elect_barWarp_deadlock (mem0 : Mem0) :
    Maximal L2 electK [] mem0 .empty ∧ ¬ Complete L2 .empty :=
  empty_deadlock (by decide) (by simp) (by decide) (fun Y hY => elect_nil Y hY)

end

end PTX.Tests.Progress
