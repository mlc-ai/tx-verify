-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.WarpUniform
public import Lemmas.Flow.Determinism
public import Lemmas.Order.OrderBaseCausality
public import Core.Assumption.PollAgree
public import Lemmas.Flow.PollSynced

/-! Litmus tests for ERR-NONUNIFORM-GUARD (may-coincide executions, the execution-dependency order
EXT-DEPENDENCY-ORDER, the poll exemption ASM-POLL-AGREE), on one warp of two lanes.

`reconverge`: `@p bra L; mov; L: @q bra.uni X` with `p` true in lane 0 only and `q` true in lane 0
only: the lanes reach the `bra.uni` on different paths, with nothing ordering them, and are
compared: flagged (`reconverge_flagged`).

`counted`: a loop of two rounds on a warp-uniform counter `i` with `setp p, i == 0; @p bra.uni` and
no blocking instruction between the rounds. Lane 0's first execution (guard true) and lane 1's
second (guard false) are not ordered: flagged (`counted_flagged`). The rule is conservative here:
lanes that never diverged may execute their rounds in step.

`rounds`: a loop of two rounds. In round 1 only lane 0 reaches the `bra.uni` (guard true); in
round 2 both lanes reach it (guard false). Nothing orders lane 0's first execution and lane 1's
second: flagged (`rounds_flagged`). A `pollAgreeAt` hook selecting the branch exempts nothing
there, since the instruction before it is no poll (`rounds_hook_flagged`).

`roundsBar`: the same loop with `fence; bar.sync 0; fence` after the branch. The barrier orders
lane 0's first round before lane 1's second (and conversely): not flagged
(`roundsBar_not_flagged`).

`roundsElect`: the loop of `rounds` with a full-mask `elect.sync` and a fence at the end of each
round. Lane 0 performs its first election after its first execution of the branch. That election
fills a need of lane 1's first election (its event of the same instance), and the return of lane
1's election precedes its fence, before its second execution. The election is not in
MEM-BASE-CAUSALITY but is in the execution-dependency order, so the two executions are ordered: not
flagged, without any assumption (`roundsElect_not_flagged`). The fence after the election is
needed: the order reaches the issue of an event, and the return of an election precedes only the
later events of its thread.

`ownPoll`: each lane initializes its own mbarrier, only lane 0 arrives on its own, and both lanes
poll their own object with parity 0 and branch with `@P bra.uni`. Lane 0's poll succeeds and lane
1's fails: a real divergence, flagged (`ownPoll_flagged`).

`sharedPoll`: both lanes poll one mbarrier with one parity; lane 0's poll fails and lane 1's
succeeds. Without an assumption the branch executions are compared and flagged
(`sharedPoll_flagged`); with `pollAgreeAt` selecting the branch the pair is exempt
(`sharedPoll_exempt`), by the assumption only: nothing checks that the two polls test the same
phase or run at the same instant.

`arriveAfter` (a conservative case): `try_wait p, [M], 0; mov; @p bra.uni DONE; @lane0 arrive [M]`.
Lane 0's poll fails and it arrives after its branch; lane 1's poll then succeeds. On hardware
lane 1's branch follows lane 0's, but the model orders an mbarrier release only before the
events after the acquiring wait, and lane 1 performs none before its branch: flagged
(`arriveAfter_flagged`).

`warpgroupMaxReg` (two warps of one warpgroup, a CTA of 64 threads): warp 0 skips a guarded
`setmaxnreg` and warp 1 executes it; each warp is uniform, but the warpgroup is not: flagged
(`warpgroupMaxReg_flagged`, the warpgroup scope of ERR-NONUNIFORM-GUARD). A `pollAgreeAt` hook
selecting the `setmaxnreg` position exempts nothing there, since the exemption applies only to a
`bra.uni` after a poll (`maxReg_not_pollAgreeExempt`): still flagged
(`warpgroupMaxReg_hook_flagged`).

`phasePoll`: both lanes poll one mbarrier at one position with the parity of their lane index and
branch with `@P bra.uni`. Lane 0's poll (parity 0) fails and lane 1's (parity 1) succeeds, with
nothing ordering them.

* Without an assumption: flagged (`phasePoll_flagged`).
* With `pollAgreeAt` selecting the branch, polls of one object are exempt whatever their
  parities: not flagged (`phasePoll_not_flagged`, through `not_warpDivergent_synced`). -/

namespace PTX.Tests.WarpUniformLitmus
open PTX

/-- One CTA of two threads: one warp. -/
def L2 : Launch := { grid := 1, block := 2, params := fun _ => none }

theorem sameWarp01 : SameWarp L2 0 1 :=
  ⟨⟨by simp [L2, Launch.threads], by simp [L2, Launch.threads], by simp [L2]⟩, by simp [L2]⟩

theorem threads_eq : L2.threads = 2 := by simp [L2, Launch.threads]

/-! ## A walk on a complete trace bounds every walk on a prefix -/

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem fires_exit {pc : Nat} {m : Tmpl} {pc' : Nat} {o : Option TState}
    (h : Fires pc m ⟨pc', .exit⟩ o) : o = none := by
  cases m <;> simp [Fires] at h
  exact h.2

/-- A walk on a prefix of the events of a walk ending in an exit records a prefix of its
records. -/
theorem Walk.prefix_of_exit {t : TState} {es es' : List Event} {vs vs' : List Visit}
    (h : Walk K A L g t es vs) (h' : Walk K A L g t es' vs') (hes : es <+: es')
    (hfin : ∃ pc, es'.getLast? = some ⟨pc, .exit⟩) : vs <+: vs' := by
  induction h generalizing es' vs' with
  | stop => exact List.nil_prefix
  | @tau t t1 es vs ht hw ih =>
    cases h' with
    | stop => simp at hfin
    | tau ht' hw' =>
      obtain rfl := PTX.tau_det ht ht'
      exact List.cons_prefix_cons.mpr ⟨rfl, ih hw' hes hfin⟩
    | ev he' _ => exact absurd ht (PTX.not_tau_of_stops (PTX.stops_of_estep he'))
    | last he' => exact absurd ht (PTX.not_tau_of_stops (PTX.stops_of_estep he'))
  | @ev t t1 e es vs he hw ih =>
    cases h' with
    | stop => simp at hes
    | tau ht' _ => exact absurd ht' (PTX.not_tau_of_stops (PTX.stops_of_estep he))
    | @ev _ t2 e' es'' vs'' he' hw' =>
      obtain ⟨rfl, hes'⟩ := List.cons_prefix_cons.mp hes
      have := PTX.estep_det he he'
      cases this
      refine List.cons_prefix_cons.mpr ⟨rfl, ih hw' hes' ?_⟩
      obtain ⟨pc, hl⟩ := hfin
      cases es'' with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hl
        subst hl
        obtain ⟨m, -, hf⟩ := he
        cases fires_exit hf
      | cons x xs => exact ⟨pc, by simpa [List.getLast?_cons] using hl⟩
    | last he' =>
      obtain ⟨rfl, -⟩ := List.cons_prefix_cons.mp hes
      cases PTX.estep_det he he'
  | @last t e he =>
    cases h' with
    | stop => simp at hes
    | tau ht' _ => exact absurd ht' (PTX.not_tau_of_stops (PTX.stops_of_estep he))
    | ev he' _ =>
      obtain ⟨rfl, -⟩ := List.cons_prefix_cons.mp hes
      cases PTX.estep_det he he'
    | last he' =>
      obtain ⟨rfl, -⟩ := List.cons_prefix_cons.mp hes
      exact List.prefix_refl _

end

/-! ## Unordered records -/

/-- A record before which the second thread performs no event is not ordered after anything. -/
theorem not_before_of_zero {L : Launch} {K : Kernel} {X : Execution} {g h i j : Nat}
    {vg vh : List Visit} (h0 : Visit.events vh j = 0) : ¬ VisitBefore L K X g vg i h vh j := by
  rintro ⟨a, b, -, hb, -⟩
  omega

theorem get_lt {X : Execution} {e : EvId} {ev : Event} (h : X.get e = some ev) :
    e.2 < (X.tr e.1).length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- The source of a dependency is an event: every step out of an issue node starts at a present
event. -/
theorem dep_src {L : Launch} {K : Kernel} {X : Execution} {e f : EvId}
    (h : DepBefore L K X e f) : e.2 < (X.tr e.1).length := by
  obtain ⟨⟨c, b⟩, hs, -⟩ := Relation.TransGen.head'_iff.mp h
  rcases hs with hs | ⟨-, -, i, j, hi, -, hij⟩
  · simp only [DepStep, StageOrder, IssueStage] at hs
    rcases hs with ⟨⟨-, -, -, ev, hev⟩ | ⟨h1, -⟩⟩ | ⟨-, -, -, -, -, -, ⟨ev, hev⟩, -⟩ |
      ⟨-, -, -, -, -, -, ⟨ev, hev⟩, -⟩ | ⟨h1, -⟩
    · exact get_lt hev
    · cases h1
    · exact get_lt hev
    · exact get_lt hev
    · cases h1
  · cases hi
    obtain ⟨h1, h2, h3⟩ := hij
    rw [h1]
    omega

/-- Nothing precedes the issue of a thread's first event: every step into an issue node is
program order or a return before a later event of its thread. -/
theorem dep_tgt_pos {L : Launch} {K : Kernel} {X : Execution} {e f : EvId}
    (h : DepBefore L K X e f) : 0 < f.2 := by
  obtain ⟨⟨c, b⟩, -, hs⟩ := Relation.TransGen.tail'_iff.mp h
  rcases hs with hs | ⟨-, -, i, j, -, hj, hij⟩
  · simp only [DepStep, StageOrder, IssueStage] at hs
    rcases hs with ⟨⟨-, -, h1, -⟩ | ⟨-, -, hse⟩⟩ | ⟨-, -, i, p, -, h1, -⟩ | ⟨-, h1, -⟩ |
      ⟨-, -, w, j, -, hj, hwj, -⟩
    · cases h1
    · rcases c with _ | ⟨i, p⟩ <;> simp [StageEdge] at hse
    · cases h1
    · cases h1
    · cases hj
      obtain ⟨-, h2, -⟩ := hwj
      omega
  · cases hj
    obtain ⟨-, h2, -⟩ := hij
    omega

/-- A record at or after which the first thread performs no event is not ordered before
anything. -/
theorem not_before_of_end {L : Launch} {K : Kernel} {X : Execution} {g h i j : Nat}
    {vg vh : List Visit} (hl : (X.tr g).length ≤ Visit.events vg i) :
    ¬ VisitBefore L K X g vg i h vh j := by
  rintro ⟨a, b, ha, -, hab⟩
  have := dep_src hab
  simp only at this
  omega

/-! ## `reconverge`: lanes on different paths are compared -/

def reconverge : Kernel where
  name := "reconverge"
  params := []
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 2], [.reg 1, .imm 0]⟩ },
    { guard := some (2, false), op := .bra 4 false },
    { op := .move ⟨.scalar, .int .b 32, [some 3], [.imm 0]⟩ },
    { guard := some (2, false), op := .bra 5 true },
    { op := .ret }]

def exitX (pc : Nat) : Execution where
  tr
    | 0 => [⟨pc, .exit⟩]
    | 1 => [⟨pc, .exit⟩]
    | _ => []
  rf _ _ := none
  objects _ := []

/-- A local record without a guard. -/
def lv (pc : Nat) : Visit := ⟨pc, none, none, none⟩

/-- A record with a guard value. -/
def gv (pc : Nat) (b : Bool) : Visit := ⟨pc, some b, none, none⟩

/-- A record of an unguarded step with an event. -/
def fv (pc : Nat) (e : Kind) : Visit := ⟨pc, none, some ⟨pc, e⟩, none⟩

def reconv0 : List Visit := [lv 0, lv 1, lv 2, gv 4 true, fv 5 .exit]

def reconv1 : List Visit :=
  [lv 0, lv 1, lv 2, lv 3, gv 4 false, fv 5 .exit]

theorem reconv_walk0 : Walk reconverge [] L2 0 {} ((exitX 5).tr 0) reconv0 :=
  .tau rfl (.tau rfl (.tau rfl (.tau rfl (.last ⟨_, rfl, rfl, rfl⟩))))

theorem reconv_walk1 : Walk reconverge [] L2 1 {} ((exitX 5).tr 1) reconv1 :=
  .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.last ⟨_, rfl, rfl, rfl⟩)))))

/-- **Lanes reaching a `bra.uni` on different paths and disagreeing: flagged.** -/
theorem reconverge_flagged : WarpDivergent L2 reconverge [] (exitX 5) := by
  refine ⟨0, 1, by simp [threads_eq], by simp [threads_eq], by decide, _, _, _, _,
    List.prefix_refl _, List.prefix_refl _, reconv_walk0, reconv_walk1, 3, 4, 4, _, _, rfl, rfl,
    rfl, rfl, sameWarp01, .inl ⟨true, false, rfl, rfl, by decide⟩, not_before_of_zero rfl,
    not_before_of_zero rfl, not_pollAgreeExempt (by simp)⟩

/-! ## `rounds`: a later round of one lane may coincide with an earlier round of another -/

def rounds : Kernel where
  name := "rounds"
  params := []
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .move ⟨.scalar, .int .b 32, [some 2], [.imm 0]⟩ },
    { op := .int ⟨.setp .ne none, .int .u 32, false, [some 3], [.reg 1, .imm 0]⟩ },
    { op := .int ⟨.setp .ne none, .int .u 32, false, [some 4], [.reg 2, .imm 0]⟩ },
    { guard := some (4, false), op := .bra 6 false },
    { guard := some (3, false), op := .bra 8 false },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 5], [.reg 2, .imm 0]⟩ },
    { guard := some (5, false), op := .bra 8 true },
    { op := .int ⟨.add, .int .u 32, false, [some 2], [.reg 2, .imm 1]⟩ },
    { op := .int ⟨.setp .lt none, .int .u 32, false, [some 6], [.reg 2, .imm 2]⟩ },
    { guard := some (6, false), op := .bra 2 false },
    { op := .ret }]

/-- Lane 0: round 1 reaches the `bra.uni` (guard true), round 2 too (guard false). -/
def rounds0 : List Visit :=
  [lv 0, lv 1, lv 2, lv 3, lv 4, lv 5, lv 6, gv 7 true, lv 8, lv 9, lv 10,
    lv 2, lv 3, lv 4, lv 6, gv 7 false, lv 8, lv 9, lv 10, fv 11 .exit]

/-- Lane 1: round 1 skips the `bra.uni`, round 2 reaches it (guard false). -/
def rounds1 : List Visit :=
  [lv 0, lv 1, lv 2, lv 3, lv 4, lv 5, lv 8, lv 9, lv 10,
    lv 2, lv 3, lv 4, lv 6, gv 7 false, lv 8, lv 9, lv 10, fv 11 .exit]

/-- An assumption selecting the `bra.uni` of `rounds` (position 7), which follows no poll. -/
def roundsHook : Assumption :=
  Assumption.pollAgreeAt "litmus-poll-agree-rounds" [7] "Selects a branch after no poll."

theorem rounds_walk0 (A : List Assumption) (hA : A = [] ∨ A = [roundsHook]) :
    Walk rounds A L2 0 {} ((exitX 11).tr 0) rounds0 := by
  rcases hA with rfl | rfl <;>
  exact .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.tau rfl (.last ⟨_, rfl, rfl, rfl⟩)))))))))))))))))))

theorem rounds_walk1 (A : List Assumption) (hA : A = [] ∨ A = [roundsHook]) :
    Walk rounds A L2 1 {} ((exitX 11).tr 1) rounds1 := by
  rcases hA with rfl | rfl <;>
  exact .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.last ⟨_, rfl, rfl, rfl⟩)))))))))))))))))

/-- **Lane 0's first execution (guard true) and lane 1's second (guard false) are unordered:
flagged.** Conservative: lane 0 can be descheduled at the branch while lane 1 runs on to its
second round, so a scheduler may group the two executions. -/
theorem rounds_flagged : WarpDivergent L2 rounds [] (exitX 11) := by
  refine ⟨0, 1, by simp [threads_eq], by simp [threads_eq], by decide, _, _, _, _,
    List.prefix_refl _, List.prefix_refl _, rounds_walk0 [] (.inl rfl), rounds_walk1 [] (.inl rfl),
    7, 13, 7, _, _, rfl, rfl, rfl, rfl, sameWarp01, .inl ⟨true, false, rfl, rfl, by decide⟩,
    not_before_of_zero rfl, not_before_of_zero rfl, not_pollAgreeExempt (by simp)⟩

/-- **A `pollAgreeAt` hook selecting a `bra.uni` that follows no poll exempts nothing: still
flagged.** -/
theorem rounds_hook_flagged : WarpDivergent L2 rounds [roundsHook] (exitX 11) := by
  refine ⟨0, 1, by simp [threads_eq], by simp [threads_eq], by decide, _, _, _, _,
    List.prefix_refl _, List.prefix_refl _, rounds_walk0 _ (.inr rfl), rounds_walk1 _ (.inr rfl),
    7, 13, 7, _, _, rfl, rfl, rfl, rfl, sameWarp01, .inl ⟨true, false, rfl, rfl, by decide⟩,
    not_before_of_zero rfl, not_before_of_zero rfl, ?_⟩
  rintro ⟨-, ⟨dst, neg, tgt, prev, base, off, par, acq, sc, -, hp, hop⟩, -⟩
  simp only [rounds, Nat.add_one_sub_one, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at hp
  subst hp
  cases hop

/-! ## `counted`: rounds on a uniform counter with nothing between them are compared -/

/-- `mov i, 0; L: setp.eq p, i, 0; @p bra.uni N; N: add i, i, 1; setp.lt q, i, 2; @q bra L; ret`. -/
def counted : Kernel where
  name := "counted"
  params := []
  code := [
    { op := .move ⟨.scalar, .int .b 32, [some 2], [.imm 0]⟩ },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 5], [.reg 2, .imm 0]⟩ },
    { guard := some (5, false), op := .bra 3 true },
    { op := .int ⟨.add, .int .u 32, false, [some 2], [.reg 2, .imm 1]⟩ },
    { op := .int ⟨.setp .lt none, .int .u 32, false, [some 6], [.reg 2, .imm 2]⟩ },
    { guard := some (6, false), op := .bra 1 false },
    { op := .ret }]

/-- Each lane: round 1 reaches the `bra.uni` with guard true, round 2 with guard false. -/
def cnt : List Visit :=
  [lv 0, lv 1, gv 2 true, lv 3, lv 4, lv 5, lv 1, gv 2 false, lv 3, lv 4,
    lv 5, fv 6 .exit]

theorem cnt_walk (x : Nat) (hx : x < 2) : Walk counted [] L2 x {} ((exitX 6).tr x) cnt := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
  exact .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.tau rfl (.tau rfl (.last ⟨_, rfl, rfl, rfl⟩)))))))))))

/-- **Lane 0's first round (guard true) and lane 1's second (guard false) on a uniform counter,
with no blocking instruction between the rounds: flagged.** Conservative: lanes that never
diverged may execute their rounds in step, but nothing in the model orders them. -/
theorem counted_flagged : WarpDivergent L2 counted [] (exitX 6) := by
  refine ⟨0, 1, by simp [threads_eq], by simp [threads_eq], by decide, _, _, _, _,
    List.prefix_refl _, List.prefix_refl _, cnt_walk 0 (by decide), cnt_walk 1 (by decide), 2, 7, 2,
    _, _, rfl, rfl, rfl, rfl, sameWarp01, .inl ⟨true, false, rfl, rfl, by decide⟩,
    not_before_of_zero rfl, not_before_of_zero rfl, not_pollAgreeExempt (by simp)⟩

/-! ## `roundsBar`: a barrier between the rounds orders them -/

/-- `fence.proxy.async.shared::cta`. -/
def fpaOp : Op := .fence (.proxy (.async (some (.shared .cta))))

/-- The event of `fence.proxy.async.shared::cta`. -/
def fpa : Kind := .fenceProxy (.async (some (.shared .cta))) none

def roundsBar : Kernel where
  name := "roundsBar"
  params := []
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .move ⟨.scalar, .int .b 32, [some 2], [.imm 0]⟩ },
    { op := .int ⟨.setp .ne none, .int .u 32, false, [some 3], [.reg 1, .imm 0]⟩ },
    { op := .int ⟨.setp .ne none, .int .u 32, false, [some 4], [.reg 2, .imm 0]⟩ },
    { guard := some (4, false), op := .bra 6 false },
    { guard := some (3, false), op := .bra 8 false },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 5], [.reg 2, .imm 0]⟩ },
    { guard := some (5, false), op := .bra 8 true },
    { op := fpaOp },
    { op := .barSync (.imm 0) true },
    { op := fpaOp },
    { op := .int ⟨.add, .int .u 32, false, [some 2], [.reg 2, .imm 1]⟩ },
    { op := .int ⟨.setp .lt none, .int .u 32, false, [some 6], [.reg 2, .imm 2]⟩ },
    { guard := some (6, false), op := .bra 2 false },
    { op := .ret }]

/-- One round's events: a fence, the barrier, a fence. -/
def roundEvs : List Event := [⟨8, fpa⟩, ⟨9, .bar 0 none⟩, ⟨10, fpa⟩]

def barX : Execution where
  tr
    | 0 => roundEvs ++ roundEvs ++ [⟨14, .exit⟩]
    | 1 => roundEvs ++ roundEvs ++ [⟨14, .exit⟩]
    | _ => []
  rf _ _ := none
  objects _ := []
  barriers
    | 0 => [.arrival 0 0 none [(0, (0, 1)), (1, (1, 1))], .arrival 0 0 none [(0, (0, 4)), (1, (1,
      4))]]
    | _ => []


/-- The records of one round's tail: the fence, the barrier, the fence and the loop. -/
def tailR : List Visit := [fv 8 fpa, fv 9 (.bar 0 none), fv 10 fpa, lv 11, lv 12, lv 13]

def bar0 : List Visit :=
  [lv 0, lv 1, lv 2, lv 3, lv 4, lv 5, lv 6, gv 7 true] ++ tailR ++
    [lv 2, lv 3, lv 4, lv 6, gv 7 false] ++ tailR ++ [fv 14 .exit]

def bar1 : List Visit :=
  [lv 0, lv 1, lv 2, lv 3, lv 4, lv 5] ++ tailR ++
    [lv 2, lv 3, lv 4, lv 6, gv 7 false] ++ tailR ++ [fv 14 .exit]

theorem bar_walk0 : Walk roundsBar [] L2 0 {} (barX.tr 0) bar0 :=
  .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩
    (.tau rfl (.tau rfl (.tau rfl
    (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩
    (.tau rfl (.tau rfl (.tau rfl (.last ⟨_, rfl, rfl, rfl⟩)))))))))))))))))))))))))

theorem bar_walk1 : Walk roundsBar [] L2 1 {} (barX.tr 1) bar1 :=
  .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩
    (.tau rfl (.tau rfl (.tau rfl
    (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩
    (.tau rfl (.tau rfl (.tau rfl (.last ⟨_, rfl, rfl, rfl⟩)))))))))))))))))))))))

/-- Each lane's first barrier event fills a need of each lane's first barrier event: its
arrival in the same record. -/
theorem bar_witness {x y : Nat} (hx : x < 2) (hy : y < 2) :
    Witness L2 barX (.thread (x, 1)) (y, 1) := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
  · exact Witness.of_need L2 (List.mem_append_left _ (List.mem_map.mpr ⟨0, by decide, rfl⟩))
      ⟨_, rfl⟩ ⟨0, _, _, rfl, by decide, rfl, rfl, .inl (by decide)⟩
  · exact Witness.of_need L2 (List.mem_append_left _ (List.mem_map.mpr ⟨0, by decide, rfl⟩))
      ⟨_, rfl⟩ ⟨0, _, _, rfl, by decide, rfl, rfl, .inl (by decide)⟩
  · exact Witness.of_need L2 (List.mem_append_left _ (List.mem_map.mpr ⟨1, by decide, rfl⟩))
      ⟨_, rfl⟩ ⟨0, _, _, rfl, by decide, rfl, rfl, .inl (by decide)⟩
  · exact Witness.of_need L2 (List.mem_append_left _ (List.mem_map.mpr ⟨1, by decide, rfl⟩))
      ⟨_, rfl⟩ ⟨0, _, _, rfl, by decide, rfl, rfl, .inl (by decide)⟩

/-- The trace order of the lanes' barrier events and the fences after them. -/
theorem bar_trace {x : Nat} (hx : x < 2) {a b : Nat} (hab : a < b) (hb : b < 7) :
    TraceBefore barX (x, a) (x, b) := by
  refine ⟨rfl, hab, ?_⟩
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> exact hb

/-- The first barrier orders the fence before it in one lane before the fence after it in the
other: the fence precedes the lane's barrier event, which fills a need of the other lane's
barrier event, whose return precedes the fence after it. -/
theorem bar_dep {x y : Nat} (hx : x < 2) (hy : y < 2) :
    DepBefore L2 roundsBar barX (x, 0) (y, 2) := by
  have hg : barX.get (y, 1) = some ⟨9, .bar 0 none⟩ := by
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> rfl
  have h01 : TraceBefore barX (x, 0) (x, 1) := bar_trace hx Nat.zero_lt_one (by decide)
  have h12 : TraceBefore barX (y, 1) (y, 2) := bar_trace hy Nat.one_lt_two (by decide)
  exact .tail (.tail (.single (.inr ⟨rfl, rfl, _, _, rfl, rfl, h01⟩))
    (.inl (DepStep.of_witness L2 (bar_witness hx hy))))
    (.inl (DepStep.of_resumes L2 (Resumes.of_blocking (b := false) hg rfl h12)))

/-- The two records disagree, as a Boolean. -/
def disB (x y : Visit) : Bool :=
  (match x.guard, y.guard with
    | some b, some b' => b != b'
    | _, _ => false) ||
  (match x.index, y.index with
    | some a, some c => a != c
    | _, _ => false)

theorem disB_of {x y : Visit} (h : x.Disagree y) : disB x y = true := by
  rcases h with ⟨b, b', h1, h2, h3⟩ | ⟨a, c, h1, h2, h3⟩ <;> simp [disB, h1, h2, h3]

/-- Every pair of disagreeing records at one position has one record at or before the first
event of its lane and the other after the `n + 1`-th event of its lane. -/
def apart (n : Nat) (va vb : List Visit) : Bool :=
  (List.range va.length).all fun i => (List.range vb.length).all fun j =>
    match va[i]?, vb[j]? with
    | some x, some y =>
      !(x.pc == y.pc && disB x y) ||
        (Visit.events va i == 0 && n < Visit.events vb j) ||
        (Visit.events vb j == 0 && n < Visit.events va i)
    | _, _ => true

theorem apart_spec {n : Nat} {va vb : List Visit} (h : apart n va vb = true) {i j : Nat}
    {x y : Visit} (hx : va[i]? = some x) (hy : vb[j]? = some y) (hp : x.pc = y.pc)
    (hd : x.Disagree y) :
    (Visit.events va i = 0 ∧ n < Visit.events vb j) ∨
      (Visit.events vb j = 0 ∧ n < Visit.events va i) := by
  have hi := (List.getElem?_eq_some_iff.mp hx).1
  have hj := (List.getElem?_eq_some_iff.mp hy).1
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  simp only [hx, hy, hp, beq_self_eq_true, disB_of hd, Bool.true_and, Bool.not_true,
    Bool.false_or] at h2
  simpa [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h2

/-- The finite check behind `roundsBar_not_flagged`. -/
theorem bar_apart : apart 2 bar0 bar1 = true := by decide

/-- A record of a walk on a prefix is the record of the complete walk, after the same events. -/
theorem get_prefix {l l' : List Visit} {n : Nat} {v : Visit} (hp : l <+: l')
    (hv : l[n]? = some v) : l'[n]? = some v ∧ Visit.events l n = Visit.events l' n := by
  obtain ⟨tl, rfl⟩ := hp
  have hlt := (List.getElem?_eq_some_iff.mp hv).1
  refine ⟨by rw [List.getElem?_append_left hlt]; exact hv, ?_⟩
  unfold Visit.events
  rw [List.take_append_of_le_length hlt.le]

/-- **With a barrier between the rounds, the loop is not flagged.** -/
theorem roundsBar_not_flagged : ¬ WarpDivergent L2 roundsBar [] barX := by
  rintro ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hvi, hvj, hpi,
    hpj, -, hd, hng, hnh, -⟩
  rw [threads_eq] at hg hh
  -- every walk is a prefix of the complete one: compare the complete walks
  have cmp : ∀ (x y : Nat) (vx vy : List Visit) (i j : Nat) (u w : Visit), x < 2 → y < 2 →
      vx[i]? = some u → vy[j]? = some w → u.pc = w.pc → u.Disagree w → apart 2 vx vy = true →
      VisitBefore L2 roundsBar barX x vx i y vy j ∨
        VisitBefore L2 roundsBar barX y vy j x vx i := by
    intro x y vx vy i j u w hx hy hu hw hp hdis hap
    rcases apart_spec hap hu hw hp hdis with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨0, 2, by omega, h2, bar_dep hx hy⟩
    · exact .inr ⟨0, 2, by omega, h2, bar_dep hy hx⟩
  have hd' : vj.Disagree vi := by
    rcases hd with ⟨b, b', h1, h2, h3⟩ | ⟨a, c, h1, h2, h3⟩
    · exact .inl ⟨b', b, h2, h1, Ne.symm h3⟩
    · exact .inr ⟨c, a, h2, h1, Ne.symm h3⟩
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl <;>
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · exact hgh rfl
  · obtain ⟨hvi', hti⟩ := get_prefix (Walk.prefix_of_exit hwg bar_walk0 hpg ⟨14, rfl⟩) hvi
    obtain ⟨hvj', htj⟩ := get_prefix (Walk.prefix_of_exit hwh bar_walk1 hph ⟨14, rfl⟩) hvj
    rcases cmp 0 1 _ _ i j vi vj (by omega) (by omega) hvi' hvj' (hpi.trans hpj.symm) hd
      bar_apart with ⟨a, c, h1, h2, h3⟩ | ⟨a, c, h1, h2, h3⟩
    · exact hng ⟨a, c, by omega, by omega, h3⟩
    · exact hnh ⟨a, c, by omega, by omega, h3⟩
  · obtain ⟨hvi', hti⟩ := get_prefix (Walk.prefix_of_exit hwg bar_walk1 hpg ⟨14, rfl⟩) hvi
    obtain ⟨hvj', htj⟩ := get_prefix (Walk.prefix_of_exit hwh bar_walk0 hph ⟨14, rfl⟩) hvj
    rcases cmp 0 1 _ _ j i vj vi (by omega) (by omega) hvj' hvi' (hpj.trans hpi.symm) hd'
      bar_apart with ⟨a, c, h1, h2, h3⟩ | ⟨a, c, h1, h2, h3⟩
    · exact hnh ⟨a, c, by omega, by omega, h3⟩
    · exact hng ⟨a, c, by omega, by omega, h3⟩
  · exact hgh rfl

/-! ## `ownPoll`: polls of different objects are not exempted -/

def ownPoll : Kernel where
  name := "ownPoll"
  params := []
  sharedBytes := 16
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .int ⟨.shl, .int .b 32, false, [some 2], [.reg 1, .imm 3]⟩ },
    { op := .int ⟨.add, .int .u 32, false, [some 3], [.reg 2, .sharedSym 0]⟩ },
    { op := .mbarInit 3 0 (.imm 1) },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 5], [.reg 1, .imm 0]⟩ },
    { guard := some (5, false), op := .mbarArrive 3 0 (.imm 0) (.imm 1) false false .cta },
    { op := .mbarWait 6 3 0 (.imm 0) false .cta },
    { guard := some (6, false), op := .bra 9 true },
    { op := .bra 6 true },
    { op := .ret }]

def mA : Loc := ⟨.shared, 0, 0⟩
def mB : Loc := ⟨.shared, 0, 8⟩

/-- Lane 0 initializes its barrier, arrives and polls successfully; lane 1 initializes its
barrier and polls without success. -/
def ownX : Execution where
  tr
    | 0 => [⟨3, .mbInit mA 1⟩, ⟨5, .arrive mA 0 1 false .cta⟩, ⟨6, .wait mA 0 true false .cta⟩]
    | 1 => [⟨3, .mbInit mB 1⟩, ⟨6, .wait mB 0 false false .cta⟩]
    | _ => []
  rf _ _ := none
  objects _ := []

/-- The static check passes: the only guarded uniform instruction is the poll's branch. -/
theorem ownPoll_static : ownPoll.pollGuardsOk = true := by decide

def own0 : List Visit :=
  [lv 0, lv 1, lv 2, fv 3 (.mbInit mA 1),
    lv 4, fv 5 (.arrive mA 0 1 false .cta),
    fv 6 (.wait mA 0 true false .cta), gv 7 true]

def own1 : List Visit :=
  [lv 0, lv 1, lv 2, fv 3 (.mbInit mB 1),
    lv 4, lv 5, fv 6 (.wait mB 0 false false .cta),
    gv 7 false]

theorem own_walk0 : Walk ownPoll [] L2 0 {} (ownX.tr 0) own0 :=
  .tau rfl (.tau rfl (.tau rfl (.ev ⟨_, rfl, rfl, rfl⟩ (.tau rfl (.ev ⟨_, rfl, rfl, rfl⟩
    (.ev ⟨_, rfl, true, rfl, rfl⟩ (.tau rfl (.stop _))))))))

theorem own_walk1 : Walk ownPoll [] L2 1 {} (ownX.tr 1) own1 :=
  .tau rfl (.tau rfl (.tau rfl (.ev ⟨_, rfl, rfl, rfl⟩ (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, false, rfl, rfl⟩ (.tau rfl (.stop _))))))))

/-- **The lanes' polls of their own objects disagree, and the branch is flagged.** -/
theorem ownPoll_flagged : WarpDivergent L2 ownPoll [] ownX := by
  refine ⟨0, 1, by simp [threads_eq], by simp [threads_eq], by decide, _, _, own0, own1,
    List.prefix_refl _, List.prefix_refl _, own_walk0, own_walk1, 7, 7, 7, _, _, rfl, rfl, rfl, rfl,
    sameWarp01, .inl ⟨true, false, rfl, rfl, by decide⟩, not_before_of_end (by decide),
    not_before_of_end (by decide), not_pollAgreeExempt (by simp)⟩

/-! ## `sharedPoll`: polls of one object with one parity are exempt -/

/-- `ownPoll` with one mbarrier for both lanes: lane 0 initializes it, lane 1 arrives. -/
def sharedPoll : Kernel where
  name := "sharedPoll"
  params := []
  sharedBytes := 8
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 2], [.reg 1, .imm 0]⟩ },
    { op := .move ⟨.scalar, .int .b 32, [some 3], [.sharedSym 0]⟩ },
    { guard := some (2, false), op := .mbarInit 3 0 (.imm 1) },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 5], [.reg 1, .imm 1]⟩ },
    { guard := some (5, false), op := .mbarArrive 3 0 (.imm 0) (.imm 1) false false .cta },
    { op := .mbarWait 6 3 0 (.imm 0) false .cta },
    { guard := some (6, false), op := .bra 9 true },
    { op := .bra 6 true },
    { op := .ret }]

def sh0 : List Visit :=
  [lv 0, lv 1, lv 2, fv 3 (.mbInit mA 1), lv 4, lv 5,
    fv 6 (.wait mA 0 false false .cta), gv 7 false]

def sh1 : List Visit :=
  [lv 0, lv 1, lv 2, lv 3, lv 4, fv 5 (.arrive mA 0 1 false .cta),
    fv 6 (.wait mA 0 true false .cta), gv 7 true]

/-- Lane 0 initializes the barrier and polls without success; lane 1 arrives and polls
successfully. -/
def sharedX : Execution where
  tr
    | 0 => [⟨3, .mbInit mA 1⟩, ⟨6, .wait mA 0 false false .cta⟩]
    | 1 => [⟨5, .arrive mA 0 1 false .cta⟩, ⟨6, .wait mA 0 true false .cta⟩]
    | _ => []
  rf _ _ := none
  objects _ := []

/-- An assumption selecting the poll's branch at position 7. -/
def sharedHook : Assumption :=
  Assumption.pollAgreeAt "litmus-poll-agree-shared" [7] "The lanes spin on one mbarrier."

theorem sh_walk0 (A : List Assumption) (hA : A = [] ∨ A = [sharedHook]) :
    Walk sharedPoll A L2 0 {} (sharedX.tr 0) sh0 := by
  rcases hA with rfl | rfl <;>
  exact .tau rfl (.tau rfl (.tau rfl (.ev ⟨_, rfl, rfl, rfl⟩ (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, false, rfl, rfl⟩ (.tau rfl (.stop _))))))))

theorem sh_walk1 (A : List Assumption) (hA : A = [] ∨ A = [sharedHook]) :
    Walk sharedPoll A L2 1 {} (sharedX.tr 1) sh1 := by
  rcases hA with rfl | rfl <;>
  exact .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.ev ⟨_, rfl, rfl, rfl⟩
    (.ev ⟨_, rfl, true, rfl, rfl⟩ (.tau rfl (.stop _))))))))

/-- **Without an assumption, lane 0's failed and lane 1's successful poll of one mbarrier with one
parity give disagreeing branch executions that nothing orders: flagged.** -/
theorem sharedPoll_flagged : WarpDivergent L2 sharedPoll [] sharedX := by
  refine ⟨0, 1, by simp [threads_eq], by simp [threads_eq], by decide, _, _, sh0, sh1,
    List.prefix_refl _, List.prefix_refl _, sh_walk0 [] (.inl rfl), sh_walk1 [] (.inl rfl), 7, 7, 7,
    _, _, rfl, rfl, rfl, rfl, sameWarp01, .inl ⟨false, true, rfl, rfl, by decide⟩,
    not_before_of_end (by decide), not_before_of_end (by decide), not_pollAgreeExempt (by simp)⟩

/-- **With `pollAgreeAt` selecting the branch, the pair is exempt (ASM-POLL-AGREE).** Lane 0 may
poll before lane 1's arrival completes the phase: the exemption rests on the assumption alone. -/
theorem sharedPoll_exempt : PollAgreeExempt sharedPoll [sharedHook] 7 sh0 sh1 7 7 :=
  ⟨rfl, ⟨6, false, 9, _, 3, 0, .imm 0, false, .cta, rfl, rfl, rfl⟩, _, _, mA, 0, 0, false, true,
    false, false, .cta, .cta, rfl, rfl, by decide, by decide, rfl, rfl⟩

/-! ## `arriveAfter`: a pair ordered on hardware but not in the model -/

def arriveAfter : Kernel where
  name := "arriveAfter"
  params := []
  sharedBytes := 8
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 2], [.reg 1, .imm 0]⟩ },
    { op := .move ⟨.scalar, .int .b 32, [some 3], [.sharedSym 0]⟩ },
    { op := .mbarWait 6 3 0 (.imm 0) false .cta },
    { op := .move ⟨.scalar, .int .b 32, [some 4], [.imm 0]⟩ },
    { guard := some (6, false), op := .bra 7 true },
    { guard := some (2, false), op := .mbarArrive 3 0 (.imm 0) (.imm 1) false false .cta },
    { op := .ret }]

/-- Lane 0 polls without success, passes its branch and arrives; lane 1 then polls
successfully and is at its branch. -/
def afterX : Execution where
  tr
    | 0 => [⟨3, .wait mA 0 false false .cta⟩, ⟨6, .arrive mA 0 1 false .cta⟩, ⟨7, .exit⟩]
    | 1 => [⟨3, .wait mA 0 true false .cta⟩]
    | _ => []
  rf _ _ := none
  objects _ := []

def after0 : List Visit :=
  [lv 0, lv 1, lv 2, fv 3 (.wait mA 0 false false .cta), lv 4,
    gv 5 false, fv 6 (.arrive mA 0 1 false .cta),
    fv 7 .exit]

def after1 : List Visit :=
  [lv 0, lv 1, lv 2, fv 3 (.wait mA 0 true false .cta), lv 4,
    gv 5 true]

theorem after_walk0 : Walk arriveAfter [] L2 0 {} (afterX.tr 0) after0 :=
  .tau rfl (.tau rfl (.tau rfl (.ev ⟨_, rfl, false, rfl, rfl⟩ (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, rfl, rfl⟩ (.last ⟨_, rfl, rfl, rfl⟩)))))))

theorem after_walk1 : Walk arriveAfter [] L2 1 {} (afterX.tr 1) after1 :=
  .tau rfl (.tau rfl (.tau rfl (.ev ⟨_, rfl, true, rfl, rfl⟩ (.tau rfl (.tau rfl (.stop _))))))

/-- **Flagged, although lane 1's branch follows lane 0's on hardware**: the model orders lane
0's arrival only before lane 1's events after its poll, and lane 1 performs none before its
branch. -/
theorem arriveAfter_flagged : WarpDivergent L2 arriveAfter [] afterX := by
  refine ⟨0, 1, by simp [threads_eq], by simp [threads_eq], by decide, _, _, _, _,
    List.prefix_refl _, List.prefix_refl _, after_walk0, after_walk1, 5, 5, 5, _, _, rfl, rfl, rfl,
    rfl, sameWarp01, .inl ⟨false, true, rfl, rfl, by decide⟩, ?_, not_before_of_end (by decide),
    not_pollAgreeExempt (by simp)⟩
  rintro ⟨a, b, -, hb, hab⟩
  have h1 : Visit.events after1 5 = 1 := by decide
  have := dep_tgt_pos hab
  simp only at this
  omega

/-! ## `warpgroupMaxReg`: `setmaxnreg` guards are compared across the warps of a warpgroup -/

/-- One CTA of 64 threads: two warps of one warpgroup. -/
def L64 : Launch := { grid := 1, block := 64, params := fun _ => none }

/-- `mov r1, %tid.x; setp.ge.u32 p2, r1, 32; @p2 setmaxnreg.dec.sync.aligned.u32 32; ret`. -/
def warpgroupMaxReg : Kernel where
  name := "warpgroupMaxReg"
  params := []
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .int ⟨.setp .ge none, .int .u 32, false, [some 2], [.reg 1, .imm 32]⟩ },
    { guard := some (2, false), op := .setMaxReg false 32 },
    { op := .ret }]

def maxRegX : Execution where
  tr
    | 0 => [⟨3, .exit⟩]
    | 32 => [⟨2, .setMaxReg false 32 0⟩, ⟨3, .exit⟩]
    | _ => []
  rf _ _ := none
  objects _ := []

def maxReg0 : List Visit := [lv 0, lv 1, gv 2 false, fv 3 .exit]

def maxReg32 : List Visit :=
  [lv 0, lv 1, ⟨2, some true, some ⟨2, .setMaxReg false 32 0⟩, none⟩, fv 3 .exit]

theorem maxReg_walk0 : Walk warpgroupMaxReg [] L64 0 {} (maxRegX.tr 0) maxReg0 :=
  .tau rfl (.tau rfl (.tau rfl (.last ⟨_, rfl, rfl, rfl⟩)))

theorem maxReg_walk32 : Walk warpgroupMaxReg [] L64 32 {} (maxRegX.tr 32) maxReg32 :=
  .tau rfl (.tau rfl (.ev ⟨_, rfl, 0, rfl, rfl⟩ (.last ⟨_, rfl, rfl, rfl⟩)))

theorem sameWarpgroup : SameWarpgroup L64 0 32 :=
  ⟨⟨by simp [L64, Launch.threads], by simp [L64, Launch.threads], by simp [L64]⟩, by simp [L64]⟩

/-- **Two warps of one warpgroup disagree on a `setmaxnreg` guard: flagged**, although each warp
is uniform (§9.7.21.5: "all threads in warpgroup evaluate the condition identically"). -/
theorem warpgroupMaxReg_flagged : WarpDivergent L64 warpgroupMaxReg [] maxRegX := by
  refine ⟨0, 32, by simp [L64, Launch.threads], by simp [L64, Launch.threads], by decide, _, _, _,
    _, List.prefix_refl _, List.prefix_refl _, maxReg_walk0, maxReg_walk32, 2, 2, 2, gv 2 false, ⟨2,
    some true, some ⟨2, .setMaxReg false 32 0⟩, none⟩, rfl, rfl, rfl, rfl, sameWarpgroup,
    .inl ⟨false, true, rfl, rfl, by decide⟩, not_before_of_zero rfl, not_before_of_zero rfl,
    not_pollAgreeExempt (by simp)⟩

/-- An assumption selecting the `setmaxnreg` at position 2 with `uniPoll`. -/
def maxRegHook : Assumption :=
  Assumption.pollAgreeAt "litmus-poll-agree-maxreg" [2] "Selects a non-branch position."

/-- **A selected position that is not a `bra.uni` after a poll is not exempt**: the hook selects
the `setmaxnreg` at position 2, and the pair is still compared. -/
theorem maxReg_not_pollAgreeExempt {i j : Nat} {vg vh : List Visit} :
    ¬ PollAgreeExempt warpgroupMaxReg [maxRegHook] 2 vg vh i j := by
  rintro ⟨-, ⟨dst, neg, tgt, prev, base, off, par, acq, sc, hc, -⟩, -⟩
  simp [warpgroupMaxReg] at hc

/-- **With the hook selecting the `setmaxnreg`, the warpgroup divergence is still flagged.** -/
theorem warpgroupMaxReg_hook_flagged : WarpDivergent L64 warpgroupMaxReg [maxRegHook] maxRegX := by
  refine ⟨0, 32, by simp [L64, Launch.threads], by simp [L64, Launch.threads], by decide, _, _, _,
    _, List.prefix_refl _, List.prefix_refl _, .tau rfl (.tau rfl (.tau rfl (.last ⟨_, rfl, rfl,
    rfl⟩))), .tau rfl (.tau rfl (.ev ⟨_, rfl, 0, rfl, rfl⟩ (.last ⟨_, rfl, rfl, rfl⟩))), 2, 2, 2,
    gv 2 false, ⟨2, some true, some ⟨2, .setMaxReg false 32 0⟩, none⟩, rfl, rfl, rfl, rfl,
    sameWarpgroup, .inl ⟨false, true, rfl, rfl, by decide⟩, not_before_of_zero rfl,
    not_before_of_zero rfl, maxReg_not_pollAgreeExempt⟩

/-- The two threads are in different warps: a warp-scoped rule does not compare them. -/
theorem maxReg_not_sameWarp : ¬ SameWarp L64 0 32 := by
  simp [SameWarp, SameCta, L64, Launch.threads]

/-! ## `roundsElect`: a full-mask election between the rounds (EXT-DEPENDENCY-ORDER) -/

def roundsElect : Kernel where
  name := "roundsElect"
  params := []
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .move ⟨.scalar, .int .b 32, [some 2], [.imm 0]⟩ },
    { op := .int ⟨.setp .ne none, .int .u 32, false, [some 3], [.reg 1, .imm 0]⟩ },
    { op := .int ⟨.setp .ne none, .int .u 32, false, [some 4], [.reg 2, .imm 0]⟩ },
    { guard := some (4, false), op := .bra 6 false },
    { guard := some (3, false), op := .bra 8 false },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 5], [.reg 2, .imm 0]⟩ },
    { guard := some (5, false), op := .bra 8 true },
    { op := .warp { kind := .elect, dsts := [none, some 7], mask := some (.imm (-1)) } },
    { op := fpaOp },
    { op := .int ⟨.add, .int .u 32, false, [some 2], [.reg 2, .imm 1]⟩ },
    { op := .int ⟨.setp .lt none, .int .u 32, false, [some 6], [.reg 2, .imm 2]⟩ },
    { guard := some (6, false), op := .bra 2 false },
    { op := .ret }]

/-- Both lanes elect lane 0 in instance 0 (round 1) and instance 1 (round 2), each election
followed by the fence. -/
def electX : Execution where
  tr
    | 0 => [⟨8, .elect 4294967295 0 0⟩, ⟨9, fpa⟩, ⟨8, .elect 4294967295 1 0⟩, ⟨9, fpa⟩,
        ⟨13, .exit⟩]
    | 1 => [⟨8, .elect 4294967295 0 0⟩, ⟨9, fpa⟩, ⟨8, .elect 4294967295 1 0⟩, ⟨9, fpa⟩,
        ⟨13, .exit⟩]
    | _ => []
  rf _ _ := none
  objects _ := []

/-- The records of one round's tail: the election, the fence and the loop. -/
def tailE (inst : Nat) : List Visit :=
  [fv 8 (.elect 4294967295 inst 0), fv 9 fpa, lv 10, lv 11, lv 12]

/-- Lane 0: both rounds reach the `bra.uni` (guard true, then false). -/
def el0 : List Visit :=
  [lv 0, lv 1, lv 2, lv 3, lv 4, lv 5, lv 6, gv 7 true] ++ tailE 0 ++
    [lv 2, lv 3, lv 4, lv 6, gv 7 false] ++ tailE 1 ++ [fv 13 .exit]

/-- Lane 1: round 1 skips the `bra.uni`, round 2 reaches it (guard false). -/
def el1 : List Visit :=
  [lv 0, lv 1, lv 2, lv 3, lv 4, lv 5] ++ tailE 0 ++
    [lv 2, lv 3, lv 4, lv 6, gv 7 false] ++ tailE 1 ++ [fv 13 .exit]

theorem el_walk0 : Walk roundsElect [] L2 0 {} (electX.tr 0) el0 :=
  .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, 0, 0, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩ (.tau rfl (.tau rfl (.tau rfl
    (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, 1, 0, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩ (.tau rfl (.tau rfl (.tau rfl
    (.last ⟨_, rfl, rfl, rfl⟩)))))))))))))))))))))))

theorem el_walk1 : Walk roundsElect [] L2 1 {} (electX.tr 1) el1 :=
  .tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, 0, 0, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩ (.tau rfl (.tau rfl (.tau rfl
    (.tau rfl (.tau rfl (.tau rfl (.tau rfl (.tau rfl
    (.ev ⟨_, rfl, 1, 0, rfl, rfl⟩ (.ev ⟨_, rfl, rfl, rfl⟩ (.tau rfl (.tau rfl (.tau rfl
    (.last ⟨_, rfl, rfl, rfl⟩)))))))))))))))))))))

/-- The finite check behind `roundsElect_not_flagged`. -/
theorem el_apart : apart 1 el0 el1 = true := by decide

/-- Each lane's first election fills a need of each lane's first election: its event of the
same instance. -/
theorem el_witness {x y : Nat} (hx : x < 2) (hy : y < 2) :
    Witness L2 electX (.thread (x, 0)) (y, 0) := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
  · exact Witness.of_need L2 (List.mem_map.mpr ⟨0, by decide, rfl⟩) ⟨_, rfl⟩
      ⟨0, 8, 0, rfl, rfl⟩
  · exact Witness.of_need L2 (List.mem_map.mpr ⟨0, by decide, rfl⟩) ⟨_, rfl⟩
      ⟨0, 8, 0, rfl, rfl⟩
  · exact Witness.of_need L2 (List.mem_map.mpr ⟨1, by decide, rfl⟩) ⟨_, rfl⟩
      ⟨0, 8, 0, rfl, rfl⟩
  · exact Witness.of_need L2 (List.mem_map.mpr ⟨1, by decide, rfl⟩) ⟨_, rfl⟩
      ⟨0, 8, 0, rfl, rfl⟩

/-- The first election orders a lane's first election before the other lane's first fence: the
election of the first lane fills a need of the other lane's election, whose return precedes its
fence. -/
theorem el_dep {x y : Nat} (hx : x < 2) (hy : y < 2) :
    DepBefore L2 roundsElect electX (x, 0) (y, 1) := by
  have hg : electX.get (y, 0) = some ⟨8, .elect 4294967295 0 0⟩ := by
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> rfl
  have h01 : TraceBefore electX (y, 0) (y, 1) := by
    refine ⟨rfl, Nat.zero_lt_one, ?_⟩
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> decide
  exact .tail (.single (.inl (DepStep.of_witness L2 (el_witness hx hy))))
    (.inl (DepStep.of_resumes L2 (Resumes.of_blocking (b := true) hg rfl h01)))

/-- **The election orders the rounds in the execution-dependency order: not flagged, without
any assumption.** -/
theorem roundsElect_not_flagged : ¬ WarpDivergent L2 roundsElect [] electX := by
  rintro ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hvi, hvj, hpi,
    hpj, -, hd, hng, hnh, -⟩
  rw [threads_eq] at hg hh
  have cmp : ∀ (x y : Nat) (vx vy : List Visit) (i j : Nat) (u w : Visit), x < 2 → y < 2 →
      vx[i]? = some u → vy[j]? = some w → u.pc = w.pc → u.Disagree w → apart 1 vx vy = true →
      VisitBefore L2 roundsElect electX x vx i y vy j ∨
        VisitBefore L2 roundsElect electX y vy j x vx i := by
    intro x y vx vy i j u w hx hy hu hw hp hdis hap
    rcases apart_spec hap hu hw hp hdis with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨0, 1, by omega, h2, el_dep hx hy⟩
    · exact .inr ⟨0, 1, by omega, h2, el_dep hy hx⟩
  have hd' : vj.Disagree vi := by
    rcases hd with ⟨b, b', h1, h2, h3⟩ | ⟨a, c, h1, h2, h3⟩
    · exact .inl ⟨b', b, h2, h1, Ne.symm h3⟩
    · exact .inr ⟨c, a, h2, h1, Ne.symm h3⟩
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl <;>
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · exact hgh rfl
  · obtain ⟨hvi', hti⟩ := get_prefix (Walk.prefix_of_exit hwg el_walk0 hpg ⟨13, rfl⟩) hvi
    obtain ⟨hvj', htj⟩ := get_prefix (Walk.prefix_of_exit hwh el_walk1 hph ⟨13, rfl⟩) hvj
    rcases cmp 0 1 _ _ i j vi vj (by omega) (by omega) hvi' hvj' (hpi.trans hpj.symm) hd
      el_apart with ⟨a, c, h1, h2, h3⟩ | ⟨a, c, h1, h2, h3⟩
    · exact hng ⟨a, c, by omega, by omega, h3⟩
    · exact hnh ⟨a, c, by omega, by omega, h3⟩
  · obtain ⟨hvi', hti⟩ := get_prefix (Walk.prefix_of_exit hwg el_walk1 hpg ⟨13, rfl⟩) hvi
    obtain ⟨hvj', htj⟩ := get_prefix (Walk.prefix_of_exit hwh el_walk0 hph ⟨13, rfl⟩) hvj
    rcases cmp 0 1 _ _ j i vj vi (by omega) (by omega) hvj' hvi' (hpj.trans hpi.symm) hd'
      el_apart with ⟨a, c, h1, h2, h3⟩ | ⟨a, c, h1, h2, h3⟩
    · exact hnh ⟨a, c, by omega, by omega, h3⟩
    · exact hng ⟨a, c, by omega, by omega, h3⟩
  · exact hgh rfl

/-! ## `phasePoll`: polls of one object with different parities (ASM-POLL-AGREE) -/

/-- Both lanes poll one mbarrier with the parity of their lane index. -/
def phasePoll : Kernel where
  name := "phasePoll"
  params := []
  sharedBytes := 8
  code := [
    { op := .move ⟨.scalar, .int .u 32, [some 1], [.sreg ⟨.tid, some .x⟩]⟩ },
    { op := .move ⟨.scalar, .int .b 32, [some 3], [.sharedSym 0]⟩ },
    { op := .mbarWait 6 3 0 (.reg 1) false .cta },
    { guard := some (6, false), op := .bra 5 true },
    { op := .bra 2 true },
    { op := .ret }]

/-- The assumption selecting the branch at position 3. -/
def phaseHook : Assumption :=
  Assumption.pollAgreeAt "litmus-poll-agree-phase" [3] "The lanes poll one mbarrier in different \
    rounds."

/-- Lane 0 polls parity 0 without success; lane 1 polls parity 1 successfully. -/
def phaseX : Execution where
  tr
    | 0 => [⟨2, .wait mA 0 false false .cta⟩]
    | 1 => [⟨2, .wait mA 1 true false .cta⟩]
    | _ => []
  rf _ _ := none
  objects _ := []

/-- The static check passes: the only guarded uniform instruction is the poll's branch. -/
theorem phasePoll_static : phasePoll.pollGuardsOk = true := by decide

def ph0 : List Visit :=
  [lv 0, lv 1, fv 2 (.wait mA 0 false false .cta), gv 3 false]

def ph1 : List Visit :=
  [lv 0, lv 1, fv 2 (.wait mA 1 true false .cta), gv 3 true]

theorem ph_walk0 (A : List Assumption) (hA : A = [] ∨ A = [phaseHook]) :
    Walk phasePoll A L2 0 {} (phaseX.tr 0) ph0 := by
  rcases hA with rfl | rfl <;>
  exact .tau rfl (.tau rfl (.ev ⟨_, rfl, false, rfl, rfl⟩ (.tau rfl (.stop _))))

theorem ph_walk1 (A : List Assumption) (hA : A = [] ∨ A = [phaseHook]) :
    Walk phasePoll A L2 1 {} (phaseX.tr 1) ph1 := by
  rcases hA with rfl | rfl <;>
  exact .tau rfl (.tau rfl (.ev ⟨_, rfl, true, rfl, rfl⟩ (.tau rfl (.stop _))))

/-- **Without the assumption, the polls of one object with different parities disagree, and the
branch is flagged.** -/
theorem phasePoll_flagged : WarpDivergent L2 phasePoll [] phaseX := by
  refine ⟨0, 1, by simp [threads_eq], by simp [threads_eq], by decide, _, _, ph0, ph1,
    List.prefix_refl _, List.prefix_refl _, ph_walk0 [] (.inl rfl), ph_walk1 [] (.inl rfl), 3, 3, 3,
    _, _, rfl, rfl, rfl, rfl, sameWarp01, .inl ⟨false, true, rfl, rfl, by decide⟩,
    not_before_of_end (by decide), not_before_of_end (by decide), not_pollAgreeExempt (by simp)⟩

/-- **With the assumption selecting the branch, the polls of one object are exempt whatever their
parities: not flagged.** -/
theorem phasePoll_not_flagged : ¬ WarpDivergent L2 phasePoll [phaseHook] phaseX := by
  refine not_warpDivergent_synced phasePoll_static
    (LocalLands.of_rules (RulesFrame.cons_none (fun _ _ _ _ => rfl) Proof.RulesFrame.nil)
      (.cons (.of_none fun _ _ _ => rfl) .nil)) ?_
  intro g h k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh _ _ he he' _ hd
  have obj : ∀ {x j pcx mx px okx acqx scx}, x < L2.threads →
      phaseX.get (x, j) = some ⟨pcx, .wait mx px okx acqx scx⟩ → pcx = 2 ∧ mx = mA := by
    intro x j pcx mx px okx acqx scx hx hj
    rw [threads_eq] at hx
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
      rcases j with _ | j <;> simp [Execution.get, phaseX] at hj <;>
      obtain ⟨rfl, rfl, -⟩ := hj <;> exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := obj hg he
  obtain ⟨-, rfl⟩ := obj hh he'
  rcases hd with hd | hd
  · exact absurd rfl hd
  · exact absurd hd (by decide)

/-- **No change when off**: with no site selected, the rule is the one without the
exemption. -/
example (L : Launch) (K : Kernel) (X : Execution) :
    WarpDivergent L K [] X ↔ ∃ g h, g < L.threads ∧ h < L.threads ∧ g ≠ h ∧
      ∃ eg eh vg vh, eg <+: X.tr g ∧ eh <+: X.tr h ∧ Walk K [] L g {} eg vg ∧
        Walk K [] L h {} eh vh ∧
        ∃ i j pc vi vj, vg[i]? = some vi ∧ vh[j]? = some vj ∧ vi.pc = pc ∧ vj.pc = pc ∧
          SameUniformGroup L (K.uniformScopeAt pc) g h ∧ vi.Disagree vj ∧
          ¬ VisitBefore L K X g vg i h vh j ∧ ¬ VisitBefore L K X h vh j g vg i :=
  warpDivergent_noPoll (by simp)

end PTX.Tests.WarpUniformLitmus
