-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Counts

@[expose] public section

/-! # The startup share of the progress contract

`Proof/Schedule/Contract.lean: RefProgress` is what the progress instance needs from the
reference layer about a followed state `d` of a thread and the counts over its earlier events.
This file proves the part of the startup phase's share that follows from the ledger and the
closed-form events. The statements do not import the progress files: each is in the terms the
field unfolds to (the field and the unfolding are named in the docstring), for a state that
satisfies the phase invariant `Inv` or, where it matters, the exit condition `Out`.

* `bar0_startup`, `bar0_out`: field `bar0`. The thread's `bar.sync 0` count is the number of
  the nine `bar.sync 0` instructions below the state's instruction (`bar0Of d.site.pc`
  unfolded: `(bar0Pcs.filter (· < pc)).length`); `led_bar0` is that fact about positions.
* `collAt_startup`: field `collAt`. A state at an election or a shuffle is at a collective
  position of the thread's own warp (`collPcs (g % L.block / 32)` unfolded, with `warp g`).
* `poll_startup`: field `poll` at the poll of instruction 384: the thread has no successful
  poll of the state barrier of its block behind it (`roundOf .state _ = 0`), and every wait
  event the state fires is on that barrier with parity 0 (`Bar.state.delta = 0`).
* `barStep_startup`: field `barStep` for the three barriers of the phase: the state is at
  sub-step 0 and the next state is at a later instruction. (The tile index is 0 on both
  sides: both instructions are at most 387.)
* `arrState_startup`: field `arrState` for the states of the phase past instruction 379 and at
  the exit: the load leader has one arrival on, and 16 loads completing on, the state barrier.
* `inv_next`: one step from a state of the phase (with the extended invariant `InvE`): the
  successor along the thread's event is a state that is in the phase or is its exit (no
  hypothesis on the trace length).

* `coll_startup`: field `coll`, for a state with the extended invariant `InvE` or the extended
  exit condition `OutE` (`Shfl.lean: startup_invE` gives one of them at every followed state):
  the thread's shuffles and elections are the collective positions of its warp (`collList`,
  the body of `collPcs`) below the state's instruction. The step lemmas prove the election
  count next to the ledger (`Steps.lean: elects`, third conjunct of `Succ`).

* `left_dec_startup`: field `left_dec` for a step from a state of the phase, with the measure
  `leftOf P g : D → Nat` (`Trace.lean`; `400 - pc` plus 100 per sequence the scan's loop of
  eight still has to scan); `leftOf_exit` (13 at the exit state) and `leftOf_le` (at most
  `400 + 100 N` at every state, for the premise `init`). The global measure is
  `E + leftOf P g d` on the states of this phase, with `E + 13` at least the measure the next
  phase gives the exit state.

* `collShape_startup`, `collTmpl_startup`, `collKind_startup`: fields `collShape` and
  `collKind`, with `F (c, w) n := collShapeAt w n` (the instruction and the static part of the
  `n`-th collective of a warp: a full-mask election, or `shfl.sync.idx` with lane operand 0
  and clamp 31) and `collShapeAt_full`. All collective sites of the kernel are in this phase.
  `startup_invE_le` gives the extended invariant at a thread's last state too. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The `bar.sync 0` count of a position** is the number of `bar.sync 0` instructions below
the position's instruction. -/
theorem led_bar0 (g : Nat) (pos : Pos) :
    (led g pos).bars = (bar0Pcs.filter (· < pos.site.pc)).length := by
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> (try fin_cases j) <;> rfl

theorem ledExit_bar0 (g : Nat) :
    (ledExit g).bars = (bar0Pcs.filter (· < (Site.fenceProxy 0).pc)).length := rfl

/-- More `bar.sync 0` instructions below an instruction: a later instruction. -/
theorem bar0_lt {p p' : Nat}
    (h : (bar0Pcs.filter (· < p)).length < (bar0Pcs.filter (· < p')).length) : p < p' := by
  by_contra hle
  have hsub : List.Sublist (bar0Pcs.filter (· < p')) (bar0Pcs.filter (· < p)) :=
    List.monotone_filter_right _ fun a ha => by
      simp only [decide_eq_true_eq] at ha ⊢
      omega
  have := hsub.length_le
  omega

/-- The position of a state with three `bar.sync 0` behind it is the poll. -/
theorem led_bars3 {pos : Pos} (h : 3 ≤ (led g pos).bars) : pos = .wait := by
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> (try fin_cases j) <;>
    first | rfl | (exfalso; rw [led_bar0] at h; revert h; decide)

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

omit hpre hX hg in
/-- **`RefProgress.bar0` for a state of the phase.** -/
theorem bar0_startup {k : Nat} {s : D} (hI : Inv P X g k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨pos, hr, hl⟩ := hI
  have h1 : ((X.tr g).take k).countP (Execution.isBarId 0) = (led g pos).bars :=
    congrArg Led.bars hl
  rw [h1, led_bar0, hr.site]

omit hpre hX hg in
/-- **`RefProgress.bar0` at the exit of the phase.** -/
theorem bar0_out {k : Nat} {s : D} (ho : Out P X g k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  have h1 : ((X.tr g).take k).countP (Execution.isBarId 0) = (ledExit g).bars :=
    congrArg Led.bars ho.2
  rw [h1, ledExit_bar0, ho.1.site]

omit hpre hX hg in
/-- **`RefProgress.collAt` for a state of the phase**: a state at an election or a shuffle is
at a collective position of its thread's warp: warp 0 alone is at the elections 61 and 93, the
load warp alone at the election 32. -/
theorem collAt_startup {k : Nat} {s : D} (hI : Inv P X g k s)
    (hc : (∃ j, s.site = .elect j) ∨ ∃ j, s.site = .shfl j) :
    s.site.pc ∈ (if warp g = 0 then [48, 52, 55, 61, 87, 93, 312]
      else if warp g = 4 then [32, 48, 52, 55, 87, 312] else [48, 52, 55, 87, 312]) := by
  obtain ⟨pos, hr, -⟩ := hI
  have hsite := hr.site
  have hpos := hr.pos
  rw [hsite]
  rcases pos with j | j | j | j | j | j | _ | j | _
  · fin_cases j <;> simp only [AtPos, finVal] at hpos
    · rw [ite_eq_right (by omega), ite_eq_left hpos.1]
      decide
    · split_ifs <;> decide
    · rw [ite_eq_left hpos.2.1]
      decide
    · rw [ite_eq_left hpos.2.2.1]
      decide
    · split_ifs <;> decide
  · fin_cases j <;> split_ifs <;> decide
  all_goals
    exfalso
    rw [hsite] at hc
    rcases hc with ⟨j', h⟩ | ⟨j', h⟩ <;> cases h

/-- The shuffles before the next position of a state of the phase are at most three. -/
theorem shfls_succ {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    ((X.tr g).take (k + 1)).countP Execution.isShfl ≤ 3 := by
  obtain ⟨pos, hr, hl⟩ := hI
  have h1 : ((X.tr g).take k).countP Execution.isShfl = (led g pos).shfls :=
    congrArg Led.shfls hl
  have h2 := count_snoc Execution.isShfl he
  have h4 := led_shfls_le g pos
  cases hsh : Execution.isShfl e with
  | false =>
    rw [hsh] at h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    omega
  | true =>
    obtain ⟨pc, md, a, b, c, v, ok, rfl⟩ :
        ∃ pc md a b c v ok, e = ⟨pc, .shfl md a b c v ok⟩ := by
      obtain ⟨pc, kd⟩ := e
      cases kd <;> first | exact ⟨_, _, _, _, _, _, _, rfl⟩ | cases hsh
    obtain ⟨site, w, p, x⟩ := s
    obtain rfl : site = pos.site := hr.site
    obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
    have hev := ev_full hpre hg pos hr hat hc hf
    rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
    rw [led_shfl] at h1
    simp only [Execution.isShfl, ↓reduceIte] at h2
    have := j.isLt
    omega

/-- **One step from a state of the phase**: the machine's successor along the thread's event
is the state before the next event, and it is in the phase or is the exit of the phase. -/
theorem inv_next {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : InvE P X g k s) :
    ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s') ∧
      (InvE P X g (k + 1) s' ∨ OutE P X g (k + 1) s') := by
  have hC := sounds hpre
  have hret := retEv_upto hpre hX
    (shfl_first hpre hC hX hg (shfls_succ hpre hX hg he hσ hI.inv)) (Nat.lt_succ_self k) he
  obtain ⟨hub, s', hn⟩ := startup_ok hpre hC hX hg he hσ hI.inv hret
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  refine ⟨s', ?_, inv_step hpre hg k e s s' t ins o he hI hat hc hf hub hret hn⟩
  rw [Frame.stateAt_succ he, hσ]
  exact hn

/-- **`RefProgress.barStep` for the three barriers of the phase**: a barrier event is fired at
sub-step 0 and the next state is at a later instruction. -/
theorem barStep_startup {k pc bid : Nat} {cnt : Option Nat} {m : BarMode} {s s' : D}
    (hE : InvE P X g k s) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (he : X.get (g, k) = some ⟨pc, .bar bid cnt m⟩)
    (hσ' : Frame.stateAt (code L) X g (k + 1) = some (some s')) :
    s.site.sub = 0 ∧ s.site.pc < s'.site.pc := by
  have hI := hE.inv
  obtain ⟨s2, hσ2, hnext⟩ := inv_next hpre hX hg he hσ hE
  have hs2 : s2 = s' := Option.some.inj (Option.some.inj (hσ2.symm.trans hσ'))
  rw [hs2] at hnext
  have hsub : s.site.sub = 0 := by
    rcases bar_startup hpre hX hg he hσ with ⟨-, -, -, j, -, -⟩ | h
    · obtain ⟨pos, hr, hl⟩ := id hI
      obtain ⟨site, w, p, x⟩ := s
      obtain rfl : site = pos.site := hr.site
      obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
      have hev := ev_full hpre hg pos hr hat hc hf
      rcases pos with j | j | j | j | j | j | _ | j | _ <;>
        simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
          false_and] at hev
      rfl
    · exact absurd h hI.not_left
  refine ⟨hsub, bar0_lt ?_⟩
  have h0 := bar0_startup hI
  have hid : bid = 0 := by
    rcases bar_startup hpre hX hg he hσ with ⟨h, -⟩ | h
    · exact h
    · exact absurd h hI.not_left
  subst hid
  have h1 := count_snoc (Execution.isBarId 0) he
  have h2 : ((X.tr g).take (k + 1)).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s'.site.pc)).length := by
    rcases hnext with h | h
    · exact bar0_startup h.inv
    · exact bar0_out h.1
  have h3 : Execution.isBarId 0 (⟨pc, .bar 0 cnt m⟩ : Event) = true := by
    simp [Execution.isBarId]
  rw [h3] at h1
  simp only [↓reduceIte] at h1
  omega

omit hX in
/-- **`RefProgress.poll` at the poll of the phase** (instruction 384): the polled mbarrier is
the state barrier of the thread's block; the thread has no successful poll of it behind it;
every wait event the state fires is on that barrier, with parity 0. -/
theorem poll_startup {k : Nat} {s : D} {j : Fin 10} (hI : Inv P X g k s)
    (hs : s.site = .mbarWait j) :
    okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) = 0 ∧
      ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
        (code L g).AtD s t → kernel.code[s.site.pc]? = some ins →
        Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o →
        ∀ l q ok acq sc, e.kind = .wait l q ok acq sc →
          l = Bar.state.loc L (g / L.block) ∧ q = 0 := by
  have hstate : Bar.state.loc L (g / L.block) = ⟨.shared, g / L.block, P.sharedBase + 98384⟩ := by
    simp only [Bar.loc, Bar.off, hpre.sharedBase]
  obtain ⟨pos, hr, hl⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  have hpos : pos = .wait := by
    rcases pos with j' | j' | j' | j' | j' | j' | _ | j' | _ <;> first | rfl | cases hs
  subst hpos
  refine ⟨okPolls_zero (congrArg Led.polls hl), ?_⟩
  intro t ins e o hat hc hf l q ok acq sc hk
  obtain ⟨ok', rfl⟩ := ev_full hpre hg .wait hr hat hc hf
  cases hk
  exact ⟨hstate.symm, rfl⟩

/-- Inside the phase every arrival made so far is on the state barrier: the count by object
is the ledger's count by kind. -/
theorem arrivals_state {k : Nat} {s : D} (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k s) :
    arrivals ⟨.shared, g / L.block, P.sharedBase + 98384⟩ ((X.tr g).take k) =
      ((X.tr g).take k).countP isArr := by
  refine List.countP_congr fun x hx => ?_
  obtain ⟨i, hi, hxi⟩ := mem_take hx
  obtain ⟨si, hσi⟩ := followed_of_le hσ (show i ≤ k by omega)
  rcases event_at hpre hX hg hxi hσi with ⟨pos, -, -, hev⟩ | hleft
  · rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
    · obtain ⟨inst, ld, rfl⟩ := hev
      simp [arrivesOn, sourceArrive, isArr]
    · obtain ⟨v, ok, rfl⟩ := hev
      simp [arrivesOn, sourceArrive, isArr]
    · subst hev
      simp [arrivesOn, sourceArrive, isArr]
    · subst hev
      simp [arrivesOn, sourceArrive, isArr]
    · subst hev
      simp [arrivesOn, sourceArrive, isArr]
    · obtain ⟨i', hi', bs, hbs, rfl⟩ := hev
      simp [arrivesOn, sourceArrive, isArr]
    · subst hev
      simp [arrivesOn, sourceArrive, isArr]
    · subst hev
      simp [arrivesOn, sourceArrive, isArr]
    · obtain ⟨ok, rfl⟩ := hev
      simp [arrivesOn, sourceArrive, isArr]
  · exact absurd (hleft.mono (by omega)) hI.not_left

/-- **`RefProgress.arrState` for the states of the phase and its exit**: the load leader past
its third `bar.sync 0` (instruction 379) has arrived on the state barrier and issued the 16
loads of the initial state. -/
theorem arrState_startup {k : Nat} {s : D} (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k s ∨ Out P X g k s) (hgl : g = loadLeader L (g / L.block))
    (hpc : 379 < s.site.pc) :
    1 ≤ arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take k) ∧
      16 ≤ ((X.tr g).take k).countP (issuesTo (Bar.state.loc L (g / L.block))) := by
  have hstate : Bar.state.loc L (g / L.block) = ⟨.shared, g / L.block, P.sharedBase + 98384⟩ := by
    simp only [Bar.loc, Bar.off, hpre.sharedBase]
  have ht : tid g = 128 := by
    have hb := hpre.block
    unfold tid
    rw [hgl]
    simp only [loadLeader, thr, hb]
    omega
  rcases hI with hI | ho
  · obtain ⟨pos, hr, hl⟩ := id hI
    have hb3 : 3 ≤ (led g pos).bars := by
      rw [led_bar0, ← hr.site]
      have : List.Sublist (bar0Pcs.filter (· < 380)) (bar0Pcs.filter (· < s.site.pc)) :=
        List.monotone_filter_right _ fun a ha => by
          simp only [decide_eq_true_eq] at ha ⊢
          omega
      exact this.length_le
    obtain rfl := led_bars3 hb3
    have h1 : ((X.tr g).take k).countP isArr = 1 := by
      have h : ((X.tr g).take k).countP isArr = (led g .wait).arrs := congrArg Led.arrs hl
      rw [h]
      simp [led, ht]
    have h2 : ((X.tr g).take k).countP isIssue = 16 := by
      have h : ((X.tr g).take k).countP isIssue = (led g .wait).issues :=
        congrArg Led.issues hl
      rw [h]
      simp [led, ht]
    rw [hstate, arrivals_state hpre hX hg hσ hI, issues_state hpre hX hg hσ hI, h1, h2]
    exact ⟨le_rfl, le_rfl⟩
  · obtain ⟨-, h2, h3⟩ := out_bar_counts hpre hX hg hσ ho .state
    rw [h2, h3]
    simp [ht]

end

/-! ### The warp collectives: field `coll` -/

/-- The positions of the warp collectives of a warp, in program order (the body of
`Schedule/Defs.lean: collPcs`): warp 0 also elects the lane that initializes the mbarriers
(61, 93), the load warp first elects the load leader (32). -/
def collList (w : Nat) : List Nat :=
  if w = 0 then [48, 52, 55, 61, 87, 93, 312]
  else if w = 4 then [32, 48, 52, 55, 87, 312]
  else [48, 52, 55, 87, 312]

theorem w0_eq (g : Nat) : w0 g = if warp g = 0 then 1 else 0 := by
  have h1 := tid_eq g
  have h2 := lane_lt g
  unfold w0
  split_ifs <;> first | rfl | omega

theorem w4_eq (g : Nat) : w4 g = if warp g = 4 then 1 else 0 := by
  have h1 := tid_eq g
  have h2 := lane_lt g
  unfold w4
  split_ifs <;> first | rfl | omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **The shuffles and elections of a position** are the collective positions of the thread's
warp below the position's instruction (the role facts of the position decide the warp where
only one warp reaches it). -/
theorem led_coll {pos : Pos} {d : D} (h : AtPos P g pos d) :
    (led g pos).shfls + elects g pos =
      ((collList (warp g)).filter (· < pos.site.pc)).length := by
  have h1 := tid_eq g
  have h2 := lane_lt g
  have h3 := warp_lt g
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> (try fin_cases j) <;>
    simp only [AtPos, finVal] at h <;>
    simp only [led, elects, finVal, w0_eq, w4_eq, collList] <;>
    (by_cases hw0 : warp g = 0
     · simp only [hw0, ↓reduceIte]
       first | rfl | decide | (exfalso; omega)
     · by_cases hw4 : warp g = 4
       · simp only [hw4, ↓reduceIte]
         first | rfl | decide | (exfalso; omega)
       · simp only [hw0, hw4, ↓reduceIte]
         first | rfl | decide | (exfalso; omega))

/-- The same at the exit: all collectives of the warp. -/
theorem ledExit_coll (g : Nat) :
    3 + electsExit g = ((collList (warp g)).filter (· < (Site.fenceProxy 0).pc)).length := by
  simp only [electsExit, w0_eq, w4_eq, collList]
  by_cases hw0 : warp g = 0
  · simp only [hw0, ↓reduceIte]
    rfl
  · by_cases hw4 : warp g = 4
    · simp only [hw4, ↓reduceIte]
      rfl
    · simp only [hw0, hw4, ↓reduceIte]
      rfl

/-- **`RefProgress.coll` for a state of the phase and for its exit** (`collOf (g % L.block /
32) d.site.pc` unfolded, with `warp g`): the thread's shuffles and elections before the
position are the collective positions of its warp below the state's instruction. -/
theorem coll_startup {k : Nat} {s : D} (hI : InvE P X g k s ∨ OutE P X g k s) :
    ((X.tr g).take k).countP Sched.isWarpColl =
      ((collList (warp g)).filter (· < s.site.pc)).length := by
  rcases hI with ⟨pos, hr, -, hc⟩ | ⟨ho, hc⟩
  · rw [hc, led_coll hr.pos, hr.site]
  · rw [hc, ledExit_coll, ho.1.site]

/-! ### The counted events left: field `left_dec` -/

/-- **`RefProgress.left_dec` for a step from a state of the phase**, with the measure
`leftOf P g` of `Trace.lean` (a function of the state): a counted event lowers it, a failed
poll does not raise it. The successor `s'` is a state of the phase or its exit state. -/
theorem left_dec_startup (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) {k : Nat}
    {s s' : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hn : Thread.next L g s e = some (some s')) :
    leftOf P g s' + (if e.counts = true then 1 else 0) ≤ leftOf P g s := by
  have hC := sounds hpre
  have hret := retEv_upto hpre hX
    (shfl_first hpre hC hX hg (shfls_succ hpre hX hg he hσ hI)) (Nat.lt_succ_self k) he
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  exact left_step hpre hg k e s s' t ins o hI hat hc hf hret hn

/-- The measure of the exit state of the phase (the proxy fence at instruction 387) is 13:
the next phase continues from there. -/
theorem leftOf_exit {s : D} (h : Exit P g s) : leftOf P g s = 13 := by
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = .fenceProxy 0 := h.site
  rfl

/-- **A bound on the measure of every state**, in particular of the first one (the premise
`init` of the termination bound): at most `400 + 100 N` for `N` sequences. -/
theorem leftOf_le (hpre : Pre P L mem0) (d : D) : leftOf P g d ≤ 400 + 100 * P.sequences := by
  have h := seqOf_lt hpre g
  unfold leftOf
  split_ifs <;> omega

/-! ### The static parts of the warp collectives: fields `collShape`, `collKind` -/

/-- **The instruction and the static part of the `n`-th warp collective of a thread of warp
`w`**: the shuffles (48, 55, 87) are `shfl.sync.idx` with lane operand 0 and clamp 31, the
others elections over the full mask. With `F (c, w) n := collShapeAt w n` this is the function
the field `RefProgress.collShape` asks for. -/
def collShapeAt (w n : Nat) : Nat × Sched.CollShape :=
  match (collList w)[n]? with
  | some pc => (pc, if pc = 48 ∨ pc = 55 ∨ pc = 87 then .shfl .idx 0 31 else .elect 4294967295)
  | none => (0, .shfl .idx 0 31)

theorem collShapeAt_full (w n : Nat) : (collShapeAt w n).2.Full := by
  unfold collShapeAt
  split
  · split_ifs
    · trivial
    · rfl
  · trivial

theorem collShapeAt_tag (w n : Nat) : (collShapeAt w n).2.tag ≤ 1 := by
  unfold collShapeAt
  split
  · split_ifs <;> simp [Sched.CollShape.tag]
  · simp [Sched.CollShape.tag]

/-- The static part of the collective of a shuffle or election position. -/
def posShape : Pos → Sched.CollShape
  | .shfl _ => .shfl .idx 0 31
  | _ => .elect 4294967295

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- At a collective position, the collective with the position's count of predecessors is
the position's: its instruction and its static part. -/
theorem collShapeAt_pos {pos : Pos} {d : D} (h : AtPos P g pos d)
    (hc : (∃ j, pos = .elect j) ∨ ∃ j, pos = .shfl j) :
    collShapeAt (warp g) ((led g pos).shfls + elects g pos) = (pos.site.pc, posShape pos) := by
  have h1 := tid_eq g
  have h2 := lane_lt g
  have h3 := warp_lt g
  rcases pos with j | j | j | j | j | j | _ | j | _
  case elect =>
    fin_cases j <;> simp only [AtPos, finVal] at h <;>
      simp only [led, elects, finVal, w0_eq, w4_eq, collShapeAt, collList] <;>
      (by_cases hw0 : warp g = 0
       · simp only [hw0, ↓reduceIte]
         first | rfl | (exfalso; omega)
       · by_cases hw4 : warp g = 4
         · simp only [hw4, ↓reduceIte]
           first | rfl | (exfalso; omega)
         · simp only [hw0, hw4, ↓reduceIte]
           first | rfl | (exfalso; omega))
  case shfl =>
    fin_cases j <;>
      simp only [led, elects, finVal, w0_eq, w4_eq, collShapeAt, collList] <;>
      (by_cases hw0 : warp g = 0
       · simp only [hw0, ↓reduceIte]
         rfl
       · by_cases hw4 : warp g = 4
         · simp only [hw4, ↓reduceIte]
           rfl
         · simp only [hw0, hw4, ↓reduceIte]
           rfl)
  all_goals
    exfalso
    rcases hc with ⟨j', h'⟩ | ⟨j', h'⟩ <;> cases h'

/-- The template of an election whose mask register holds `-1` is an election over the full
mask. -/
theorem elect_tmplShape {t : TState} {r pr : Nat} {dst : Option Nat} {ty : Option DType}
    (hr : t.regs r = some (.bits 32 (i32 (-1)))) :
    Sched.tmplShape (eventTmpl Assumptions.all L g t
      (.warp ⟨.elect, ty, [dst, some pr], [], some (.reg r)⟩)) = some (.elect 4294967295) := by
  rw [full_mask] at hr
  have hm := readBits_b32 (L := L) (g := g) hr (by decide)
  have hmem : electMember (BitVec.ofNat 64 4294967295).toNat (laneOf L g) :=
    Sched.full_member (Nat.mod_lt _ (by decide))
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hm, hmem, ↓reduceIte, Sched.tmplShape]
  rfl

/-- The template of `shfl.sync.idx` with the immediate lane operand 0, clamp 31 and mask -1
is undefined behaviour or a shuffle with that static part. (The library's `Sched.warpOp_tmpl`
says this for every warp instruction with immediate operands, but its file cannot be imported
next to the thread layer: `Lemmas/Flow/NotWarpColl.lean` and `Lemmas/Flow/WordRead.lean` both
declare `PTX.Flow.readBits_imm`.) -/
theorem shfl_tmplShape {t : TState} {d pr ar : Nat} :
    (∃ f, eventTmpl Assumptions.all L g t (.warp ⟨.shfl .idx, some (.int .b 32),
        [some d, some pr], [.reg ar, .imm 0, .imm 31], some (.imm (-1))⟩) = .ub f) ∨
      Sched.tmplShape (eventTmpl Assumptions.all L g t (.warp ⟨.shfl .idx, some (.int .b 32),
        [some d, some pr], [.reg ar, .imm 0, .imm 31], some (.imm (-1))⟩)) =
        some (.shfl .idx 0 31) := by
  change (∃ f, shflTmpl L g t .idx d (some pr) (.reg ar) (.imm 0) (.imm 31) (.imm (-1)) =
      .ub f) ∨ Sched.tmplShape (shflTmpl L g t .idx d (some pr) (.reg ar) (.imm 0) (.imm 31)
      (.imm (-1))) = some (.shfl .idx 0 31)
  have hb : readBits L g t 32 (.imm 0) = .ok (truncBits 32 (BitVec.ofInt 64 0)) := rfl
  have hc : readBits L g t 32 (.imm 31) = .ok (truncBits 32 (BitVec.ofInt 64 31)) := rfl
  have hmk : readBits L g t 32 (.imm (-1)) = .ok (truncBits 32 (BitVec.ofInt 64 (-1))) := rfl
  cases hav : readValue L g t 32 (.reg ar) with
  | error f =>
    refine .inl ⟨f, ?_⟩
    simp only [shflTmpl, hav, hb, hc, hmk]
  | ok av =>
    by_cases h1 : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 ∧ L.block % 32 = 0
    · by_cases h2 : av.bytes = 4
      · refine .inr ?_
        simp only [shflTmpl, hav, hb, hc, hmk, h1, h2, and_self, ↓reduceIte, Sched.tmplShape]
        rfl
      · refine .inl ⟨.typeMismatch, ?_⟩
        simp only [shflTmpl, hav, hb, hc, hmk, h1, h2, and_self, ↓reduceIte]
    · refine .inl ⟨.noRule, ?_⟩
      simp only [shflTmpl, hav, hb, hc, hmk, h1, ↓reduceIte]

/-- The initial state satisfies the extended invariant. -/
theorem invE_init (hpre : Pre P L mem0) : InvE P X g 0 (init L g) := by
  obtain ⟨pos, h1, h2, h3⟩ := st_init (L := L) (g := g) hpre
  refine ⟨pos, h1, ?_, ?_⟩
  · rw [h2, List.take_zero]
    rfl
  · rw [h2, h3, List.take_zero]
    rfl

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

set_option maxRecDepth 8000 in
/-- **The extended invariant at every followed state, the last one included** (`startup_invE`
asks for a position before an event; the state after a thread's last event is the one the
progress argument looks at). -/
theorem startup_invE_le {k : Nat} {s : D} (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    InvE P X g k s ∨ LeftE P L X g k := by
  rcases Nat.lt_or_ge k (X.tr g).length with h | h
  · exact startup_invE hpre hX hg h hσ
  · cases k with
    | zero =>
      rw [Frame.stateAt_zero] at hσ
      obtain rfl := Option.some.inj (Option.some.inj hσ)
      exact .inl (invE_init hpre)
    | succ k =>
      obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨sk, hσk⟩ := followed_of_le hσ (Nat.le_succ k)
      rcases startup_invE hpre hX hg (by omega) hσk with hI | ⟨j, hj, s0, h1, h2⟩
      · obtain ⟨s2, hσ2, hn⟩ := inv_next hpre hX hg he hσk hI
        have hs2 : s2 = s := Option.some.inj (Option.some.inj (hσ2.symm.trans hσ))
        rw [hs2] at hn
        rcases hn with h1 | h1
        · exact .inl h1
        · exact .inr ⟨k + 1, le_rfl, s, hσ, h1⟩
      · exact .inr ⟨j, by omega, s0, h1, h2⟩

/-- **`RefProgress.collShape`, events**: a shuffle or an election fired at a state of the
phase has the static part of the collective of its ordinal. -/
theorem collShape_startup {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : InvE P X g k s)
    (hc : Sched.isWarpColl e = true) :
    Sched.kindShape e.kind =
      some (collShapeAt (warp g) (((X.tr g).take k).countP Sched.isWarpColl)).2 := by
  obtain ⟨pos, hr, -, hcl⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hcode, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  have hev := ev_full hpre hg pos hr hat hcode hf
  rw [hcl]
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
  · obtain ⟨inst, ld, rfl⟩ := hev
    rw [collShapeAt_pos hr.pos (.inl ⟨j, rfl⟩)]
    rfl
  · obtain ⟨v, ok, rfl⟩ := hev
    rw [collShapeAt_pos hr.pos (.inr ⟨j, rfl⟩)]
    rfl
  · subst hev
    cases hc
  · subst hev
    cases hc
  · subst hev
    cases hc
  · obtain ⟨i, hi, bs, hbs, rfl⟩ := hev
    cases hc
  · subst hev
    cases hc
  · subst hev
    cases hc
  · obtain ⟨ok, rfl⟩ := hev
    cases hc

omit hX in
/-- **`RefProgress.collShape`, templates**: at a state of the phase at an election or a
shuffle, the template of the instruction is undefined behaviour or is the collective of the
state's ordinal: its instruction and its static part. -/
theorem collTmpl_startup {k : Nat} {s : D} {t : TState} {m : Tmpl} (hI : InvE P X g k s)
    (hcoll : (∃ j, s.site = .elect j) ∨ ∃ j, s.site = .shfl j)
    (hat : (code L g).AtD s t) (hinv : (code L g).inv s)
    (hout : out kernel Assumptions.all L g t = .ev m) :
    (∃ f, m = .ub f) ∨
      (t.pc = (collShapeAt (warp g) (((X.tr g).take k).countP Sched.isWarpColl)).1 ∧
        Sched.tmplShape m =
          some (collShapeAt (warp g) (((X.tr g).take k).countP Sched.isWarpColl)).2) := by
  obtain ⟨pos, hr, -, hcl⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  have hC := sounds hpre g hg
  obtain ⟨ins, hcode, -, -⟩ := (hC.steps ⟨pos.site, w, p, x⟩).site hinv
  have hso := Code.site_out hC (d := ⟨pos.site, w, p, x⟩) (t := t) ⟨hat, hinv⟩
  rw [hso] at hout
  have hm : m = eventTmpl Assumptions.all L g t ins.op := by
    injection hout with hm
    rw [← hm]
    simp only [Code.tmpl, hcode]
  subst hm
  have hpc : t.pc = pos.site.pc := hat.1
  have hpos := hr.pos
  rw [hcl]
  rcases pos with j | j | j | j | j | j | _ | j | _
  case elect =>
    rw [collShapeAt_pos hpos (.inl ⟨j, rfl⟩)]
    refine .inr ⟨hpc, ?_⟩
    fin_cases j <;> simp only [AtPos, Fin.isValue] at hpos <;>
      obtain rfl := Option.some.inj (hcode.symm.trans (by code_lookup))
    · have r1 := reg_w hat (r := 331) (by lit_mem) (n := 32) rfl
      simp only [hpos] at r1
      exact elect_tmplShape r1
    · have r1 := reg_w hat (r := 334) (by lit_mem) (n := 32) rfl
      simp only [hpos] at r1
      exact elect_tmplShape r1
    · have r1 := reg_w hat (r := 339) (by lit_mem) (n := 32) rfl
      simp only [hpos] at r1
      exact elect_tmplShape r1
    · have r1 := reg_w hat (r := 356) (by lit_mem) (n := 32) rfl
      simp only [hpos] at r1
      exact elect_tmplShape r1
    · have r1 := reg_w hat (r := 487) (by lit_mem) (n := 32) rfl
      simp only [hpos] at r1
      exact elect_tmplShape r1
  case shfl =>
    rw [collShapeAt_pos hpos (.inr ⟨j, rfl⟩)]
    fin_cases j <;> obtain rfl := Option.some.inj (hcode.symm.trans (by code_lookup)) <;>
      (rcases shfl_tmplShape (L := L) (g := g) (t := t) with hu | hsh
       · exact .inl hu
       · exact .inr ⟨hpc, hsh⟩)
  all_goals
    exfalso
    rcases hcoll with ⟨j', h'⟩ | ⟨j', h'⟩ <;> cases h'

omit hX in
/-- **`RefProgress.collKind`**: the template at an election or a shuffle of the phase, when
it has a static part, is a shuffle or an election (tag at most 1). -/
theorem collKind_startup {k : Nat} {s : D} {t : TState} {m : Tmpl} {sh : Sched.CollShape}
    (hI : InvE P X g k s) (hcoll : (∃ j, s.site = .elect j) ∨ ∃ j, s.site = .shfl j)
    (hat : (code L g).AtD s t) (hinv : (code L g).inv s)
    (hout : out kernel Assumptions.all L g t = .ev m) (hsh : Sched.tmplShape m = some sh) :
    sh.tag ≤ 1 := by
  rcases collTmpl_startup hpre hg hI hcoll hat hinv hout with ⟨f, rfl⟩ | ⟨-, h⟩
  · cases hsh
  · rw [h] at hsh
    obtain rfl := Option.some.inj hsh
    exact collShapeAt_tag _ _

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
