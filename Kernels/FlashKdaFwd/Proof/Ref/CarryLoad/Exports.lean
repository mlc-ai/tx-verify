-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Links
public import Kernels.FlashKdaFwd.Proof.Protocol.UnionClass

@[expose] public section

/-! # The exports of the CarryLoad phase, by contract

Facts about the events of a thread at the states of the phase, in the shapes the contracts of
the layers above ask for. A state "of the phase" is a followed state with the invariant
(`Inv P X g k1 k s`: before the 128 carry loads and the proxy fence) or with the exit condition
(`Out P X g k s`: before the `bar.sync 0` of instruction 1402). Hypotheses everywhere: the
precondition `Pre`, consistency, the thread is launched. The exports that need a count per
mbarrier or of a class that the phases before the tile loops do not count also take the
thread's history `Entered P L X g j0 k1` (`Links.lean`: the first exit of the startup phase at
`j0`, the entry of the CarryLoad phase at `k1`).

**Events in closed form** (`event_at` of `Trace.lean` is the general statement):

* `site_cases`, `pc_carry`, `kind_carry`, `compute_of_load`: where a state of the invariant
  is: at carry load `j` (a compute thread, `j` events after the entry) or at the proxy fence;
  instructions 765 to 1401, sub-step 0; a load site or the fence, so never a poll, a warp
  collective or a matrix site.
* `read_carry`: the event at carry load `j` is the read of the four bytes at `ldAddr P g j`.
* `fence_carry`: the event at the fence is `fence.proxy.async.shared::cta`.
* `bar_exit`: the event at the exit state is `bar.sync 0` (instruction 1402).
* `no_bar_carry`: no event at a state of the invariant is a barrier arrival.

**Protocol layer, `UnionFacts`** (`Proof/Protocol/UnionClass.lean`):

* `union_thread_carry`: field `thread` for the events of the phase: an access of a byte of the
  union region (the FP32 state buffer) is a read in the thread's own block, after the thread's
  successful poll of the state mbarrier, of class `early` (at most five `bar.sync 0` before).
* `bar_fence_exit`: field `bar_fence` for the sixth `bar.sync 0`: the event before the exit
  state is the proxy fence of the same thread.

**Protocol layer, `BarFacts`** (`Proof/Protocol/Bars.lean`): `bar_ev_exit` (fields `shape` and
`bar0_pc` for the barrier at 1402: `bar.sync 0` at instruction 1402 with five earlier ones) and
`bar_sched_exit` (field `sched`: it is the sixth barrier arrival of any kind).

**Direct safety facts** (`Proof/Top/Wire.lean: DirectFacts`):

* `touch_carry`, `memTouches_carry`: what an operation issued at a state of the invariant
  touches: the four bytes of a carry load. `memTouches_exit`: the barrier touches nothing.
* `memSpaces_carry` (field `memSpaces`), `sharedFrame_carry` (field `sharedFrame`: the bytes
  lie in the FP32 state buffer, offsets 32768 to 98304 of the window of the thread's block).
* The control half of `computeNoUb` / `loadNoUb` / `storeNoUb`: `Trace.lean: carry_noUb` (no
  event of the phase is undefined behaviour, with no condition on the data), `carry_ok` (under
  the data condition `DataOk` the machine's successor is a state), `exit_event`, `exit_next`.

**Progress contract** (`Proof/Schedule/Contract.lean: RefProgress`), in the terms the fields
unfold to:

* `bar0_carry`, `bar0_exit`: field `bar0` (five `bar.sync 0` instructions lie below every
  instruction of the phase).
* `carried_inv`, `carried_exit`: the counts of `Links.lean: Carried` at a state of the phase,
  for the fields `bar8` (no named barrier), `matrix` (no matrix event), `arrState` (the load
  leader's arrival on and 16 loads completing on the state mbarrier), and the lower bounds
  `arrLoadEmpty` to `arrStoreEmpty` (the tile index is 0). `coll_carry`: field `coll`: the
  shuffles and elections are those of the startup's first exit.
* `barStep_exit`: field `barStep` for the barrier at 1402: sub-step 0, and the next state is at
  a later instruction (whatever the role: `after_bar_5_pc`).
* `leftOf`, `leftOf_dec`, `leftOf_entry`, `leftOf_exit`, `leftOf_le`: field `left_dec`: the
  number of events left in the phase as a function of the state (`1403 -` the instruction),
  which every step from a state of the invariant lowers by at least one; 638 or 2 at the
  entry (compute thread or not), 1 at the exit state. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar bar0Before bar0Pcs)

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {e : Event}

/-! ### Where a state of the phase is -/

/-- The instruction of a position: `765 + 5 j` for carry load `j`, 1401 for the fence. -/
def pcOf : Pos → Nat
  | .ld j => 765 + 5 * j.val
  | .fence => 1401

theorem site_pcOf (pos : Pos) : pos.site.pc = pcOf pos := by
  cases pos with
  | ld j => exact ldSite_pc j.val j.isLt
  | fence => rfl

/-- A position has fewer events of the phase before it than the exit. -/
theorem done_lt_len {pos : Pos} {d : D} (h : RefAt P g pos d) : done g pos < len g := by
  cases pos with
  | ld j =>
    have hc : tid g < 128 := h.pos.1
    simp only [done, len, hc, ↓reduceIte]
    omega
  | fence =>
    simp only [done, len]
    split <;> omega

/-- **Where a state of the invariant is**: at carry load `j`, in a compute thread, `j` events
after the entry; or at the proxy fence, 128 events after the entry in a compute thread and at
the entry in a thread of the load or the store warp. -/
theorem site_cases {k0 k : Nat} {s : D} (hI : Inv P X g k0 k s) :
    (∃ j : Fin 128, s.site = ldSite j.val ∧ tid g < 128 ∧ k = k0 + j.val) ∨
      (s.site = .fenceProxy 1 ∧ k = k0 + if tid g < 128 then 128 else 0) := by
  obtain ⟨pos, hr, -, hd⟩ := hI
  cases pos with
  | ld j => exact .inl ⟨j, hr.site, hr.pos.1, hd⟩
  | fence => exact .inr ⟨hr.site, hd⟩

/-- **A state of the invariant is at an instruction from 765 to 1401, at sub-step 0.** -/
theorem pc_carry {k0 k : Nat} {s : D} (hI : Inv P X g k0 k s) :
    765 ≤ s.site.pc ∧ s.site.pc ≤ 1401 ∧ s.site.sub = 0 := by
  obtain ⟨pos, hr, -⟩ := hI
  rw [hr.site, site_pcOf]
  cases pos with
  | ld j =>
    have := j.isLt
    exact ⟨by simp only [pcOf]; omega, by simp only [pcOf]; omega, ldSite_sub j.isLt⟩
  | fence => exact ⟨by decide, by decide, rfl⟩

/-- **A state of the invariant is at a load site or at the proxy fence** (so at no poll, no
shuffle or election, no matrix site and no barrier). -/
theorem kind_carry {k0 k : Nat} {s : D} (hI : Inv P X g k0 k s) :
    (∃ j, s.site = .load j) ∨ s.site = .fenceProxy 1 := by
  rcases site_cases hI with ⟨j, hs, -⟩ | ⟨hs, -⟩
  · refine .inl ⟨⟨31 + j.val, by omega⟩, ?_⟩
    rw [hs]
    simp only [ldSite, j.isLt, ↓reduceDIte]
  · exact .inr hs

/-- **Only a compute thread is at a carry load.** -/
theorem compute_of_load {k0 k : Nat} {s : D} (hI : Inv P X g k0 k s)
    (hs : ∃ j, s.site = .load j) : tid g < 128 := by
  obtain ⟨j, hj⟩ := hs
  rcases site_cases hI with ⟨_, -, hc, -⟩ | ⟨hf, -⟩
  · exact hc
  · rw [hj] at hf
    cases hf

/-- The exit state is at instruction 1402, at sub-step 0. -/
theorem pc_exit {s : D} (ho : Exit P g s) : s.site.pc = 1402 ∧ s.site.sub = 0 := by
  rw [ho.site]
  exact ⟨rfl, rfl⟩

/-! ### The events in closed form -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **The event at carry load `j`**: the read of the four bytes at `ldAddr P g j` (the swizzled
address of the thread's base pointer plus the constant of the load) of the shared window of
the thread's own block; the thread is a compute thread and the load is its event `k0 + j`. -/
theorem read_carry {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) {j : Nat}
    (hj : j < 128) (hs : s.site = ldSite j) :
    ∃ bs, bs.length = 4 ∧ e = ⟨765 + 5 * j,
      .rd { loc := ⟨.shared, cta g, ldAddr P g j⟩, size := 4 } bs⟩ ∧ tid g < 128 ∧
      k = k0 + j := by
  obtain ⟨pos, hr, hev, hd⟩ := event_at hpre hX hg he hσ hI
  cases pos with
  | ld j' =>
    obtain rfl : j'.val = j := ldSite_inj j'.isLt hj (hr.site.symm.trans hs)
    obtain ⟨bs, hbs, rfl⟩ := hev
    exact ⟨bs, hbs, rfl, hr.pos.1, hd⟩
  | fence => exact absurd (hs.symm.trans hr.site) (ldSite_ne_fence hj)

/-- **The event at the proxy fence** is `fence.proxy.async.shared::cta` (instruction 1401). -/
theorem fence_carry {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hs : s.site = .fenceProxy 1) :
    e = ⟨1401, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  obtain ⟨pos, hr, hev, -⟩ := event_at hpre hX hg he hσ hI
  cases pos with
  | ld j => exact absurd (hr.site.symm.trans hs) (ldSite_ne_fence j.isLt)
  | fence => exact hev

omit hg in
/-- **The event at the exit state** is `bar.sync 0` (instruction 1402). -/
theorem bar_exit {k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (ho : Exit P g s) :
    e = ⟨1402, .bar 0 none .sync⟩ :=
  exit_event hpre hX he hσ ho

/-- **No event at a state of the invariant is a barrier arrival.** -/
theorem no_bar_carry {k0 k : Nat} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    ∀ pc id cnt m, e ≠ ⟨pc, .bar id cnt m⟩ := by
  obtain ⟨pos, -, hev, -⟩ := event_at hpre hX hg he hσ hI
  rintro pc id cnt m rfl
  rcases hev.kind_cases with ⟨_, _, h, -⟩ | ⟨_, _, h⟩ <;> cases h

/-! ### The counts at a state of the phase -/

omit hpre hX hg in
/-- The ledger of a state of the invariant has five `bar.sync 0`. -/
theorem bars_inv {k0 k : Nat} {s : D} (hI : Inv P X g k0 k s) : bar0Before X (g, k) = 5 := by
  obtain ⟨pos, -, hl, -⟩ := hI
  exact congrArg Startup.Led.bars hl

omit hpre hX hg in
/-- The ledger of the exit state has five `bar.sync 0`. -/
theorem bars_exit {k : Nat} {s : D} (ho : Out P X g k s) : bar0Before X (g, k) = 5 :=
  congrArg Startup.Led.bars ho.2.1

/-- **The counts of `Carried` at a state of the invariant**: no named barrier, no matrix
event, no tensor store, commit, group wait or global write; one successful poll of the state
mbarrier and none of the others; the load leader's arrival and 16 loads on the state
mbarrier. -/
theorem carried_inv {j0 k1 k : Nat} {s : D} (hen : Entered P L X g j0 k1)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k1 k s) :
    Carried P L X g k := by
  obtain ⟨pos, hr, -, hd⟩ := id hI
  have := done_lt_len hr
  have := hen.le
  exact carried hpre hX hg hen hσ (by omega) (by omega)

/-- **The counts of `Carried` at the exit state.** -/
theorem carried_exit {j0 k1 k : Nat} {s : D} (hen : Entered P L X g j0 k1)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hout : (phase P L X g).Out k1 k s) :
    Carried P L X g k := by
  obtain ⟨rfl, -⟩ := hout
  have := hen.le
  exact carried hpre hX hg hen hσ (by omega) le_rfl

/-- **`RefProgress.coll` at a state of the invariant**: the thread's shuffles and elections
are those of its first exit from the startup phase. -/
theorem coll_carry {j0 k1 k : Nat} {s : D} (hen : Entered P L X g j0 k1)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k1 k s) :
    ((X.tr g).take k).countP Sched.isWarpColl =
      ((X.tr g).take j0).countP Sched.isWarpColl := by
  obtain ⟨pos, hr, -, hd⟩ := id hI
  have := done_lt_len hr
  have := hen.le
  exact coll_keep hpre hX hg hen hσ (by omega) (by omega)

/-! ### Protocol layer: the union region -/

/-- **`UnionFacts.thread` for the events of the phase**: an access, at a state of the
invariant, of a byte of the union region of block `c` is by a thread of block `c` that has
polled the state mbarrier of the block successfully, and it is an `early` access: a read with
at most five `bar.sync 0` before it. (The only accesses of the phase are the carry loads.) -/
theorem union_thread_carry {j0 k1 k c : Nat} {s : D} {a : Acc} {w : Bool} {l : Loc}
    {O : Protocol.Owners} (hen : Entered P L X g j0 k1)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k1 k s)
    (hacc : X.Access (g, k) a w) (hcov : a.Covers l) (hu : Protocol.InUnion L c l) :
    g / L.block = c ∧ 1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take k) ∧
      Protocol.ThreadClass L X O c g k w l := by
  have hC := carried_inv hpre hX hg hen hσ hI
  have hbar := bars_inv hI
  have key : ∀ e, X.get (g, k) = some e → ∀ a', AccessOf e a' → a'.loc.cta = cta g ∧
      ∀ bs pc, e ≠ ⟨pc, .wr a' bs⟩ := by
    intro e he a' ha'
    obtain ⟨pos, -, hev, -⟩ := event_at hpre hX hg he hσ hI
    cases pos with
    | ld j =>
      obtain ⟨bs, -, rfl⟩ := hev
      obtain rfl : a' = _ := ha'
      exact ⟨rfl, fun _ _ h => by cases h⟩
    | fence =>
      obtain rfl := hev
      exact ha'.elim
  have hc : g / L.block = c := by
    have h1 : a.loc.cta = cta g := by
      rcases hacc with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩ <;>
        exact (key _ he a rfl).1
    rw [block_div hpre, ← h1, ← hcov.2.1, hu.2.1]
  subst hc
  refine ⟨rfl, hC.polled, .early ?_ (by rw [hbar])⟩
  rcases hacc with ⟨bs, -, hw⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
  · exact hw
  · exact absurd rfl ((key _ he a rfl).2 bs pc)
  · obtain ⟨pos, -, hev, -⟩ := event_at hpre hX hg he hσ hI
    rcases hev.kind_cases with ⟨_, _, h, -⟩ | ⟨_, _, h⟩ <;> cases h

omit hpre hX hg in
/-- **`UnionFacts.bar_fence` for the sixth `bar.sync 0`**: the event before the exit state is
the proxy fence of instruction 1401 of the same thread. -/
theorem bar_fence_exit {k : Nat} {s : D} (ho : Out P X g k s) :
    0 < k ∧ ∃ pcf, X.get (g, k - 1) =
      some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ :=
  ⟨ho.2.2.1, 1401, ho.2.2.2⟩

/-! ### Protocol layer: the barrier at 1402 -/

omit hg in
/-- **`BarFacts.shape` and `bar0_pc` for the barrier of the exit state**: it is `bar.sync 0`
without a thread count, at instruction 1402, the sixth of the nine positions. -/
theorem bar_ev_exit {k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {s : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (ho : Out P X g k s) :
    mode = .sync ∧ id = 0 ∧ cnt = none ∧ pc = 1402 ∧ bar0Before X (g, k) = 5 ∧
      bar0Pcs[bar0Before X (g, k)]? = some pc := by
  have h := bar_exit hpre hX he hσ ho.1
  simp only [Event.mk.injEq, Kind.bar.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  have hb := bars_exit ho
  refine ⟨rfl, rfl, rfl, rfl, hb, ?_⟩
  rw [hb]
  rfl

/-- **`BarFacts.sched` for the barrier of the exit state**: it is the sixth barrier arrival of
the thread (the five before it are `bar.sync 0`), which the schedule says is a `bar.sync 0`
whatever the role and the number of tiles `T`. -/
theorem bar_sched_exit {j0 k1 k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {s : D}
    (hen : Entered P L X g j0 k1) (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hout : (phase P L X g).Out k1 k s)
    (compute : Bool) (T : Nat) :
    (id, cnt, mode) = Protocol.barSched compute T (((X.tr g).take k).countP Execution.isBar) := by
  have hC := carried_exit hpre hX hg hen hσ hout
  obtain ⟨rfl, rfl, rfl, -, hb, -⟩ := bar_ev_exit hpre hX he hσ hout.2
  have h5 : ((X.tr g).take k).countP Execution.isBar = 5 := hC.bars.trans hb
  rw [h5]
  simp [Protocol.barSched]

/-! ### Direct safety facts -/

/-- **What an event at a state of the invariant accesses**: the four bytes of a carry load,
in a compute thread. The phase issues no asynchronous operation. -/
theorem touch_carry {k0 k : Nat} {s : D} {a : Acc} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (ha : AccessOf e a ∨ AsyncOf e a) :
    ∃ j : Fin 128, a = { loc := ⟨.shared, cta g, ldAddr P g j.val⟩, size := 4 } ∧
      tid g < 128 := by
  obtain ⟨pos, hr, hev, -⟩ := event_at hpre hX hg he hσ hI
  cases pos with
  | ld j =>
    obtain ⟨bs, -, rfl⟩ := hev
    rcases ha with ha | ha
    · exact ⟨j, ha, hr.pos.1⟩
    · exact ha.elim
  | fence =>
    obtain rfl := hev
    rcases ha with ha | ha <;> exact ha.elim

/-- **What a memory operation issued at a state of the invariant touches**
(`Execution.MemTouches`: thread accesses, `nc` reads, the stages of asynchronous operations):
the four bytes of a carry load. -/
theorem memTouches_carry {k0 k : Nat} {s : D} {r : AsyncCopy.Ref} {a : Acc}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    ∃ j : Fin 128, a = { loc := ⟨.shared, cta g, ldAddr P g j.val⟩, size := 4 } ∧
      tid g < 128 := by
  rcases ht with ⟨w, hi⟩ | ⟨i, bs, hri, pc, hnc⟩
  · obtain ⟨e, he, ha⟩ := Frame.intent_issuer hi
    rw [hr] at he
    exact touch_carry hpre hX hg he hσ hI ha
  · subst hri
    have hi : i = (g, k) := hr
    subst hi
    exact touch_carry hpre hX hg hnc hσ hI (.inl rfl)

omit hg in
/-- The barrier of the exit state touches no memory. -/
theorem memTouches_exit {k : Nat} {s : D} {r : AsyncCopy.Ref} {a : Acc}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (ho : Exit P g s) : False := by
  rcases ht with ⟨w, hi⟩ | ⟨i, bs, hri, pc, hnc⟩
  · obtain ⟨e, he, ha⟩ := Frame.intent_issuer hi
    rw [hr] at he
    obtain rfl := bar_exit hpre hX he hσ ho
    rcases ha with ha | ha <;> exact ha.elim
  · subst hri
    have hi : i = (g, k) := hr
    subst hi
    have := bar_exit hpre hX hnc hσ ho
    cases this

/-- **`DirectFacts.memSpaces` for the phase**: what it touches is shared memory. -/
theorem memSpaces_carry {k0 k : Nat} {s : D} {r : AsyncCopy.Ref} {a : Acc}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    a.loc.space = .shared ∨ a.loc.space = .global := by
  obtain ⟨j, rfl, -⟩ := memTouches_carry hpre hX hg hr ht hσ hI
  exact .inl rfl

/-- **`DirectFacts.sharedFrame` for the phase**: the bytes a carry load reads are bytes of the
FP32 state buffer (offsets 32768 to 98304) of the window of the thread's own block. -/
theorem sharedFrame_carry {k0 k : Nat} {s : D} {r : AsyncCopy.Ref} {a : Acc}
    (hr : r.issuer = (g, k)) (ht : X.MemTouches r a)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s) :
    a.loc.cta = g / L.block ∧ P.sharedBase + 32768 ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304 := by
  obtain ⟨j, rfl, hc⟩ := memTouches_carry hpre hX hg hr ht hσ hI
  obtain ⟨f1, f2, -⟩ := ldAddr_frame hpre hc j.isLt
  exact ⟨(block_div hpre).symm, f1, f2⟩

end

/-! ### Progress: `bar0`, `barStep`, the events left -/

/-- Five `bar.sync 0` instructions lie below an instruction from 622 to 1402. -/
theorem bar0_five {pc : Nat} (h1 : 621 < pc) (h2 : pc ≤ 1402) :
    (bar0Pcs.filter (· < pc)).length = 5 := by
  have e1 : decide (85 < pc) = true := decide_eq_true (by omega)
  have e2 : decide (110 < pc) = true := decide_eq_true (by omega)
  have e3 : decide (379 < pc) = true := decide_eq_true (by omega)
  have e4 : decide (620 < pc) = true := decide_eq_true (by omega)
  have e5 : decide (621 < pc) = true := decide_eq_true (by omega)
  have e6 : decide (1402 < pc) = false := decide_eq_false (by omega)
  have e7 : decide (3113 < pc) = false := decide_eq_false (by omega)
  have e8 : decide (3775 < pc) = false := decide_eq_false (by omega)
  have e9 : decide (3834 < pc) = false := decide_eq_false (by omega)
  simp [bar0Pcs, List.filter, e1, e2, e3, e4, e5, e6, e7, e8, e9]

/-- **`RefProgress.bar0` for a state of the invariant**: the thread's `bar.sync 0` count is
the number of `bar.sync 0` instructions below the state's instruction. -/
theorem bar0_carry {k0 k : Nat} {s : D} (hI : Inv P X g k0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨h1, h2, -⟩ := pc_carry hI
  rw [bar0_five (by omega) (by omega)]
  exact bars_inv hI

/-- **`RefProgress.bar0` at the exit state.** -/
theorem bar0_exit {k : Nat} {s : D} (ho : Out P X g k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  rw [(pc_exit ho.1).1, bar0_five (by omega) le_rfl]
  exact bars_exit ho

variable {L : Launch} {g : Nat}

theorem tail_1436_pc (d : D) : 1402 < (tail_1436 L g d).site.pc := by
  unfold tail_1436
  dsimp only
  decide

theorem tail_1412_pc (d : D) : 1402 < (tail_1412 L g d).site.pc := by
  unfold tail_1412
  dsimp only
  split
  · dsimp only
    decide
  · exact tail_1436_pc _

theorem tail_2117_pc (d : D) : 1402 < (tail_2117 L g d).site.pc := by
  unfold tail_2117
  dsimp only
  split <;> (dsimp only; decide)

theorem tail_2949_pc (d : D) : 1402 < (tail_2949 L g d).site.pc := by
  unfold tail_2949
  dsimp only
  repeat' split
  all_goals (dsimp only; decide +kernel)

/-- **The transition of the barrier at 1402 leads to a later instruction**, whatever the
registers: every branch of the local code after it ends at a site of the tile loops or of the
epilogue (the first poll of the role's loop, the `bar.sync 0` at 3113, or a breakpoint behind
a condition that the tile loops' phases exclude). -/
theorem after_bar_5_pc (d : D) : 1402 < (after_bar_5 L g d).site.pc := by
  unfold after_bar_5
  dsimp only
  split
  · split
    · split
      · dsimp only
        decide
      · exact tail_2949_pc _
    · split
      · dsimp only
        decide
      · split
        · dsimp only
          decide
        · exact tail_2117_pc _
  · split
    · split
      · dsimp only
        decide
      · dsimp only
        decide
    · exact tail_1412_pc _

/-- **`RefProgress.barStep` for the barrier at 1402**: the barrier event is fired at sub-step
0 and the next state is at a later instruction. -/
theorem barStep_exit {k : Nat} {s s' : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (ho : Exit P g s)
    (hσ' : Frame.stateAt (code L) X g (k + 1) = some (some s')) :
    s.site.sub = 0 ∧ s.site.pc < s'.site.pc := by
  rw [Frame.stateAt_succ he, hσ] at hσ'
  have hn : Thread.next L g s e = some (some s') := hσ'
  rw [exit_next ho e] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  obtain ⟨h1, h2⟩ := pc_exit ho
  exact ⟨h2, by rw [h1]; exact after_bar_5_pc s⟩

/-- **The events left in the phase, as a function of the state**: the distance of the state's
instruction from the instruction after the barrier at 1402. It is at most 638 at a carry load,
2 at the fence and 1 at the exit state; the measure of a whole run is this number plus the
measure the tile loop gives the state after the barrier. -/
def leftOf (d : D) : Nat := 1403 - d.site.pc

theorem leftOf_le (d : D) : leftOf d ≤ 1403 := Nat.sub_le _ _

theorem leftOf_exit {s : D} (ho : Exit P g s) : leftOf s = 1 := by
  simp only [leftOf, (pc_exit ho).1]

/-- **The events left at the entry of the phase**: 638 for a compute thread (at its first
carry load, instruction 765), 2 for a thread of the load or the store warp (at the fence). -/
theorem leftOf_entry {s : D} (h : Entry P g s) :
    leftOf s = if tid g < 128 then 638 else 2 := by
  have hs := h.site
  by_cases hc : tid g < 128 <;> simp only [hc, ↓reduceIte] at hs ⊢ <;> rw [leftOf, hs] <;> rfl

/-- The instructions of two positions, the second with one more event before it. -/
theorem pcOf_lt {pos pos' : Pos} {d d' : D} (h : RefAt P g pos d) (h' : RefAt P g pos' d')
    (hd : done g pos' = done g pos + 1) : pcOf pos < pcOf pos' ∧ pcOf pos' ≤ 1401 := by
  cases pos with
  | ld j =>
    cases pos' with
    | ld j' =>
      have := j'.isLt
      simp only [done] at hd
      simp only [pcOf]
      omega
    | fence =>
      have := j.isLt
      simp only [pcOf]
      omega
  | fence =>
    cases pos' with
    | ld j' =>
      have hc : tid g < 128 := h'.pos.1
      have := j'.isLt
      simp only [done, hc, ↓reduceIte] at hd
      omega
    | fence =>
      simp only [done] at hd
      omega

/-- **`RefProgress.left_dec` for a step from a state of the invariant**: the successor has at
least one event less left (it is at a later instruction, at most 1402). -/
theorem leftOf_dec (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k0 k : Nat} {s s' : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k0 k s)
    (hn : Thread.next L g s e = some (some s')) : leftOf s' + 1 ≤ leftOf s := by
  obtain ⟨pos, hr, -, hd⟩ := id hI
  have hpc : s.site.pc = pcOf pos := by rw [hr.site, site_pcOf]
  rcases inv_next hpre hX hg he hσ hI hn with ⟨pos', hr', -, hd'⟩ | ⟨hk, hE, -⟩
  · have hpc' : s'.site.pc = pcOf pos' := by rw [hr'.site, site_pcOf]
    obtain ⟨h1, h2⟩ := pcOf_lt hr hr' (by omega)
    simp only [leftOf, hpc, hpc']
    omega
  · obtain ⟨-, h2, -⟩ := pc_carry hI
    simp only [leftOf, (pc_exit hE).1]
    omega

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
