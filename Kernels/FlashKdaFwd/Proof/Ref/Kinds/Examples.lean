-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Kinds
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Trace

@[expose] public section

/-! # Worked examples for `Ref/Kinds.lean`, against the startup phase

Nothing imports this file. It shows, on the startup phase (`Ref/Startup/`), the three
steps of a count that a phase never put in its ledger:

1. *Every position of the phase is of a kind that cannot fire the class* (`pos_not_matrix`): a
   case analysis over the phase's positions, each case evaluated.
2. *So the count does not change along the phase* (`startup_no_matrix`): one call of
   `count_isMatrix`, with the phase invariant at the positions in between.
3. *The positions in between are positions of the phase*: `first_exit` turns the phase's
   theorem ("the invariant holds or the thread left the phase earlier") into "the thread leaves
   the phase at a first position, and the invariant holds before it" (the second `example`).

Then two counts that are finer than the kind of the site. Per object: the startup phase has one
poll site, and the phase's closed-form event shape says that its poll is on the state barrier,
so the successful polls of a pipeline barrier (`Bar.loadEmpty st`) are not counted there. Per
barrier: the phase's `bar` sites are `bar.sync 0`, so no arrival at barrier 8 is counted there.
The last two examples prove `FiredOnly` for classes of the phase's own ledger.

`Inv P X g k s` is the startup invariant (the state before event `k` is at a position `pos` of
the phase: `RefAt P g pos s`, with `s.site = pos.site`), `Out` its exit condition, `Ev` the
closed form of the event of a position (`Startup/Shapes.lean`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- Step 1: no position of the startup phase is a matrix site. -/
theorem pos_not_matrix (pos : Pos) : pos.site.kind ∉ matrixKinds := by
  cases pos <;> simp [Pos.site, Site.kind, matrixKinds]

/-- Step 2, **"the startup phase makes no matrix event"**: a thread whose states before
position `k` all satisfy the startup invariant has made no matrix event before `k`. -/
theorem startup_no_matrix (hC : ∀ g < L.threads, (code L g).Sound)
    (hX : Consistent L kernel Assumptions.all mem0 X) {k : Nat} {s : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hin : ∀ i < k, ∀ si, Frame.stateAt (code L) X g i = some (some si) → Inv P X g i si) :
    ((X.tr g).take k).countP isMatrix = 0 :=
  count_zero_of_state hC hX firedOnly_isMatrix hσ (Nat.le_succ k) fun i d hik hd => by
    obtain ⟨pos, hr, -⟩ := hin i hik d hd
    left
    rw [hr.site]
    exact pos_not_matrix pos

/-- Step 3: at the first exit of the startup phase the thread has made no matrix event. The
phase's theorem is passed as it is (here `startup_inv_of_shfl`); under the precondition the
soundness hypothesis is `sounds hpre`. -/
example (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) (hS : ShflWarp X g) {k : Nat} {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P X g k s ∨ ∃ j ≤ k, ∃ s0, Frame.stateAt (code L) X g j = some (some s0) ∧
      Out P X g j s0 ∧ ((X.tr g).take j).countP isMatrix = 0 := by
  rcases first_exit (fun _ _ => startup_inv_of_shfl hpre (sounds hpre) hX hg hS) hk hσ with
    h | ⟨j, hj, s0, h0, hout, hbefore⟩
  · exact .inl h
  · exact .inr ⟨j, hj, s0, h0, hout, startup_no_matrix (sounds hpre) hX h0 hbefore⟩

/-- **"The startup phase makes no successful poll of `Bar.loadEmpty st`"**: the phase's one
poll site polls the state barrier (`hev`: the closed-form event shape of each visited position,
the first alternative of `Startup.event_at`), which is another mbarrier; no other position is a
poll site. The per-site condition of `count_zero_of_state` is given in its second form (the
event fired there is not of the class). -/
example (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) {k : Nat}
    {s : D} (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hev : ∀ i < k, ∀ si e, Frame.stateAt (code L) X g i = some (some si) →
      X.get (g, i) = some e → ∃ pos, RefAt P g pos si ∧ Ev P L g pos e) (st : Fin 3) :
    okPolls ((Bar.loadEmpty st).loc L (g / L.block)) ((X.tr g).take k) = 0 :=
  count_zero_of_state (sounds hpre) hX (firedOnly_okPoll _) hσ (Nat.le_succ k)
    fun i d hik hd => .inr fun e he => by
      obtain ⟨pos, hr, hshape⟩ := hev i hik d e hd he
      by_cases hp : pos = .wait
      · -- the poll site: its event is a poll of the state barrier
        subst hp
        obtain ⟨ok, rfl⟩ := hshape
        refine okPoll_other rfl fun h => ?_
        simp only [Bar.loc, Bar.off, hpre.sharedBase, Loc.mk.injEq, true_and] at h
        omega
      · -- every other position: not a poll site
        refine not_class_of_kind (sounds hpre) hX (firedOnly_okPoll _) he hd ?_
        rw [hr.site]
        cases pos <;> simp [Pos.site, Site.kind] at hp ⊢

/-- **"The startup phase makes no arrival at the named barrier"** (barrier 8, of the tile
loop): its three `bar` positions are `bar.sync 0` instructions, and the event of a `bar.sync 0`
is decided by the code alone (`isBarId_bar0`), without the phase's event shapes. -/
example (hC : ∀ g < L.threads, (code L g).Sound)
    (hX : Consistent L kernel Assumptions.all mem0 X) {k : Nat} {s : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hin : ∀ i < k, ∀ si, Frame.stateAt (code L) X g i = some (some si) → Inv P X g i si) :
    ((X.tr g).take k).countP (Execution.isBarId 8) = 0 :=
  count_zero_of_state hC hX (firedOnly_isBarId 8) hσ (Nat.le_succ k) fun i d hik hd => by
    obtain ⟨pos, hr, -⟩ := hin i hik d hd
    by_cases hb : ∃ j, pos = .bar j
    · obtain ⟨j, rfl⟩ := hb
      refine .inr fun e he => ?_
      have hpc : ∀ j : Fin 3, (Pos.bar j).site.pc ∈ bar0Pcs := by decide
      rw [isBarId_bar0 hC hX he hd (by rw [hr.site]; exact hpc j)]
      rfl
    · left
      rw [hr.site]
      cases pos <;> simp [Pos.site, Site.kind] at hb ⊢

/-- A class of a phase's own ledger (`isInit`: the mbarrier initializations, `Startup/Inv.lean`)
is fired only at `mbarInit` sites: `fired_only` with the name to unfold. -/
example : FiredOnly isInit [.mbarInit] := by
  fired_only [isInit]

/-- The same for a class that reads a field of the event (`isOkPoll`: the successful polls of
any mbarrier). -/
example : FiredOnly isOkPoll [.mbarWait] := by
  fired_only [isOkPoll]

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
