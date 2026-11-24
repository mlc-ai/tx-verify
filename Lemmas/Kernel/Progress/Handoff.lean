-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Poll
public import Lemmas.Kernel.Progress.Glued
public import Lemmas.Protocol.UnitsTrace
public import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-! # Progress at a declared hand-off: the blocker is an earlier producer

A proof tool, generic over the kernel. A thread waiting on a declared hand-off object `m`
(mbarrier, offset `δ`) whose poll fails is blocked by a producer that has not made its arrival of
the waited use; with time tables the descent needs that producer to be earlier than the waiter.
The hand-off is given a **schedule** `τ` (`Lag`): a waiter with `n` successful polls of `m` is
no earlier than `τ n`; a producer that has made `c` events counted towards the hand-off (`cnt`:
arrivals, no-increment arrive-ons or commits) is earlier than `τ (c + δ)`; a producer that exits
has made at least `U` of them, and a waiter has fewer than `U + δ` successful polls. These are
facts of the roles' time tables and ledgers, one per role (`Lag.prod_of_states`,
`Lag.wait_of_count` read them off the states). Then:

* a producer short of the waited use is a blocker (`Lag.blk`): it has not exited and is earlier;
  `LagShort` asks the lag only of such short producers (`LagShort.blk`, `Lag.short`);
* a waiter of a gated unit object (`MbarRing.Unit.Gate`: `RingDecl`/`UnitGate` hand-offs) whose
  poll fails has such a producer (`Gate.blocked`, `unitsOf_eq_arrivals`), so it is a
  `PollBlocked` thread (`Lag.pollBlocked_gate`) and steps in the descent
  (`Lag.steps_gate`, through `mbarAt_of` and `mbar_at_steps`); the same for a unit object whose
  producers' arrivals follow the waiter's polls (`Unit.Reach`, `Lag.pollBlocked_reach`);
* the blockers of the other object kinds (commit objects, no-increment objects, one-CTA TMA unit
  objects) are in `Lemmas/Kernel/Progress/HandoffBlockers.lean`.

A kernel's progress at such a wait is therefore its time table, the object's declaration, the
waiter's `PollsOn` (from its shape table, `Frame.pollsOn_of_shapeAt`) and the two per-role lag
facts; no blocker is found by hand. -/

namespace PTX.Sched
open PTX PTX.Flow MBarrier

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **The schedule of a hand-off on `m` against a time table**, for the producers `prod` and the
waiters `cons`, with the producers' events that count towards the hand-off `cnt` (`arrivesOn m`
for thread arrivals, `MbarRing.arriveOnTo m` for no-increment arrive-ons, `commitsTo m0` for
Tensor Core commits): `τ` is monotone; a waiter's machine state at its trace's end is no earlier
than `τ` of its successful polls; a producer is earlier than `τ` of its counted events plus `δ`;
a producer that exits has made at least `U` counted events; a waiter has fewer than `U + δ`
successful polls. `cons` may carry the waiter's position (its state at a poll of `m`). -/
structure Lag (M : Timed K A L) (X : Execution) (m : Loc) (δ : Nat) (prod cons : Nat → Prop)
    (τ : Nat → Nat) (U : Nat) (cnt : Event → Bool) : Prop where
  /-- The schedule is monotone. -/
  mono : ∀ a b, a ≤ b → τ a ≤ τ b
  /-- A waiter is no earlier than `τ` of its successful polls. -/
  wait : ∀ g d, cons g → Frame.stateAt M.code X g (X.tr g).length = some (some d) →
    τ (okPolls m (X.tr g)) ≤ M.time g d
  /-- A producer is earlier than `τ` of its counted events plus `δ`. -/
  early : ∀ y, prod y → y < L.threads → threadTime M X y < τ ((X.tr y).countP cnt + δ)
  /-- A producer that exits has made at least `U` counted events. -/
  exit : ∀ y k pc, prod y → X.get (y, k) = some ⟨pc, .exit⟩ → U ≤ (X.tr y).countP cnt
  /-- A waiter has fewer than `U + δ` successful polls. -/
  bound : ∀ g, cons g → okPolls m (X.tr g) < U + δ

/-- **The schedule of a hand-off with the lag of short producers only**: `Lag` whose `early`
fact is required only of a producer short of some waiter's waited use (its counted events plus
`δ` at most the waiter's successful polls). A producer that has made the waited use, such as a
lane that keeps issuing after its last counted event, need not be earlier than the schedule. -/
structure LagShort (M : Timed K A L) (X : Execution) (m : Loc) (δ : Nat) (prod cons : Nat → Prop)
    (τ : Nat → Nat) (U : Nat) (cnt : Event → Bool) : Prop where
  /-- The schedule is monotone. -/
  mono : ∀ a b, a ≤ b → τ a ≤ τ b
  /-- A waiter is no earlier than `τ` of its successful polls. -/
  wait : ∀ g d, cons g → Frame.stateAt M.code X g (X.tr g).length = some (some d) →
    τ (okPolls m (X.tr g)) ≤ M.time g d
  /-- A producer short of a waiter's waited use is earlier than `τ` of its counted events plus
  `δ`. -/
  early : ∀ y g, prod y → cons g → y < L.threads →
    (X.tr y).countP cnt + δ ≤ okPolls m (X.tr g) →
    threadTime M X y < τ ((X.tr y).countP cnt + δ)
  /-- A producer that exits has made at least `U` counted events. -/
  exit : ∀ y k pc, prod y → X.get (y, k) = some ⟨pc, .exit⟩ → U ≤ (X.tr y).countP cnt
  /-- A waiter has fewer than `U + δ` successful polls. -/
  bound : ∀ g, cons g → okPolls m (X.tr g) < U + δ

/-- A schedule whose every producer lags is one whose short producers lag. -/
theorem Lag.short {m : Loc} {δ : Nat} {prod cons : Nat → Prop} {τ : Nat → Nat} {U : Nat}
    {cnt : Event → Bool} (H : Lag M X m δ prod cons τ U cnt) :
    LagShort M X m δ prod cons τ U cnt :=
  ⟨H.mono, H.wait, fun y _ hy _ hyt _ => H.early y hy hyt, H.exit, H.bound⟩

/-- **A producer short of the waited use is a blocker** of a waiter at a poll of `m`: it has not
exited, and it is earlier than the waiter. -/
theorem LagShort.blk {m : Loc} {δ : Nat} {prod cons : Nat → Prop} {τ : Nat → Nat} {U : Nat}
    {cnt : Event → Bool} (H : LagShort M X m δ prod cons τ U cnt) (hX : Consistent L K A mem0 X)
    (hub : ¬ HasUb X) {g : Nat} (hg : g < L.threads) (hc : cons g) (hne : X.tr g ≠ [])
    {d : (M.code g).D} (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d))
    {y : Nat} (hy : prod y) (hyt : y < L.threads)
    (hcl : L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block))
    (hshort : (X.tr y).countP cnt + δ ≤ okPolls m (X.tr g)) : Blk M X g := by
  refine blk_of_lags hX hub hg hne hσ hyt hcl fun _ => ⟨fun k pc hx => ?_, ?_⟩
  · have h1 := H.exit y k pc hy hx
    have h2 := H.bound g hc
    omega
  · exact (H.early y g hy hc hyt hshort).trans_le ((H.mono _ _ hshort).trans (H.wait g d hc hσ))

namespace Lag

variable {m : Loc} {δ : Nat} {prod cons : Nat → Prop} {τ : Nat → Nat} {U : Nat}
  {cnt : Event → Bool}

/-- **A producer short of the waited use is a blocker** of a waiter at a poll of `m`: it has not
exited, and it is earlier than the waiter. -/
theorem blk (H : Lag M X m δ prod cons τ U cnt) (hX : Consistent L K A mem0 X)
    (hub : ¬ HasUb X) {g : Nat} (hg : g < L.threads) (hc : cons g) (hne : X.tr g ≠ [])
    {d : (M.code g).D} (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d))
    {y : Nat} (hy : prod y) (hyt : y < L.threads)
    (hcl : L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block))
    (hshort : (X.tr y).countP cnt + δ ≤ okPolls m (X.tr g)) : Blk M X g :=
  H.short.blk hX hub hg hc hne hσ hy hyt hcl hshort

/-- **A waiter of a gated unit object whose poll fails has an earlier blocker**, when no record of
the object faults: some producer has made exactly the final phase's arrivals, one use short. -/
theorem pollBlocked_gate (H : Lag M X m δ prod cons τ U (arrivesOn m))
    (hX : Consistent L K A mem0 X)
    (hub : ¬ HasUb X) {N : Nat} {pr : Fin N → Nat} {pair : Fin N → Nat → Prop}
    (G : MbarRing.Unit.Gate L K A X m N pr δ cons pair) (hpr : ∀ a, prod (pr a))
    (hff : ∀ r ∈ X.objects m, r.fault = none) {g : Nat} (hg : g < L.threads) (hc : cons g)
    (hp : PollsOn K A L X g m δ) (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before) :
    PollBlocked M X g := by
  refine pollBlocked_of hp hst fun hpar => ?_
  obtain ⟨hph, a, ha⟩ := G.blocked hX hc hst hpar
  rw [MbarRing.Unit.unitsOf_eq_arrivals hX hff] at ha
  have hcta := G.cta a g hc
  exact H.blk hX hub hg hc hne hσ (hpr a) hcta.1 (by rw [hcta.2.2])
    (by unfold arrivals at ha; omega)

/-- **A waiter of a unit object reached by its polls whose poll fails has an earlier blocker**
(`MbarRing.Unit.Reach`: the producers' arrivals follow the waiter's polls), when no record of the
object faults and the producers are in the waiter's cluster. -/
theorem pollBlocked_reach (H : Lag M X m δ prod cons τ U (arrivesOn m))
    (hX : Consistent L K A mem0 X)
    (hub : ¬ HasUb X) {N : Nat} {pr : Fin N → Nat} (O : MbarRing.Unit.Obj X m N pr δ)
    (hpr : ∀ a, prod (pr a) ∧ pr a < L.threads)
    (hff : ∀ r ∈ X.objects m, r.fault = none) {g : Nat}
    (hR : MbarRing.Unit.Reach L K A X m N pr δ g) (hg : g < L.threads) (hc : cons g)
    (hcl : ∀ a, L.clusterOfCta (pr a / L.block) = L.clusterOfCta (g / L.block))
    (hp : PollsOn K A L X g m δ) (hδ : δ ≤ okPolls m (X.tr g)) (hne : X.tr g ≠ [])
    {d : (M.code g).D} (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d))
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before) :
    PollBlocked M X g := by
  refine pollBlocked_of hp hst fun hpar => ?_
  obtain ⟨hph, a, ha⟩ := O.reach_short hX hR hff hst hδ hpar
  exact H.blk hX hub hg hc hne hσ (hpr a).1 (hpr a).2 (hcl a) (by unfold arrivals at ha; omega)

/-- **The descent step of a released waiter of a gated unit object** at time at least 2. -/
theorem steps_gate (H : Lag M X m δ prod cons τ U (arrivesOn m))
    (hA : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) (hmax : Maximal L K A mem0 X)
    {N : Nat} {pr : Fin N → Nat} {pair : Fin N → Nat → Prop}
    (G : MbarRing.Unit.Gate L K A X m N pr δ cons pair) (hpr : ∀ a, prod (pr a))
    (hff : ∀ r ∈ X.objects m, r.fault = none) {g : Nat} (hpe : Frame.Pending L X g)
    (hrel : Step.Released L X g) (hc : cons g) (hp : PollsOn K A L X g m δ) (hne : X.tr g ≠ [])
    {d : (M.code g).D} (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d))
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (h2 : 2 ≤ threadTime M X g) : Steps M mem0 X (.thread g) :=
  mbar_at_steps hA hub hmax hpe hrel hne
    (mbarAt_of (H.pollBlocked_gate hX hub G hpr hff hpe.1 hc hp hne hσ hst)) (by omega) h2

/-- **The producer's lag fact from its states**: when every state of a producer's machine is
earlier, by more than one, than `τ` of its counted events so far plus `δ`, the producer is earlier
than `τ` of its counted events plus `δ` (the one more covers a machine that stopped after its last
event). -/
theorem prod_of_states (hmono : ∀ a b, a ≤ b → τ a ≤ τ b) {y : Nat}
    (hs : ∀ k d, k ≤ (X.tr y).length → Frame.stateAt M.code X y k = some (some d) →
      M.time y d + 1 < τ (((X.tr y).take k).countP cnt + δ)) :
    threadTime M X y < τ ((X.tr y).countP cnt + δ) := by
  have h0 := hs 0 (M.code y).init (Nat.zero_le _) Frame.stateAt_zero
  have hmon : ∀ k, τ (((X.tr y).take k).countP cnt + δ) ≤ τ ((X.tr y).countP cnt + δ) := by
    intro k
    apply hmono
    have := (List.take_sublist k (X.tr y)).countP_le (p := cnt)
    omega
  unfold threadTime
  split
  · rename_i d hσ
    have := hs _ d le_rfl hσ
    rw [List.take_length] at this
    omega
  · have := hmon 0
    omega
  · split
    · rename_i d hσ
      have := hs _ d (by omega) hσ
      have := hmon ((X.tr y).length - 1)
      omega
    · have := hmon 0
      omega

/-- **The waiter's lag fact from its ledger**: a waiter whose state at its trace's end counts its
successful polls of `m` in a ledger class (`Sched.okPolls_count`) is no earlier than `τ` of them
when its time is no earlier than `τ` of that count. -/
theorem wait_of_count {C : (g : Nat) → Flow.Code K A L g} {κ : Type}
    {cls : Nat → κ → Event → Bool} {c : κ} {g : Nat} (hcls : cls g c = okPoll m)
    {dn : ((C g).counted (cls g)).D}
    (hσ : Frame.stateAt (fun g => (C g).counted (cls g)) X g (X.tr g).length = some (some dn))
    {t : Nat} (ht : τ (dn.2 c) ≤ t) : τ (okPolls m (X.tr g)) ≤ t := by
  have h := okPolls_count hcls hσ
  rw [List.take_length] at h
  rwa [h]

end Lag

end
end PTX.Sched
