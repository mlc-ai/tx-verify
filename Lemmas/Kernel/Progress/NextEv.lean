-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Handoff
public import Lemmas.Quiet.Progress.WaitSite
public import Lemmas.Quiet.Progress.WaitSiteU

@[expose] public section

/-! # A waiting lane described by its next event

The upper layers of a proof describe a waiting lane without naming its role's machine state:

* `NextEv L K A mem0 X g e`: a consistent execution extends lane `g`'s trace by the event `e`
  (what `Sched.wait_site_steps` hands to the blocker of a failed poll, and tml-fa4's `PollExt`);
* `timeAt M X g k`: the time of lane `g` after its first `k` events, so that
  `threadTime M X g = timeAt M X g (X.tr g).length` and an extension that keeps the trace as a
  prefix has the same time there (`timeAt_ext`);
* `NextEv.fired_site`: the role's private bridge from a next event to the instruction of its
  state, by which a role exports facts about a lane at a next event (its time, its counts);
* `WaitBlk M X g m q`: a channel's blocker shape: `m` has a state, and when its phase has the
  parity `q` the lane has a blocker;
* `LagN`: `Sched.Lag` whose waiter fact is `τ (okPolls m (X.tr g)) ≤ threadTime M X g` instead
  of a statement about the waiter's machine state, with its consumers (`LagN.blk`,
  `LagN.blk_gate`, `LagN.pollBlocked_gate`, `LagN.steps_gateQ`) and `Lag.toN`;
* `wait_site_stepsN` / `wait_site_stepsUN`: the wait-site step whose blocker premise is stated with
  `NextEv`. -/

namespace PTX.Sched
open PTX PTX.Flow MBarrier

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X Y : Execution} {g : Nat}

/-- **The next event of lane `g`**: a consistent execution extends `g`'s trace by `e`. -/
def NextEv (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0) (X : Execution)
    (g : Nat) (e : Event) : Prop :=
  ∃ Y, Consistent L K A mem0 Y ∧ (Y.tr g).take (X.tr g).length = X.tr g ∧
    Y.get (g, (X.tr g).length) = some e

section
variable (M : Timed K A L)

/-- **The time of lane `g` after its first `k` events** (`threadTime` at `k`). -/
def timeAt (X : Execution) (g k : Nat) : Nat :=
  match Frame.stateAt M.code X g k with
  | some (some d) => M.time g d
  | some none => 0
  | none =>
    match Frame.stateAt M.code X g (k - 1) with
    | some (some d) => M.time g d + 1
    | _ => 0

end

/-- The time of a lane is its time after all its events. -/
theorem threadTime_eq_timeAt : threadTime M X g = timeAt M X g (X.tr g).length := by
  unfold threadTime timeAt
  rfl

/-- The state after `k` events depends only on the first `k` events. -/
theorem stateAt_congr {C : (g : Nat) → Flow.Code K A L g} {k : Nat}
    (h : (Y.tr g).take k = (X.tr g).take k) : Frame.stateAt C Y g k = Frame.stateAt C X g k := by
  unfold Frame.stateAt
  rw [h]

/-- The time after `k` events depends only on the first `k` events. -/
theorem timeAt_congr {k : Nat} (h : (Y.tr g).take k = (X.tr g).take k) :
    timeAt M Y g k = timeAt M X g k := by
  have h' : (Y.tr g).take (k - 1) = (X.tr g).take (k - 1) := by
    have := congrArg (List.take (k - 1)) h
    simpa only [List.take_take, Nat.min_eq_left (Nat.sub_le k 1)] using this
  unfold timeAt
  rw [stateAt_congr h, stateAt_congr h']

/-- **An extension that keeps a lane's trace as a prefix has the lane's time at its end.** -/
theorem timeAt_ext (h : (Y.tr g).take (X.tr g).length = X.tr g) :
    timeAt M Y g (X.tr g).length = threadTime M X g := by
  rw [threadTime_eq_timeAt]
  exact timeAt_congr (by simp [h])

/-- A lane with a next event is launched. -/
theorem NextEv.lt (h : NextEv L K A mem0 X g e) : g < L.threads := by
  obtain ⟨Y, hY, -, he⟩ := h
  exact Frame.lt_of_get hY he

/-- **The time of a lane at its next event**: the extension has the lane's time there. -/
theorem NextEv.time (h : NextEv L K A mem0 X g e) :
    ∃ Y, Consistent L K A mem0 Y ∧ Y.get (g, (X.tr g).length) = some e ∧
      timeAt M Y g (X.tr g).length = threadTime M X g := by
  obtain ⟨Y, hY, hp, he⟩ := h
  exact ⟨Y, hY, he, timeAt_ext hp⟩

/-- **A next event is fired from the lane's state at its trace's end**: it is an event of the
instruction at the state's site. A role uses it to state facts about a lane at a next event. -/
theorem NextEv.fired_site {C : (g : Nat) → Flow.Code K A L g}
    (hC : ∀ g < L.threads, (C g).Sound) (h : NextEv L K A mem0 X g e) {d : (C g).D}
    (hσ : Frame.stateAt C X g (X.tr g).length = some (some d)) :
    ∃ t ins o, (C g).AtD d t ∧ (C g).inv d ∧ K.code[(C g).pc d]? = some ins ∧
      Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o := by
  obtain ⟨Y, hY, hp, he⟩ := h
  have hσY : Frame.stateAt C Y g (X.tr g).length = some (some d) := by
    rw [stateAt_congr (X := X) (by simp [hp])]
    exact hσ
  exact Frame.fired_site hC hY he hσY

section
variable (M : Timed K A L)

/-- **A channel's blocker shape at a wait on `m` with parity `q`**: `m` has a state, and when its
phase has the poll's parity the lane has a blocker. -/
def WaitBlk (X : Execution) (g : Nat) (m : Loc) (q : Nat) : Prop :=
  ∃ before, stateBefore (X.objects m) (X.objects m).length = some before ∧
    (before.phase % 2 = q % 2 → Blk M X g)

end

/-- **A lagging producer of the waiter's cluster is a blocker**, against the waiter's time. -/
theorem blk_of_lagsN (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) {y : Nat} (hy : y < L.threads)
    (hc : L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block))
    (hl : Lags M X y (threadTime M X g)) : Blk M X g :=
  .inr ⟨y, pending_of_noExit hX hg hne hy hc (hl hub).1, (hl hub).2⟩

/-- **The schedule of a hand-off on `m`, with the waiter's fact on its time** (`Lag` without the
waiter's machine state): `τ` is monotone; a waiter is no earlier than `τ` of its successful polls;
a producer is earlier than `τ` of its counted events plus `δ`; a producer that exits has made at
least `U` counted events; a waiter has fewer than `U + δ` successful polls. A channel states
`cons` with `NextEv` (a lane whose next event polls `m`). -/
structure LagN (M : Timed K A L) (X : Execution) (m : Loc) (δ : Nat) (prod cons : Nat → Prop)
    (τ : Nat → Nat) (U : Nat) (cnt : Event → Bool) : Prop where
  /-- The schedule is monotone. -/
  mono : ∀ a b, a ≤ b → τ a ≤ τ b
  /-- A waiter is no earlier than `τ` of its successful polls. -/
  wait : ∀ g, cons g → τ (okPolls m (X.tr g)) ≤ threadTime M X g
  /-- A producer is earlier than `τ` of its counted events plus `δ`. -/
  early : ∀ y, prod y → y < L.threads → threadTime M X y < τ ((X.tr y).countP cnt + δ)
  /-- A producer that exits has made at least `U` counted events. -/
  exit : ∀ y k pc, prod y → X.get (y, k) = some ⟨pc, .exit⟩ → U ≤ (X.tr y).countP cnt
  /-- A waiter has fewer than `U + δ` successful polls. -/
  bound : ∀ g, cons g → okPolls m (X.tr g) < U + δ

namespace LagN

variable {m : Loc} {δ : Nat} {prod cons : Nat → Prop} {τ : Nat → Nat} {U : Nat}
  {cnt : Event → Bool}

/-- A schedule stated with the waiters' states, whose waiters have states, is one stated with
their times. -/
theorem _root_.PTX.Sched.Lag.toN (H : Lag M X m δ prod cons τ U cnt)
    (hs : ∀ g, cons g → ∃ d, Frame.stateAt M.code X g (X.tr g).length = some (some d)) :
    LagN M X m δ prod cons τ U cnt := by
  refine ⟨H.mono, fun g hc => ?_, H.early, H.exit, H.bound⟩
  obtain ⟨d, hσ⟩ := hs g hc
  rw [threadTime_of hσ]
  exact H.wait g d hc hσ

/-- **A producer short of the waited use is a blocker** of a waiter of `m`. -/
theorem blk (H : LagN M X m δ prod cons τ U cnt) (hX : Consistent L K A mem0 X)
    (hub : ¬ HasUb X) (hg : g < L.threads) (hc : cons g) (hne : X.tr g ≠ [])
    {y : Nat} (hy : prod y) (hyt : y < L.threads)
    (hcl : L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block))
    (hshort : (X.tr y).countP cnt + δ ≤ okPolls m (X.tr g)) : Blk M X g := by
  refine blk_of_lagsN hX hub hg hne hyt hcl fun _ => ⟨fun k pc hx => ?_, ?_⟩
  · have h1 := H.exit y k pc hy hx
    have h2 := H.bound g hc
    omega
  · exact (H.early y hy hyt).trans_le ((H.mono _ _ hshort).trans (H.wait g hc))

/-- **A waiter of a gated unit object is blocked when the object's phase has the parity of its
successful polls plus `δ`**, when no record of the object faults. -/
theorem blk_gate (H : LagN M X m δ prod cons τ U (arrivesOn m))
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) {N : Nat} {pr : Fin N → Nat}
    {pair : Fin N → Nat → Prop} (G : MbarRing.Unit.Gate L K A X m N pr δ cons pair)
    (hpr : ∀ a, prod (pr a)) (hff : ∀ r ∈ X.objects m, r.fault = none) (hg : g < L.threads)
    (hc : cons g) (hne : X.tr g ≠ []) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hpar : before.phase % 2 = (okPolls m (X.tr g) + δ) % 2) : Blk M X g := by
  obtain ⟨hph, a, ha⟩ := G.blocked hX hc hst hpar
  rw [MbarRing.Unit.unitsOf_eq_arrivals hX hff] at ha
  have hcta := G.cta a g hc
  exact H.blk hX hub hg hc hne (hpr a) hcta.1 (by rw [hcta.2.2])
    (by unfold arrivals at ha; omega)

/-- **A waiter of a gated unit object polls with a blocker when not ready.** -/
theorem pollBlocked_gate (H : LagN M X m δ prod cons τ U (arrivesOn m))
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) {N : Nat} {pr : Fin N → Nat}
    {pair : Fin N → Nat → Prop} (G : MbarRing.Unit.Gate L K A X m N pr δ cons pair)
    (hpr : ∀ a, prod (pr a)) (hff : ∀ r ∈ X.objects m, r.fault = none) (hg : g < L.threads)
    (hc : cons g) (hp : PollsOn K A L X g m δ) (hne : X.tr g ≠ []) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before) :
    PollBlocked M X g :=
  pollBlocked_of hp hst fun hpar => H.blk_gate hX hub G hpr hff hg hc hne hst hpar

/-- **The descent step of a released waiter of a gated unit object** at time at least 2. -/
theorem steps_gateQ (H : LagN M X m δ prod cons τ U (arrivesOn m))
    (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) (hmax : Maximal L K A mem0 X)
    {N : Nat} {pr : Fin N → Nat} {pair : Fin N → Nat → Prop}
    (G : MbarRing.Unit.Gate L K A X m N pr δ cons pair) (hpr : ∀ a, prod (pr a))
    (hff : ∀ r ∈ X.objects m, r.fault = none) (hpe : Frame.Pending L X g)
    (hrel : Step.Released L X g) (hc : cons g) (hp : PollsOn K A L X g m δ) (hne : X.tr g ≠ [])
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (h2 : 2 ≤ threadTime M X g) : Steps M mem0 X (.thread g) :=
  mbar_at_stepsQ hA hub hmax hpe hrel hne
    (mbarAt_of (H.pollBlocked_gate hX hub G hpr hff hpe.1 hc hp hne hst)) (by omega) h2

end LagN

/-- **A released lane at a wait steps** (`wait_site_stepsQ`), when every failed poll its state
fires, given as the lane's next event, is blocked as a channel states it (`WaitBlk`). -/
theorem wait_site_stepsN (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).Sound)
    (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → waitOp ins.op = true)
    {P : Event → Prop}
    (hS : ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState}, (M.code g).AtD d t →
      (M.code g).inv d → K.code[(M.code g).pc d]? = some ins →
      Fires ((M.code g).pc d) (eventTmpl A L g t ins.op) e o → P e)
    (hfin : ∀ l q ok sc, P ⟨(M.code g).pc d, .wait l q ok true sc⟩ →
      ∃ before, stateBefore (X.objects l) (X.objects l).length = some before)
    (hblk : ∀ l q sc, P ⟨(M.code g).pc d, .wait l q false true sc⟩ →
      NextEv L K A mem0 X g ⟨(M.code g).pc d, .wait l q false true sc⟩ → WaitBlk M X g l q)
    (h2 : 2 ≤ M.time g d) : Steps M mem0 X (.thread g) := by
  refine wait_site_stepsQ hA hmax hub hC hp hσ hne hrel hk hS hfin
    (fun l q sc before hP hst hY hpar => ?_) h2
  obtain ⟨before', hst', hb⟩ := hblk l q sc hP hY
  rw [hst] at hst'
  cases hst'
  exact hb hpar

/-- **A released lane of an unrolled machine at a wait steps** (`wait_site_stepsUQ`), with the
blocker premise stated with `NextEv` and `WaitBlk`. -/
theorem wait_site_stepsUN (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).SoundU)
    (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → waitOp ins.op = true)
    {P : Event → Prop}
    (hS : ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState}, (M.code g).AtD d t →
      (M.code g).inv d → K.code[(M.code g).pc d]? = some ins →
      Fires ((M.code g).pc d) (eventTmpl A L g t ins.op) e o → (∀ f, e.kind ≠ .ub f) → P e)
    (hfin : ∀ l q ok sc, P ⟨(M.code g).pc d, .wait l q ok true sc⟩ →
      ∃ before, stateBefore (X.objects l) (X.objects l).length = some before)
    (hblk : ∀ l q sc, P ⟨(M.code g).pc d, .wait l q false true sc⟩ →
      NextEv L K A mem0 X g ⟨(M.code g).pc d, .wait l q false true sc⟩ → WaitBlk M X g l q)
    (h2 : 2 ≤ M.time g d) : Steps M mem0 X (.thread g) := by
  refine wait_site_stepsUQ hA hmax hub hC hp hσ hne hrel hk hS hfin
    (fun l q sc before hP hst hY hpar => ?_) h2
  obtain ⟨before', hst', hb⟩ := hblk l q sc hP hY
  rw [hst] at hst'
  cases hst'
  exact hb hpar

end
end PTX.Sched
