-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Handoff
public import Lemmas.Protocol.NoIncBlocker
public import Lemmas.Protocol.NotifyBlocker
public import Lemmas.Protocol.TmaUnitBlock

@[expose] public section

/-! # Progress at a declared hand-off: the blockers of the other object kinds

A proof tool, generic over the kernel, beside `Lemmas/Kernel/Progress/Handoff.lean` (unit objects).
A waiter at a poll of a hand-off object whose final phase has the poll's parity has a blocker
(`Blk`): an open asynchronous obligation of the object's kind, or a producer short of the waited
use, which the hand-off's schedule (`Lag`, counting the producers' events of the object's kind)
makes earlier than the waiter.

* **No-increment objects** (`MbarRing.NoIncObject`, completed by `cp.async.mbarrier.arrive.noinc`
  arrive-ons, `cnt := MbarRing.arriveOnTo m`): with no open arrive-on obligation the arrive-ons
  are recorded (`MbarRing.arr_recorded`), and some producer has no more recorded arrive-ons than
  the phase (`NoIncObject.blocked`). The waiter states the phase bound
  `phase + δ ≤ okPolls + 1` (`Lag.blk_noInc`, `Lag.pollBlocked_noInc`).
* **Commit objects** (`MbarRing.Notify.Obj`, completed by the notifications of one lane's Tensor
  Core commits, `cnt := commitsTo m0`): with the reuse paths (`Notify.Reach`) the phase is at most
  the waiter's polls minus `δ`, and the lane made no more commits than the phase or a commit's
  notification is undelivered (`Notify.Obj.blocker`; `Lag.blk_notify`, `Lag.pollBlocked_notify`).
* **One-CTA TMA unit objects** (`MbarRing.TmaUnitObject`, one arrival with expected bytes and the
  completions of `n` copies of `B` bytes per use): the final phase awaits its arrival or a copy
  (`TmaUnitObject.short`); with no open tensor-copy obligation every copy is notified, so a
  producer is short of arrivals or of copies (`blk_tmaUnit`, the lag of a short producer given by
  the kernel; `Lag.blk_tmaUnit` with the arrival schedule). -/

namespace PTX.Sched
open PTX PTX.Flow MBarrier

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

namespace LagShort

variable {m : Loc} {δ : Nat} {prod cons : Nat → Prop} {τ : Nat → Nat} {U : Nat}

/-! ### No-increment objects -/

/-- **A waiter of a no-increment object whose final phase has its poll's parity has a blocker**:
an open arrive-on obligation, or a producer with no more arrive-ons than the phase, which is short
of the waited use. -/
theorem blk_noInc (H : LagShort M X m δ prod cons τ U (MbarRing.arriveOnTo m))
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) {N : Nat} (O : MbarRing.NoIncObject X m N)
    {pr : Fin N → Nat} (hinj : Function.Injective pr) {g : Nat}
    (hpr : ∀ a, prod (pr a) ∧ pr a < L.threads ∧
      L.clusterOfCta (pr a / L.block) = L.clusterOfCta (g / L.block))
    (hff : ∀ r ∈ X.objects m, r.fault = none) (hg : g < L.threads) (hc : cons g)
    (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hle : before.phase + δ ≤ okPolls m (X.tr g) + 1)
    (hpar : before.phase % 2 = (okPolls m (X.tr g) + δ) % 2) : Blk M X g := by
  by_cases hob : Descent.Obl L X .arriveOn
  · exact .inl ⟨.arriveOn, by simp, hob⟩
  obtain ⟨a, ha⟩ := O.blocked hX hinj hst
  have hrec := MbarRing.arr_recorded hX hob hff (pr a)
  exact H.blk hX hub hg hc hne hσ (hpr a).1 (hpr a).2.1 (hpr a).2.2 (by omega)

/-- **A waiter of a no-increment object polls with a blocker when not ready.** -/
theorem pollBlocked_noInc (H : LagShort M X m δ prod cons τ U (MbarRing.arriveOnTo m))
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) {N : Nat} (O : MbarRing.NoIncObject X m N)
    {pr : Fin N → Nat} (hinj : Function.Injective pr) {g : Nat}
    (hpr : ∀ a, prod (pr a) ∧ pr a < L.threads ∧
      L.clusterOfCta (pr a / L.block) = L.clusterOfCta (g / L.block))
    (hff : ∀ r ∈ X.objects m, r.fault = none) (hg : g < L.threads) (hc : cons g)
    (hp : PollsOn K A L X g m δ) (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hle : before.phase + δ ≤ okPolls m (X.tr g) + 1) : PollBlocked M X g :=
  pollBlocked_of hp hst fun hpar => H.blk_noInc hX hub O hinj hpr hff hg hc hne hσ hst hle hpar

end LagShort

namespace Lag

variable {m : Loc} {δ : Nat} {prod cons : Nat → Prop} {τ : Nat → Nat} {U : Nat}

/-! ### No-increment objects -/

/-- **A waiter of a no-increment object whose final phase has its poll's parity has a blocker**
(`LagShort.blk_noInc` for a schedule of every producer). -/
theorem blk_noInc (H : Lag M X m δ prod cons τ U (MbarRing.arriveOnTo m))
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) {N : Nat} (O : MbarRing.NoIncObject X m N)
    {pr : Fin N → Nat} (hinj : Function.Injective pr) {g : Nat}
    (hpr : ∀ a, prod (pr a) ∧ pr a < L.threads ∧
      L.clusterOfCta (pr a / L.block) = L.clusterOfCta (g / L.block))
    (hff : ∀ r ∈ X.objects m, r.fault = none) (hg : g < L.threads) (hc : cons g)
    (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hle : before.phase + δ ≤ okPolls m (X.tr g) + 1)
    (hpar : before.phase % 2 = (okPolls m (X.tr g) + δ) % 2) : Blk M X g :=
  H.short.blk_noInc hX hub O hinj hpr hff hg hc hne hσ hst hle hpar

/-- **A waiter of a no-increment object polls with a blocker when not ready.** -/
theorem pollBlocked_noInc (H : Lag M X m δ prod cons τ U (MbarRing.arriveOnTo m))
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) {N : Nat} (O : MbarRing.NoIncObject X m N)
    {pr : Fin N → Nat} (hinj : Function.Injective pr) {g : Nat}
    (hpr : ∀ a, prod (pr a) ∧ pr a < L.threads ∧
      L.clusterOfCta (pr a / L.block) = L.clusterOfCta (g / L.block))
    (hff : ∀ r ∈ X.objects m, r.fault = none) (hg : g < L.threads) (hc : cons g)
    (hp : PollsOn K A L X g m δ) (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hle : before.phase + δ ≤ okPolls m (X.tr g) + 1) : PollBlocked M X g :=
  H.short.pollBlocked_noInc hX hub O hinj hpr hff hg hc hp hne hσ hst hle

/-! ### Commit objects -/

/-- **A waiter of a commit object whose final phase has its poll's parity has a blocker**: an
undelivered commit notification, or the committing lane, short of the waited use. -/
theorem blk_notify {c : Nat} {m0 : Loc} (H : Lag M X m δ prod cons τ U (commitsTo m0))
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) (O : MbarRing.Notify.Obj X m c m0 δ)
    {g : Nat} (hR : MbarRing.Notify.Reach L K A X m c m0 δ g)
    (hff : ∀ r ∈ X.objects m, r.fault = none)
    (htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec}, X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = m0 → ∃ rank, TcCommit.target sp rank = some m)
    (hcp : prod c ∧ c < L.threads ∧ L.clusterOfCta (c / L.block) = L.clusterOfCta (g / L.block))
    (hg : g < L.threads) (hc : cons g) (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hδ : δ ≤ okPolls m (X.tr g))
    (hpar : before.phase % 2 = (okPolls m (X.tr g) + δ) % 2) : Blk M X g := by
  obtain ⟨hle, hb⟩ := O.blocker hX hR hff htgt hst hpar hδ
  rcases hb with hb | hb
  · exact H.blk hX hub hg hc hne hσ hcp.1 hcp.2.1 hcp.2.2 (by omega)
  · exact .inl ⟨.commit, by simp, hb⟩

/-- **A waiter of a commit object polls with a blocker when not ready.** -/
theorem pollBlocked_notify {c : Nat} {m0 : Loc} (H : Lag M X m δ prod cons τ U (commitsTo m0))
    (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) (O : MbarRing.Notify.Obj X m c m0 δ)
    {g : Nat} (hR : MbarRing.Notify.Reach L K A X m c m0 δ g)
    (hff : ∀ r ∈ X.objects m, r.fault = none)
    (htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec}, X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = m0 → ∃ rank, TcCommit.target sp rank = some m)
    (hcp : prod c ∧ c < L.threads ∧ L.clusterOfCta (c / L.block) = L.clusterOfCta (g / L.block))
    (hg : g < L.threads) (hc : cons g) (hp : PollsOn K A L X g m δ) (hne : X.tr g ≠ [])
    {d : (M.code g).D} (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d))
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hδ : δ ≤ okPolls m (X.tr g)) : PollBlocked M X g :=
  pollBlocked_of hp hst fun hpar =>
    H.blk_notify hX hub O hR hff htgt hcp hg hc hne hσ hst hδ hpar

end Lag

/-! ### One-CTA TMA unit objects -/

variable {m : Loc}

/-- **A one-CTA TMA unit object has a blocker of every waiter**: an open tensor-copy obligation,
or a producer `y` short of the final phase's arrival or of its copies, when such a producer lags
the waiter (the kernel's time table). Each arrival expects `n` copies of `B` bytes, and the
completions do not run ahead of the phase. -/
theorem blk_tmaUnit {prod : Nat → Prop} (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X)
    (O : MbarRing.TmaUnitObject X m prod) (hff : ∀ r ∈ X.objects m, r.fault = none) {n B : Nat}
    (hbytes : expectedTxBytes (X.objects m) = n * B * arrivalUnits (X.objects m))
    (hu : UniformCompletedTx (X.objects m) B) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hle : completedTxCount (X.objects m) ≤ n * (before.phase + 1)) {g : Nat}
    (hg : g < L.threads) (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {y : Nat}
    (hyt : y < L.threads) (hcl : L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block))
    (hlag : arrivals m (X.tr y) ≤ before.phase ∨
      (X.tr y).countP (issuesTo m) < n * (before.phase + 1) → Lags M X y (M.time g d)) :
    Blk M X g := by
  by_cases hob : Descent.Obl L X .tensor
  · exact .inl ⟨.tensor, by simp, hob⟩
  refine blk_of_lags hX hub hg hne hσ hyt hcl (hlag ?_)
  rcases O.short hX hst hbytes hu hle with h | ⟨-, h⟩
  · exact .inl ((O.arrivals_le_units hX hff y).trans h.le)
  · exact .inr ((O.issues_le_completions hX hff y
      (MbarRing.TmaUnitObject.notified_rec hX hob)).trans_lt h)

/-- **A waiter of a one-CTA TMA unit object whose final phase has its poll's parity has a
blocker**, with the arrival schedule `Lag` of its producer `y` and the lag of a producer short of
the phase's copies. The waiter states the phase bound `phase + δ ≤ okPolls + 1`. -/
theorem Lag.blk_tmaUnit {prod : Nat → Prop} {δ : Nat} {pd cons : Nat → Prop} {τ : Nat → Nat}
    {U : Nat} (H : Lag M X m δ pd cons τ U (arrivesOn m)) (hX : Consistent L K A mem0 X)
    (hub : ¬ HasUb X) (O : MbarRing.TmaUnitObject X m prod)
    (hff : ∀ r ∈ X.objects m, r.fault = none) {n B : Nat}
    (hbytes : expectedTxBytes (X.objects m) = n * B * arrivalUnits (X.objects m))
    (hu : UniformCompletedTx (X.objects m) B) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hle : completedTxCount (X.objects m) ≤ n * (before.phase + 1)) {g : Nat}
    (hg : g < L.threads) (hc : cons g) (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {y : Nat} (hy : pd y)
    (hyt : y < L.threads) (hcl : L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block))
    (hph : before.phase + δ ≤ okPolls m (X.tr g) + 1)
    (hpar : before.phase % 2 = (okPolls m (X.tr g) + δ) % 2)
    (hcopy : (X.tr y).countP (issuesTo m) < n * (before.phase + 1) →
      Lags M X y (M.time g d)) : Blk M X g := by
  refine Sched.blk_tmaUnit hX hub O hff hbytes hu hst hle hg hne hσ hyt hcl fun h => ?_
  rcases h with h | h
  · intro _
    refine ⟨fun k pc hx => ?_, ?_⟩
    · have h1 := H.exit y k pc hy hx
      have h2 := H.bound g hc
      unfold arrivals at h
      omega
    · have := H.early y hy hyt
      have h3 := H.mono _ _ (show (X.tr y).countP (arrivesOn m) + δ ≤ okPolls m (X.tr g) by
        unfold arrivals at h; omega)
      have h4 := H.wait g d hc hσ
      omega
  · exact hcopy h

end
end PTX.Sched
