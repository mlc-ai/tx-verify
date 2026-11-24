-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.HandoffBlockers

/-! # A waiter of a no-increment or commit object is an `MbarAt` thread

The blockers of `Lemmas/Kernel/Progress/HandoffBlockers.lean` composed with `mbarAt_of`: a
waiter at a poll of a no-increment object (tml-fa4's K/V full barriers: 64 loader lanes, `δ = 0`)
or of a commit object (one committing lane) polls with a blocker when not ready, so it is a
thread at an mbarrier wait whose blocker time is one below its own (the descent's step). A
one-CTA TMA unit object of two copies of 16384 bytes per use (tml-fa4's Q stages) has a blocker
of every waiter when its producer, short of an arrival or a copy, lags it. -/

namespace PTX.Tests.HandoffBlockers
open PTX PTX.Flow PTX.Sched MBarrier

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

example {m : Loc} {prod cons : Nat → Prop} {τ : Nat → Nat} {U : Nat}
    (H : Lag M X m 0 prod cons τ U (MbarRing.arriveOnTo m)) (hX : Consistent L K A mem0 X)
    (hub : ¬ HasUb X) (O : MbarRing.NoIncObject X m 64) {pr : Fin 64 → Nat}
    (hinj : Function.Injective pr) {g : Nat}
    (hpr : ∀ a, prod (pr a) ∧ pr a < L.threads ∧
      L.clusterOfCta (pr a / L.block) = L.clusterOfCta (g / L.block))
    (hff : ∀ r ∈ X.objects m, r.fault = none) (hg : g < L.threads) (hc : cons g)
    (hp : PollsOn K A L X g m 0) (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hle : before.phase ≤ okPolls m (X.tr g) + 1) :
    MbarAt M mem0 X g (threadTime M X g - 1) :=
  mbarAt_of (H.pollBlocked_noInc hX hub O hinj hpr hff hg hc hp hne hσ hst (by omega))

example {m m0 : Loc} {c : Nat} {prod cons : Nat → Prop} {τ : Nat → Nat} {U : Nat}
    (H : Lag M X m 0 prod cons τ U (commitsTo m0)) (hX : Consistent L K A mem0 X)
    (hub : ¬ HasUb X) (O : MbarRing.Notify.Obj X m c m0 0) {g : Nat}
    (hR : MbarRing.Notify.Reach L K A X m c m0 0 g) (hff : ∀ r ∈ X.objects m, r.fault = none)
    (htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec}, X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = m0 → ∃ rank, TcCommit.target sp rank = some m)
    (hcp : prod c ∧ c < L.threads ∧ L.clusterOfCta (c / L.block) = L.clusterOfCta (g / L.block))
    (hg : g < L.threads) (hc : cons g) (hp : PollsOn K A L X g m 0) (hne : X.tr g ≠ [])
    {d : (M.code g).D} (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d))
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before) :
    MbarAt M mem0 X g (threadTime M X g - 1) :=
  mbarAt_of (H.pollBlocked_notify hX hub O hR hff htgt hcp hg hc hp hne hσ hst (Nat.zero_le _))

example {m : Loc} {prod : Nat → Prop} (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X)
    (O : MbarRing.TmaUnitObject X m prod) (hff : ∀ r ∈ X.objects m, r.fault = none)
    (hbytes : expectedTxBytes (X.objects m) = 2 * 16384 * arrivalUnits (X.objects m))
    (hu : UniformCompletedTx (X.objects m) 16384) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hle : completedTxCount (X.objects m) ≤ 2 * (before.phase + 1)) {g : Nat}
    (hg : g < L.threads) (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) {y : Nat}
    (hyt : y < L.threads) (hcl : L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block))
    (hlag : Lags M X y (M.time g d)) : Blk M X g :=
  blk_tmaUnit hX hub O hff hbytes hu hst hle hg hne hσ hyt hcl fun _ => hlag

end PTX.Tests.HandoffBlockers
