-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.RingRegion

/-! # A ring region and the rest of shared memory, no race

A ring region whose accesses are the ring's copies and the consumer's reads, ordered by uses
(`ConflictsOrdered.of_ring`), and the rest of memory ordered by other means, together give
`¬ Race` (`ConflictsOrdered.or`, `mono`, `no_race`): the shape of tml-fa4's K/V slots. -/

namespace PTX.Tests.RingRegion
open PTX AsyncCopy

example {L : Launch} {X : Execution} {R : Loc → Prop} (IsW IsRd : Ref → Prop) (use : Ref → Nat)
    (hacc : ∀ ref a w l, X.Intent ref a w → a.Covers l → R l →
      (IsW ref ∧ w = true) ∨ (IsRd ref ∧ w = false))
    (hsame : ∀ e f l, IsW e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e = use f → e = f)
    (hww : ∀ e f l, IsW e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e < use f → modelCausality L X l e f)
    (hwr : ∀ e f l, IsW e → IsRd f → CoversAt X e l → CoversAt X f l → R l →
      use e ≤ use f → modelCausality L X l e f)
    (hrw : ∀ e f l, IsRd e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e < use f → modelCausality L X l e f)
    (hrest : ConflictsOrdered L X fun l => ¬ R l) : ¬ Race L X :=
  ConflictsOrdered.no_race (((ConflictsOrdered.of_ring IsW IsRd use hacc hsame hww hwr
    hrw).or hrest).mono fun l _ => Classical.em (R l))

end PTX.Tests.RingRegion
