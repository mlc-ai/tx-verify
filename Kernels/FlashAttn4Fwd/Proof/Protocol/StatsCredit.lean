-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Lemmas.Protocol.UnitHandoff
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The statistics credit barriers

Stage `st`'s credit barrier (`statsBar`, count 128) of a CTA is arrived on by the CTA's 128
correction threads and polled by its 128 softmax threads of the stage, whose first poll passes on
the fresh barrier. Its phase `q` holds each correction thread's credit arrival with `q` earlier
ones, and the softmax poll with `q + 1` earlier successful polls observes it: the unit handoff
with offset 1 (`StatsCredit`). That is the content of the barrier's phases under the kernel's
credit chain (a correction thread's credit arrival `q + 1` follows its `bar.sync` of ordinal
`q + 1`, which needs the softmax arrival of ordinal `q + 1`, which follows that softmax thread's
poll observing phase `q`). Its proof, from the role counts and the barrier's history, is
`StatsCreditGate.statsCredit`; the statistics protocol states its lemmas from `StatsCredit`.

The roles are named by thread (`corrIn`, `softIn`), and the CTA's lane-0 correction thread of
warp `8 + k` (`corrLead`) is a producer of every credit barrier of the CTA. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

namespace Stats

/-- A correction thread of CTA `c`. -/
def corrIn (L : Launch) (c g : Nat) : Prop :=
  g < L.threads ∧ ctaOf L g = c ∧ 8 ≤ warpOf L g ∧ warpOf L g < 12

/-- A softmax thread of stage `st` of CTA `c`. -/
def softIn (L : Launch) (c st g : Nat) : Prop :=
  g < L.threads ∧ ctaOf L g = c ∧ warpOf L g < 8 ∧ warpOf L g / 4 = st

/-- **The statistics credit handoff** of every stage of every CTA. -/
def StatsCredit (L : Launch) (X : Execution) : Prop :=
  ∀ c st, st < 2 →
    MbarRing.UnitHandoff L X (statsBar L c st) (corrIn L c) (softIn L c st) 1

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- Lane 0 of correction warp `8 + k` of CTA `c`. -/
def corrLead (L : Launch) (c k : Nat) : Nat := c * L.block + 32 * (8 + k)

theorem corrLead_in (hpre : Pre P L mem0) {c k : Nat} (hc : c < L.grid) (hk : k < 4) :
    corrIn L c (corrLead L c k) ∧ warpOf L (corrLead L c k) = 8 + k := by
  have hb := hpre.block
  have hlt : corrLead L c k < L.threads := by
    unfold corrLead Launch.threads
    rw [hb] at *
    nlinarith
  have hmod : corrLead L c k % L.block = 32 * (8 + k) := by
    unfold corrLead
    rw [hb]
    omega
  have hdiv : ctaOf L (corrLead L c k) = c := by
    unfold ctaOf corrLead
    rw [hb]
    omega
  have hw : warpOf L (corrLead L c k) = 8 + k := by
    unfold warpOf
    rw [hmod]
    omega
  exact ⟨⟨hlt, hdiv, by omega, by omega⟩, hw⟩

end Stats

end
end PTX.Kernels.FlashAttn4Fwd.Proof
