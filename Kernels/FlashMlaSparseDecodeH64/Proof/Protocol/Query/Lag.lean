-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Lemmas.Kernel.Progress.NextEv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Time

@[expose] public section

/-! # The query channels' progress rows

The waiting sites of the two query objects, described by their next events (`Sched.NextEv`) and
the glued time table `timed P L` only, with no machine state:

* **`qUtccp`** (waits at 1983, 2205, 2644, blocked on the MMA lane's commit at 1982): the
  schedule `Sched.LagN` with the constant slot `qUtccpSlot` of the commit (`qUtccp_lag`), producer
  the MMA lane while it has not committed (guarded by `MmaPast`: an event of the MMA code from the
  arrival at 1929 on; a CTA that exits early has no MMA lane), consumers the waiters at their first
  poll, counted events the lane's commits to `qUtccp`, `U = 1`, `δ = 0`. `LagN.blk` then makes
  the lagging MMA lane a blocker of every waiter (`qUtccp_blk`).
* **`qTma`** (wait at 1931, blocked on the eight tensor loads: environment steps): the lane is its
  own producer, so no time fact is needed, only its prefix at the wait (`qTma_pre`: its arrival
  and its eight loads are made, `mma_tmaPre`); `qTma_blk` in `Protocol/Query/LagTma.lean`.

The MMA lane's facts are its exports (`mma_tmaPre`, `mma_slot_wait`, `mma_slot_early`,
`mma_commitExit`); a waiter's first poll is the rows' (`qUtccp_use`, `qUtccp_first`).
**Inputs (`QueryTime`):** the TMA lane's (A) and the dequant lanes' (D) waits are at the slot. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Lane `g` of CTA `c` waits next on `qUtccp` at one of its waiter sites. -/
def QWaitNext (L : Launch) (m : Mem0) (X : Execution) (c g : Nat) : Prop :=
  g < L.threads ∧ g / L.block = c ∧ ∃ pc p ok acq sc, QWaiter L g pc ∧
    Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait (mbarLoc L c .qUtccp) p ok acq sc⟩

/-- **The waiters' slot facts** (inputs of lanes A and D): the TMA lane at its `qUtccp` wait
(2205) and a dequant lane at its (2644) are no earlier than the commit's slot. -/
structure QueryTime (P : Params) (L : Launch) (m : Mem0) (X : Execution) : Prop where
  /-- (lane A) The TMA lane at its wait on `qUtccp` is no earlier than the slot. -/
  tmaSlot : ∀ {g c p : Nat} {ok acq : Bool} {sc : MbarScope}, MbarRow.TmaAt L g 2205 →
    Sched.NextEv L kernel Assumptions.all m X g ⟨2205, .wait (mbarLoc L c .qUtccp) p ok acq sc⟩ →
    qUtccpSlot ≤ Sched.threadTime (timed P L) X g
  /-- (lane D) A dequant lane at its wait on `qUtccp` is no earlier than the slot. -/
  deqSlot : ∀ {g c p : Nat} {ok acq : Bool} {sc : MbarScope}, MbarRow.DequantAt L g 2644 →
    Sched.NextEv L kernel Assumptions.all m X g ⟨2644, .wait (mbarLoc L c .qUtccp) p ok acq sc⟩ →
    qUtccpSlot ≤ Sched.threadTime (timed P L) X g

/-- Lane `y` has an event of the MMA code from the arrival on `qTma` (pc 1929) on that is neither
undefined behaviour nor its exit. -/
def MmaPast (L : Launch) (X : Execution) (y : Nat) : Prop :=
  ∃ j e0, X.get (y, j) = some e0 ∧ (∀ f, e0.kind ≠ .ub f) ∧ e0.kind ≠ .exit ∧
    MbarRow.MmaAt L y e0.pc ∧ 1929 ≤ e0.pc

/-- The producer of `qUtccp` while it lags: the MMA lane of the CTA past its arrival, before its
commit. -/
def QProd (L : Launch) (X : Execution) (c y : Nat) : Prop :=
  y = mmaLane L X c ∧ y / L.block = c ∧ MmaPast L X y ∧
    (X.tr y).countP (commitsTo (mbarLoc L c .qUtccp)) = 0

/-- **A waiter at its `qUtccp` wait has no successful poll of it** (the rows' first polls). -/
theorem qUtccp_first (hR : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows P L Y)
    {c g : Nat} (hg : QWaitNext L m X c g) : okPolls (mbarLoc L c .qUtccp) (X.tr g) = 0 := by
  obtain ⟨hgt, -, pc, p, ok, acq, sc, -, Y, hY, htk, he⟩ := hg
  rcases qUtccp_use (hR Y hY) hgt he rfl with ⟨n, hk⟩ | ⟨-, ⟨-, -, s, hk, -⟩ | ⟨-, -, h0⟩⟩
  · cases hk
  · cases hk
  · rwa [htk] at h0

/-- **At its wait on `qTma` the lane has made its arrival and its eight loads.** -/
theorem qTma_pre (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows P L Y)
    {y c pc p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y ⟨pc, .wait (mbarLoc L c .qTma) p ok acq sc⟩) :
    arrivals (mbarLoc L c .qTma) (X.tr y) = 1 ∧
      (X.tr y).countP (issuesTo (mbarLoc L c .qTma)) = 8 := by
  have hn' := hn
  obtain ⟨Y, hY, -, he⟩ := hn'
  rcases qTma_use (hR Y hY) hn.lt he rfl with ⟨n, hk⟩ | ⟨⟨⟨hw, hlo, hhi⟩, -⟩, hc, -⟩
  · cases hk
  · subst hc
    exact mma_tmaPre hp hX hFw hw hn ⟨hlo, hhi⟩

/-- **The `qUtccp` schedule**: the waiters of CTA `c` wait for the MMA lane's commit, at the
slot `qUtccpSlot`. -/
theorem qUtccp_lag (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows P L Y)
    (hnu : ¬ HasUb X) (hT : QueryTime P L m X) (c : Nat) :
    Sched.LagN (timed P L) X (mbarLoc L c .qUtccp) 0 (QProd L X c) (QWaitNext L m X c)
      (fun _ => qUtccpSlot) 1 (commitsTo (mbarLoc L c .qUtccp)) := by
  refine ⟨fun _ _ _ => le_rfl, fun g hg => ?_, ?_, ?_, fun g hg => ?_⟩
  · obtain ⟨-, -, pc, p, ok, acq, sc, hw, hn⟩ := hg
    rcases hw with ⟨-, rfl⟩ | ⟨ht, rfl⟩ | ⟨hd, rfl⟩
    · exact (mma_slot_wait hp hFw hn).ge
    · exact hT.tmaSlot ht hn
    · exact hT.deqSlot hd hn
  · rintro y ⟨-, hc, ⟨j, e0, he0, hu0, -, ⟨hw, -, hhi⟩, hlo⟩, h0⟩ -
    subst hc
    exact mma_slot_early hp hX hFw hnu hw he0 hu0 ⟨hlo, hhi⟩ h0
  · rintro y k pc ⟨-, hc, ⟨j, e0, he0, hu0, hx0, ⟨hw, -, hhi⟩, hlo⟩, -⟩ hx
    subst hc
    have hl := Execution.exit_last hX (Frame.lt_of_get hX hx) hx
    have hj : j < (X.tr y).length := (List.getElem?_eq_some_iff.mp he0).1
    have hjk : j < k := by
      rcases Nat.lt_or_ge j k with h | h
      · exact h
      · have hjk : j = k := by omega
        subst hjk
        rw [hx] at he0
        cases he0
        exact absurd rfl hx0
    exact mma_commitExit hp hX hFw hw he0 hu0 ⟨hlo, hhi⟩ hjk hx
  · rw [qUtccp_first hR hg]
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
