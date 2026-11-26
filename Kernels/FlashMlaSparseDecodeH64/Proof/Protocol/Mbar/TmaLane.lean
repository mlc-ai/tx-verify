-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch

@[expose] public section

/-! # The TMA warp's mbarrier uses are its elected lane's

Every mbarrier site of the TMA row (`MbarRow.tmaSites`, pcs 2205–2308) is after the warp's
election at pc 2165, so a use of the row is at a `TmaOn` pc (`tmaOn_of_use`), and with one TMA lane
per CTA (`TmaOne`, lane A) it is the CTA's `tmaLane` (`tma_lane_eq`). `tmaThread L X c` is that lane
when the CTA has one and a thread of warp 5 otherwise, so it is never a lane of another warp
(`tmaThread_mod`), as a producer list of distinct threads needs. The channels of the TMA lane
(`Protocol/Raw`, `Protocol/Coord`, `Protocol/Close`) take their lane from here. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {L : Launch} {X : Execution}

/-- **A use of the TMA row is after the election.** -/
theorem tmaOn_of_use {g k : Nat} {e : Event} {l : Loc} (hw : MbarRow.TmaAt L g e.pc)
    (h : MbarRow.TmaUse L X g k e l) : TmaOn L g e.pc := by
  refine ⟨hw, ?_⟩
  cases h with
  | rawLoad hpc =>
    simp only [MbarRow.rawLoadPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
    omega
  | qWait hpc | lastWait hpc | coordWait hpc | freeWait hpc | rawArrive hpc | coordFree hpc =>
    omega

/-- **The lane of a use of the TMA row is its CTA's TMA lane.** -/
theorem tma_lane_eq (hO : TmaOne L X) {g k : Nat} {e : Event} {l : Loc}
    (he : X.get (g, k) = some e) (hn : ∀ f, e.kind ≠ .ub f) (hw : MbarRow.TmaAt L g e.pc)
    (h : MbarRow.TmaUse L X g k e l) :
    g = tmaLane L X (g / L.block) :=
  laneOn_eq hO he hn (tmaOn_of_use hw h)

variable {P : Params} {m : Mem0}

open Classical in
/-- The TMA lane of CTA `c`, or thread 160 of the CTA when no lane has a `TmaOn` event. -/
def tmaThread (L : Launch) (X : Execution) (c : Nat) : Nat :=
  if ∃ y k e, X.get (y, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ TmaOn L y e.pc ∧
      y / L.block = c then tmaLane L X c
  else c * L.block + 160

/-- **The TMA thread is a warp-5 thread of its CTA.** -/
theorem tmaThread_mod (hp : Pre P L m) (c : Nat) :
    tmaThread L X c / 384 = c ∧ 160 ≤ tmaThread L X c % 384 ∧ tmaThread L X c % 384 < 192 := by
  unfold tmaThread
  split
  · next hex =>
    unfold tmaLane laneOn
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨k, e, -, -, ⟨⟨h5, -⟩, -⟩, hc⟩ := Classical.choose_spec hex
    simp only [MbarRow.warp, tidOf_x_eq hp] at h5
    generalize Classical.choose hex = y at hc h5 ⊢
    rw [hp.block] at hc
    omega
  · rw [hp.block]
    omega

/-- **The lane of a use of the TMA row is its CTA's TMA thread.** -/
theorem tma_thread_eq (hO : TmaOne L X) {g k : Nat} {e : Event} {l : Loc}
    (he : X.get (g, k) = some e) (hn : ∀ f, e.kind ≠ .ub f) (hw : MbarRow.TmaAt L g e.pc)
    (h : MbarRow.TmaUse L X g k e l) :
    g = tmaThread L X (g / L.block) := by
  have hex : ∃ y k e, X.get (y, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ TmaOn L y e.pc ∧
      y / L.block = g / L.block :=
    ⟨g, k, e, he, hn, tmaOn_of_use hw h, rfl⟩
  unfold tmaThread
  rw [ite_eq_left_of_eq_true _ _ (eq_true hex)]
  exact tma_lane_eq hO he hn hw h

/-- **A lane with an event at a TMA pc after the election is its CTA's TMA thread.** -/
theorem tma_thread_on (hO : TmaOne L X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hn : ∀ f, e.kind ≠ .ub f) (hon : TmaOn L g e.pc) :
    g = tmaThread L X (g / L.block) := by
  unfold tmaThread
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨g, k, e, he, hn, hon, rfl⟩)]
  exact laneOn_eq hO he hn hon

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
