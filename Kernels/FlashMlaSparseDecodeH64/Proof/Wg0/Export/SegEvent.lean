-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Objects
public import Lemmas.Flow.Counted

@[expose] public section

/-! # The events of a finished block

A finished block `t` of a lane's prefix `k` is the block in progress before the closing event
at index `K0` (`w0Fin_block_of_close`); its events are the entries before `K0` with `t` closed
blocks before them (`w0_seg_events`, the converse `w0Scan_mem_of_idx`). The ring counts of the
lane's `soReady` arrivals give the closed blocks (`w0Closed_of_ring`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The ring counts of the `so_ready` arrivals are the closed blocks**: `r` blocks. -/
theorem w0Closed_of_ring (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k r : Nat}
    (h : ∀ b : Fin 2, arrivals (mbarLoc L (g / L.block) (.soReady b)) ((X.tr g).take k) =
      ringUses 2 b.val r) (hal : LaneUbFree X g k) : w0Closed ((X.tr g).take k) = r := by
  rw [w0Closed_arrs hp hX hFw hw hal]
  have h0 := h 0
  have h1 := h 1
  unfold arrs2
  change arrivals (mbarLoc L (g / L.block) (.soReady 0)) _ +
    arrivals (mbarLoc L (g / L.block) (.soReady 1)) _ = r
  rw [h0, h1]
  simp only [ringUses]
  omega

/-- **The events of a finished block**: block `t` of the prefix `k` (ending with a lane's
exit-free prefix) is the block in progress before its closing event at `K0 < k`, and each of its
events is an entry before `K0` with `t` closed blocks before it. -/
theorem w0_seg_events (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k t : Nat} {seg : List Event}
    (hseg : (w0Fin ((X.tr g).take k)).1[t]? = some seg) (hal : LaneUbFree X g k) :
    ∃ K0 c0, X.get (g, K0) = some c0 ∧ c0.pc = 1122 ∧ K0 < k ∧
      (w0Fin ((X.tr g).take K0)).1.length = t ∧ seg = (w0Fin ((X.tr g).take K0)).2 ∧
      ∀ f ∈ seg, ∃ j < K0, X.get (g, j) = some f ∧ w0Closed ((X.tr g).take j) = t := by
  have hno := w0_noEarly_pre hp hX hFw hw hal
  have htl : t < w0Closed ((X.tr g).take k) := by
    have := (List.getElem?_eq_some_iff.mp hseg).1
    rwa [w0Fin_length hno] at this
  obtain ⟨K0, c0, hK0, hpc0, hcl0⟩ := w0_close_idx htl
  have hK0lt : K0 < k := by
    have := (List.getElem?_eq_some_iff.mp hK0).1
    simp only [List.length_take] at this
    omega
  have hc0 : X.get (g, K0) = some c0 := by
    have : (X.tr g)[K0]? = some c0 := by
      rw [List.getElem?_take_of_lt hK0lt] at hK0
      exact hK0
    exact this
  have hno0 := w0_noEarly_pre hp hX hFw hw (hal.mono hK0lt.le)
  have hlen0 : (w0Fin ((X.tr g).take K0)).1.length = t := by
    rw [w0Fin_length hno0, ← hcl0, List.take_take, Nat.min_eq_left hK0lt.le]
  have hblk := w0Fin_block_of_close hp hX hFw hw hc0 hpc0 hK0lt hal
  rw [hlen0, hseg] at hblk
  obtain rfl : seg = (w0Fin ((X.tr g).take K0)).2 := Option.some.inj hblk
  refine ⟨K0, c0, hc0, hpc0, hK0lt, hlen0, rfl, fun f hf => ?_⟩
  have hfs : f ∈ (w0Scan ((X.tr g).take K0)).2 := by rw [← w0Fin_snd]; exact hf
  obtain ⟨j, hj, hcj⟩ := w0Scan_snd_idx hfs
  have hjK : j < K0 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  refine ⟨j, hjK, ?_, ?_⟩
  · rw [List.getElem?_take_of_lt hjK] at hj
    exact hj
  · rw [List.take_take, Nat.min_eq_left hjK.le] at hcj
    rw [hcj, ← hcl0, List.take_take, Nat.min_eq_left hK0lt.le]

/-- **The last reading of a block at some pcs is of an event of the block at one of them.** -/
theorem w0Last_event {α : Type} {f : Event → Option α} {pcs : List Nat} {seg : List Event} {v : α}
    (h : w0Last f pcs seg = some v) : ∃ ev ∈ seg, ev.pc ∈ pcs ∧ f ev = some v := by
  unfold w0Last at h
  obtain ⟨ev, hev, hv⟩ := List.mem_filterMap.mp (List.mem_of_getLast? h)
  refine ⟨ev, hev, ?_, ?_⟩
  · by_contra hn
    simp [hn] at hv
  · by_cases hm : ev.pc ∈ pcs
    · simpa [hm] using hv
    · simp [hm] at hv

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
