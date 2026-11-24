-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneCta
public import Kernels.InklingRelDecode.Proof.Protocol.BarOne
public import Kernels.InklingRelDecode.Proof.Interface.LockLate

@[expose] public section

/-!
# The workers' final `bar.sync 0` follows the default partition's loop

`WorkerLate` (`BarLaneCta.lean`): when a worker thread of a CTA has made its final `bar.sync 0`
(source ordinal at least 2), every `bar.sync 0, 128` of a default-partition thread of the CTA has
a later event in its thread. The worker's event follows three barrier-1 events of its thread
(`Interface.worker_final_b1`); the third (ordinal 2) was passed, so every thread of the CTA has
a barrier-1 event of ordinal 2 (`Bar.bar1_member`, with the exit's three barrier-1 events for an
exiting thread, `ledger_exit`); a default-partition thread's `bar.sync 0, 128` follows at most two
barrier-1 events (`Interface.loop_b1_le`), so it is before that event.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`WorkerLate`**, from `RoleReads`. -/
theorem workerLate_of_roleReads (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) : WorkerLate L X := by
  intro g k pc cnt m hg hw he hord g' k' pc' hdiv hD' he'
  have hw' : ¬ g % L.block < 128 := by omega
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have h3 := worker_final_b1 hpre hX hS ht hR he hw' hord
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  -- the worker's barrier-1 event of ordinal 2
  have hlt2 : 2 < ((X.tr g).take k).countP (Execution.isBarId 1) := h3
  obtain ⟨j, x, hj, hx, hjord⟩ := CtaBarrier.countP_index
    (xs := (X.tr g).take k) (p := Execution.isBarId 1) hlt2
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hjk] at hj
  obtain ⟨pcx, cx, mx, rfl⟩ := NamedBar.isBarId_form hx
  have hxget : X.get (g, j) = some ⟨pcx, .bar 1 cx mx⟩ := hj
  obtain ⟨hcx, hmx⟩ := bar_one_static hX hb hxget
  subst hcx hmx
  have hxb : X.IsBarrier (g, j) 1 none pcx := hxget
  rw [List.take_take, Nat.min_eq_left hjk.le] at hjord
  -- every thread of the CTA has the barrier-1 arrival of ordinal 2
  have hjp : (g, j).2 + 1 < (X.tr (g, j).1).length := by
    show j + 1 < (X.tr g).length
    omega
  obtain ⟨i, pci, hi, hiord⟩ := bar1_member hpre hX hxb hjp (g := g') hdiv (by
    rintro ⟨jx, pcx', hjx⟩
    have hex := ledger_exit hpre hX hS ht hR hjx
    have hlt : 2 < ((X.tr g').take jx).countP (Execution.isBarId 1) := hex
    obtain ⟨i, y, hi, hy, hiord⟩ := CtaBarrier.countP_index
      (xs := (X.tr g').take jx) (p := Execution.isBarId 1) hlt
    have hijx : i < jx := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hijx] at hi
    obtain ⟨pcy, cy, my, rfl⟩ := NamedBar.isBarId_form hy
    have hyget : X.get (g', i) = some ⟨pcy, .bar 1 cy my⟩ := hi
    obtain ⟨hcy, hmy⟩ := bar_one_static hX hb hyget
    subst hcy hmy
    refine ⟨i, pcy, hyget, ?_⟩
    rw [List.take_take, Nat.min_eq_left hijx.le] at hiord
    simp only
    omega)
  -- the loop's `bar.sync 0, 128` is before it
  have hle := loop_b1_le hpre hX hS ht hR he'
  have hik : k' < i := by
    by_contra hge
    have hne : i ≠ k' := by
      intro h
      subst h
      have h1 : X.get (g', i) = some ⟨pc', .bar 0 (some 128) .sync⟩ := he'
      have h2 : X.get (g', i) = some ⟨pci, .bar 1 none .sync⟩ := hi
      rw [h1] at h2
      simp at h2
    have hsucc : ((X.tr g').take (i + 1)).countP (Execution.isBarId 1) =
        ((X.tr g').take i).countP (Execution.isBarId 1) + 1 := by
      rw [countP_take_succ (Execution.isBarId 1) (l := X.tr g')
        (show (X.tr g')[i]? = some ⟨pci, .bar 1 none .sync⟩ from hi)]
      simp [Execution.isBarId]
    have hmono : ((X.tr g').take (i + 1)).countP (Execution.isBarId 1) ≤
        ((X.tr g').take k').countP (Execution.isBarId 1) :=
      (List.take_sublist_take_left (by omega : i + 1 ≤ k')).countP_le
    have hb1 : b1N X g' k' = ((X.tr g').take k').countP (Execution.isBarId 1) := rfl
    simp only at hiord
    omega
  have hil : i < (X.tr g').length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simpa using this
  omega

/-- **`Safety.Protocol.ctaBar`**: no CTA barrier arrival faults. The premises are the ones the
other barrier fields take (`hpre`, the consistency of `X`, the soundness of the machines, the
tracking of the execution, `RoleReads`) and `AlphaAgree`: the default partition's threads of a CTA
agree on the count of each barrier-0 arrival. -/
theorem ctaBar_of_roleReads (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) (hA : AlphaAgree L X) : ¬ CtaBarFault L X :=
  NamedBar.no_fault_of_mismatch hX
    (bar_no_mismatch hpre hX hS ht hA (workerLate_of_roleReads hpre hX hS ht hR))

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
