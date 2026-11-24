-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

@[expose] public section

/-! # A 512-column allocation is column 0

A Tensor Memory allocation completes only at a column whose range fits the 512-column address
space (`Tmem.available`: `base + columns ≤ 512`), so an allocation of all 512 columns that its
CTA's allocator performs is at column 0 (`perform_alloc512`). In a CTA history whose replay does
not fault, every recorded allocation was performed from a replayed state, and the consistency
field `HistoriesOk` excludes a blocked replay, so every recorded 512-column allocation has column 0
(`run_alloc512`, `Consistent.alloc512_base`). The address the allocating warp stores is then the
32-bit value 0 (`Consistent.alloc512_result`, from OBJ-TMEM-ALLOC-RESULT). A history without fault
is what `¬ ResourceUnsafe` gives (`tmemNoFault_of_safe`). -/

namespace PTX.Tmem.Pair
noncomputable section

/-- **An allocation of 512 columns completes only at column 0.** -/
theorem perform_alloc512 {s t : Tmem.State} {base : Nat}
    (h : Tmem.perform s (.alloc 512 base) = .done t) : base = 0 := by
  unfold Tmem.perform at h
  by_cases hav : Tmem.available s base 512 = true
  · simp only [Tmem.available, Bool.and_eq_true, decide_eq_true_eq] at hav
    omega
  · simp [hav] at h
    split_ifs at h

/-- In a replay that neither blocks nor faults, every recorded 512-column allocation is at
column 0. -/
theorem run_alloc512 {H : List Requests} {s : Tmem.State} (hnb : runRequests s H ≠ .blocked)
    (hnf : ∀ reason, runRequests s H ≠ .fault reason) {r : Requests} (hr : r ∈ H) {base : Nat}
    (ha : r.action = .alloc 512 base) : base = 0 := by
  induction H generalizing s with
  | nil => simp at hr
  | cons x H ih =>
    simp only [runRequests] at hnb hnf
    cases hp : Tmem.perform s x.action with
    | done next =>
      rw [hp] at hnb hnf
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [ha] at hp
        exact perform_alloc512 hp
      · exact ih hnb hnf hr
    | blocked => rw [hp] at hnb; exact absurd rfl hnb
    | fault reason => rw [hp] at hnf; exact absurd rfl (hnf reason)

end
end PTX.Tmem.Pair

namespace PTX
noncomputable section
open Tmem.Pair
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A safe execution's CTA histories replay without a fault. -/
theorem tmemNoFault_of_safe (hs : ¬ ResourceUnsafe L X) (cta : Nat) :
    ∀ reason, runRequests {} (X.tmemHistory cta) ≠ .fault reason :=
  fun reason h => hs ⟨cta, .inl ⟨reason, h⟩⟩

/-- **Every 512-column allocation a CTA's allocator performs is at column 0**, when its history
replays without a fault. -/
theorem Consistent.alloc512_base (hX : Consistent L K A mem0 X) {cta : Nat}
    (hnf : ∀ reason, runRequests {} (X.tmemHistory cta) ≠ .fault reason)
    {r : Requests} (hr : r ∈ X.tmemHistory cta) {base : Nat}
    (ha : r.action = .alloc 512 base) : base = 0 :=
  run_alloc512 (hX.tmemPair.1 cta).2.2 hnf hr ha

/-- **The address stored by a 512-column allocation is 0.** Lane 0's allocation event `i`, of a
request its CTA's allocator performed (`r`), stores the 32-bit value 0 at its next event. -/
theorem Consistent.alloc512_result (hX : Consistent L K A mem0 X) {cta : Nat}
    (hnf : ∀ reason, runRequests {} (X.tmemHistory cta) ≠ .fault reason)
    {i : EvId} {pc : Nat} {group : CtaGroup} {dst : Option Loc}
    (hi : X.get i = some ⟨pc, .tc (.resource group dst (.alloc 512))⟩)
    {r : Requests} (hr : r ∈ X.tmemHistory cta) (hown : r.own.event L 0 = i) {base : Nat}
    (ha : r.action = .alloc 512 base) {pc' : Nat} {a : Acc} {bs : List Byte}
    (hw : X.get (i.1, i.2 + 1) = some ⟨pc', .wr a bs⟩) :
    bs = (Value.bits 32 (BitVec.ofNat 64 0)).toBytes := by
  have h0 := hX.alloc512_base hnf hr ha
  subst h0
  exact hX.tmemPairResult i pc group dst 512 hi cta r 0 hr hown ha pc' a bs hw

end
end PTX
