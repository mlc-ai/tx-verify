-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderVCopies

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow

/-- Within one CTA, distinct K/V copy coordinates have disjoint 16-byte destinations. -/
theorem kvCopyVectorsApart {base a b i j k s : Nat} {u v : Bool}
    (hBase : base % 1024 = 0) (hi : i < 16) (hj : j < 16)
    (hDiff : k ≠ s ∨ a % 64 ≠ b % 64 ∨ i ≠ j ∨ u ≠ v) :
    kvCopyAddress base k a i u + 16 ≤ kvCopyAddress base s b j v ∨
      kvCopyAddress base s b j v + 16 ≤ kvCopyAddress base k a i u := by
  have hA := kvCopyAddress_aligned hBase k a i u
  have hB := kvCopyAddress_aligned hBase s b j v
  have hNe : kvCopyAddress base k a i u ≠ kvCopyAddress base s b j v := by
    intro hEq
    have hBlockA := kvCopyAddress_div_1024 hBase k a i u
    have hBlockB := kvCopyAddress_div_1024 hBase s b j v
    rw [hEq] at hBlockA
    have hIdx : k = s ∧ i = j ∧ u = v := by
      cases u <;> cases v <;> simp at hBlockA hBlockB ⊢ <;> omega
    obtain ⟨rfl, rfl, rfl⟩ := hIdx
    have hLane : a % 64 ≠ b % 64 := by simpa using hDiff
    exact kvCopyAddress_lane_ne hLane hEq
  omega

private theorem sharedKvNoOverlap {base owner a b i j k s : Nat} {u v : Bool}
    (hBase : base % 1024 = 0) (hi : i < 16) (hj : j < 16)
    (hDiff : k ≠ s ∨ a % 64 ≠ b % 64 ∨ i ≠ j ∨ u ≠ v) :
    ¬ ({loc := ⟨.shared, owner, kvCopyAddress base k a i u⟩, size := 16} : Acc).Overlap
      {loc := ⟨.shared, owner, kvCopyAddress base s b j v⟩, size := 16} := by
  have hApart := kvCopyVectorsApart hBase hi hj hDiff
  rintro ⟨loc, ⟨_, _, ha, ha'⟩, ⟨_, _, hb, hb'⟩⟩
  change kvCopyAddress base k a i u ≤ loc.addr at ha
  change loc.addr < kvCopyAddress base k a i u + 16 at ha'
  change kvCopyAddress base s b j v ≤ loc.addr at hb
  change loc.addr < kvCopyAddress base s b j v + 16 at hb'
  omega

/-- Distinct priming K coordinates cannot overlap, irrespective of the live-row byte count. -/
theorem kCopyDstNoOverlap {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g k s a b src src' n n' : Nat} {i j : Fin 16} {u v : Bool}
    (hDiff : k ≠ s ∨ a % 64 ≠ b % 64 ∨ i.val ≠ j.val ∨ u ≠ v) :
    ¬ (kCopySpec l g k a src n i u).dst.Overlap (kCopySpec l g s b src' n' j v).dst :=
  sharedKvNoOverlap hp.shared.1 i.isLt j.isLt hDiff

/-- Distinct priming V coordinates cannot overlap, irrespective of the live-row byte count. -/
theorem vCopyDstNoOverlap {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g a b src src' n n' : Nat} {i j : Fin 16} {u v : Bool}
    (hDiff : a % 64 ≠ b % 64 ∨ i.val ≠ j.val ∨ u ≠ v) :
    ¬ (vCopySpec l g a src n i u).dst.Overlap (vCopySpec l g b src' n' j v).dst :=
  sharedKvNoOverlap hp.shared.1 i.isLt j.isLt (Or.inr hDiff)

end PTX.Kernels.TmlFa4Fwd.Loader
