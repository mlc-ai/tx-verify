-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Ref

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

/-- Only the read at PC 2423 introduces a new value of the loop bound. -/
theorem ref_next {n : Nat} {L : Launch} {g : Nat} {e : Event} {d d' : D} (hr : Ref n d)
    (hread : d.site = .ldNum → ∀ a bs v, e.kind = .rd a bs →
      rebuild 3 bs = .ok v → readsCount v n)
    (hn : next L g d e = some (some d')) : Ref n d' := by
  obtain ⟨s,i,w⟩ := d
  cases s
  case ldNum =>
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i a bs hk
    cases hw : rebuild 3 bs <;> simp [hw, Except.toOption] at hn
    subst d'
    exact fun _ => hread rfl a bs _ hk hw
  case setMaxReg =>
    cases hn
    intro h
    cases h
  all_goals
    have keep := hr (by rfl)
    simp only [next] at hn
    repeat' split at hn
    all_goals try contradiction
    all_goals cases hn
    all_goals intro _
    all_goals first | exact keep |
      (simp only [iterNext, afterQk]; split_ifs <;> exact keep)

end PTX.Kernels.InklingRelDecode.Proof.Mma
