-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Measure

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow Control

private theorem store_after (j : Fin 64) : (Site.store j).position < (storeAt (j.val+1)).position :=
  (by decide +kernel : ∀ k : Fin 64, (Site.store k).position < (storeAt (k.val+1)).position) j

private theorem gate_after (a b : Bool) : 3 < (firstStore a b).position := by
  cases a <;> cases b <;> decide

theorem measure_next {e L g d dn ev} (h : Control.next e L g d ev = some (some dn)) :
    measure dn + ev.counts.toNat ≤ measure d := by
  have cnt : ev.counts.toNat ≤ 1 := by cases ev.counts <;> decide
  have bound := position_bound dn.site
  obtain ⟨s,v⟩ := d
  cases s with
  | wait =>
    obtain ⟨p,k⟩ := ev
    cases k with
    | wait l q ok a sc =>
      cases ok <;> cases h
      · exact Nat.le_refl _
      · change 75-(if e.skip then firstStore e.valid (lead (g%L.block)) else Site.shfl).position
            + 1 ≤ 75
        split
        · have lo := gate_after e.valid (lead (g%L.block)); omega
        · decide
    | _ => cases h
  | store j =>
    cases h
    have lt := store_after j
    change 75-(storeAt (j.val+1)).position+_ ≤ 75-(Site.store j).position
    have bd := position_bound (storeAt (j.val+1)); omega
  | waitLd =>
    cases h
    have lo := gate_after e.valid (lead (g%L.block))
    change 75-(firstStore e.valid (lead (g%L.block))).position+_ ≤ 72
    omega
  | sync0 =>
    cases h
    unfold measure
    split <;> simp only [Site.position] <;> omega
  | shfl =>
    simp only [Control.next] at h
    split at h <;> try contradiction
    cases h
    change 73+_ ≤ 74; omega
  | exit => cases h
  | _ =>
    cases h
    simp only [measure,Site.position]
    omega

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
