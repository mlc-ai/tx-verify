-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX

private theorem plain {r : Nat} (lo : 2141 ≤ r) (hi : r ≤ 2274) :
    r ≠ 506 ∧ r ≠ 944 ∧ r ≠ 945 ∧ r ≠ 1542 ∧ r ≠ 1543 ∧ r ≠ 1544 ∧ r ≠ 1611 ∧ r ≠ 1676 ∧
      r ≠ 1534 ∧ r ≠ 1536 ∧ r ≠ 1538 ∧ r ≠ 1540 := by
  omega

/-- The address registers of the preloaded bias loads. -/
theorem value_pre (e : Entry) (L : Launch) (g : Nat) (d : D) {r : Nat} (h1 : 2141 ≤ r)
    (h2 : r ≤ 2204) : valueOf e L g d r = u64 (sx ((e.split + d.i * e.splits) * 128) * 2 +
      biasBase e (g % L.block) + 2 * (r - 2141)) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := plain h1 (by omega)
  simp only [valueOf, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, ↓reduceIte]
  unfold scalarValue
  split <;> try (exfalso; omega)
  simp only [h1, h2, and_self, ↓reduceIte]

/-- The address registers of the loop's bias loads, one block ahead. -/
theorem value_nxt (e : Entry) (L : Launch) (g : Nat) (d : D) {r : Nat} (h1 : 2211 ≤ r)
    (h2 : r ≤ 2274) : valueOf e L g d r = u64 (sx ((e.splits + (e.split + d.i * e.splits)) * 128)
      * 2 + biasBase e (g % L.block) + 2 * (r - 2211)) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := plain (by omega) h2
  simp only [valueOf, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, ↓reduceIte]
  unfold scalarValue
  split <;> try (exfalso; omega)
  have gap : ¬ (2141 ≤ r ∧ r ≤ 2204) := by omega
  simp only [gap, h1, h2, and_self, ↓reduceIte]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
