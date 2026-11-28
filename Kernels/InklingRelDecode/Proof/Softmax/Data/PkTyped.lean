-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS

@[expose] public section

/-! # The 32 words the probability store writes are pairs of `bf16` numbers

From typed inputs of the exponent window (`ExpIn`) its outputs are typed (`exp_typed`), the pack of
the exponentials gives the 32 words of the store of pc 1009 (registers 1677 to 1708): each a pair
of `bf16` numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- A run leaves the registers it does not write. -/
theorem V'_notin (r : RunData) (ok : r.Ok) (W : Nat → Value) {x : Nat} (hx : x ∉ r.outs) :
    r.V' W x = W x := by
  unfold RunData.V' valueEx
  have : (r.fs1 W).lookup x = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    have hk : p.1 ∈ r.outs := by rw [← ok.h1 W]; exact List.mem_map_of_mem hp
    simpa using fun h : x = p.1 => hx (h ▸ hk)
  rw [this]
  rfl

theorem pkIn_of {V : Nat → Value} (h : ExpIn V) : PkIn (vE3 V) :=
  ⟨fun r h1 h2 => by
    have hr : r ∈ runE2.outs := by
      have : ∀ x, 1994 ≤ x → x < 2018 → x ∈ runE2.outs := by decide +kernel
      exact this r h1 h2
    simpa [ExpTy, h1, h2] using exp_typed h hr,
   fun r h1 h2 => by
    have hr : r ∈ runE2.outs := by
      have : ∀ x, 508 ≤ x → x < 524 → x ∈ runE2.outs := by decide +kernel
      exact this r h1 h2
    have := exp_typed h hr
    simpa [ExpTy, show ¬(1994 ≤ r ∧ r < 2018) by omega] using this⟩

theorem pkIn_p1 {W : Nat → Value} (h : PkIn W) : PkIn (vP1 W) := by
  have n1 : ∀ x, 1994 ≤ x → x < 2018 → x ∉ runK1.outs := by decide +kernel
  have n2 : ∀ x, 508 ≤ x → x < 524 → x ∉ runK1.outs := by decide +kernel
  exact ⟨fun r h1 h2 => by rw [vP1, V'_notin runK1 runK1_ok W (n1 r h1 h2)]; exact h.pr r h1 h2,
    fun r h1 h2 => by rw [vP1, V'_notin runK1 runK1_ok W (n2 r h1 h2)]; exact h.sg r h1 h2⟩

/-- **The 32 words of the store are pairs of `bf16` numbers.** -/
theorem tm_typed {V : Nat → Value} (h : ExpIn V) : ∀ r ∈ kTm, BfNum (vP2 (vP1 (vE3 V)) r) := by
  intro r hr
  have hp := pkIn_of h
  rcases List.mem_append.mp hr with h1 | h2
  · have hn : r ∉ runK2.outs := by
      have : ∀ x ∈ runK1.outs, x ∉ runK2.outs := by decide +kernel
      exact this r h1
    rw [vP2, V'_notin runK2 runK2_ok _ hn]
    exact pk1_typed hp h1
  · exact pk2_typed (pkIn_p1 hp) h2

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
