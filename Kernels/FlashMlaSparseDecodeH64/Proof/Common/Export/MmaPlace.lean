-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem

@[expose] public section

/-! # The MMA warp's tensor-core events

An MMA or a copy of a launched lane is the MMA warp's (`mma_place`), from the Tensor Memory
rows of the roles; `cover_one`: a byte a one-byte access covers is its location. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {X : Execution}

/-- An MMA or a copy of a launched lane is the MMA warp's. -/
theorem mma_place (hR : TmemRows P L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) {c : TcKind} (hk : e.kind = .tc c)
    (hc : (∃ d s acc mk, c = .mma d s acc mk) ∨ ∃ s, c = .cp s) : MmaAt L g e.pc := by
  rcases hR.place hg he hk with h | h | h | h | h | h | h
  · obtain ⟨-, ⟨dst, h1⟩ | h1⟩ := hR.startup hg he h hk <;> rw [hk] at h1 <;> cases h1 <;>
      rcases hc with ⟨_, _, _, _, h2⟩ | ⟨_, h2⟩ <;> cases h2
  · rcases hR.wg0 hg he h hk with h1 | h1 | h1 | h1 | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ |
      ⟨-, _, _, h1⟩ <;> rw [hk] at h1 <;> cases h1 <;>
      rcases hc with ⟨_, _, _, _, h2⟩ | ⟨_, h2⟩ <;> cases h2
  · exact (hR.wg1 hg he h hk).elim
  · exact h
  · exact (hR.tma hg he h hk).elim
  · exact (hR.index hg he h hk).elim
  · exact (hR.dequant hg he h hk).elim

/-- A covered byte of a one-byte access is its location. -/
theorem cover_one {a : Acc} {b : Loc} (hc : a.Covers b) (h1 : a.size = 1) : b = a.loc := by
  obtain ⟨h2, h3, h4, h5⟩ := hc
  rw [h1] at h5
  have h4' : a.loc.addr ≤ b.addr := h4
  have h5' : b.addr < a.loc.addr + 1 := h5
  cases b
  cases hl : a.loc
  rw [hl] at h2 h3 h4' h5'
  simp only at h2 h3 h4' h5' ⊢
  subst h2 h3
  simp only [Loc.mk.injEq, true_and]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
