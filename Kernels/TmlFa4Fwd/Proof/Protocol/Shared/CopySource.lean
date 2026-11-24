-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Source
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime

@[expose] public section

/-! # The sources of the row copies are K/V elements (`cpSrc`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A row copy reads an element of a K/V row.** -/
theorem cpSrc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : CpSrc p X := by
  intro i s l hcp hc
  obtain ⟨hw, -⟩ := copy_row hp hX hFw hcp
  obtain ⟨pc, he⟩ := hcp
  obtain ⟨lay, hl, page, hpg, h, hh, r, hr, c, hc2, t, ht, hloc, hz⟩ :=
    ld_cp_src hp hX hFw hw he
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [hloc] at h1 h2 h3 h4
  simp only at h1 h2 h3 h4
  generalize hB : page * lay.pageStride + h * lay.headStride + r * lay.rowStride = B at h3 h4
  refine ⟨page, hpg, h, hh, r, hr, (l.addr - (lay.base + 2 * B)) / 2, by omega,
    (l.addr - (lay.base + 2 * B)) % 2, by omega, ?_⟩
  have key : l = (lay.loc page h r ((l.addr - (lay.base + 2 * B)) / 2)).at
      ((l.addr - (lay.base + 2 * B)) % 2) := by
    obtain ⟨sp, ct, ad⟩ := l
    simp only at h1 h2 h3 h4 ⊢
    subst h1 h2
    simp only [CacheLayout.loc, globalLoc, Loc.at, Loc.mk.injEq, true_and, hB]
    omega
  rcases hl with rfl | rfl
  · exact .inl key
  · exact .inr key

end PTX.Kernels.TmlFa4Fwd.Proof
