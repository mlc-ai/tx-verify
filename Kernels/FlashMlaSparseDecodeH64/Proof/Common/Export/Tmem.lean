-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Place
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Tmem

@[expose] public section

/-! # The Tensor Memory rows of every role, and what they give

`TmemRows P L X` bundles the rows of `Iface/TmemRows/`; `tmem_rows` proves them all from the
roles' exports (`tmemRow_<role>`, `tmemRow_place`). `tmem_res` is what the classes use of them: a
paired Tensor Memory operation (`.resource`) of a launched lane is the startup's allocation of 512
columns or its relinquishment, in warp 0, or warpgroup 0's deallocation at pc 1840; all of CTA
group 1. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

/-- **The Tensor Memory rows of every role.** -/
structure TmemRows (P : Params) (L : Launch) (X : Execution) : Prop where
  startup : TmemRow.Startup P L X
  wg0 : TmemRow.Wg0 P L X
  wg1 : TmemRow.Wg1 P L X
  mma : TmemRow.Mma P L X
  tma : TmemRow.Tma P L X
  index : TmemRow.Index P L X
  dequant : TmemRow.Dequant P L X
  place : TmemRow.Place P L X

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The rows hold** under `Follow`. -/
theorem tmem_rows (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRows P L X :=
  ⟨tmemRow_startup hp hX hFw, tmemRow_wg0 hp hX hFw, tmemRow_wg1 hp hX hFw,
    tmemRow_mma hp hX hFw, tmemRow_tma hp hX hFw, tmemRow_index hp hX hFw,
    tmemRow_dequant hp hX hFw, tmemRow_place hp hX hFw⟩

/-- **The paired Tensor Memory operations**: the startup's allocation of 512 columns or its
relinquishment, in warp 0, or warpgroup 0's deallocation at pc 1840; of CTA group 1. -/
theorem tmem_res (hR : TmemRows P L X) {g k : Nat} {e : Event} {grp : CtaGroup}
    {dst : Option Loc} {act : Tmem.Request} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hk : e.kind = .tc (.resource grp dst act)) :
    grp = .one ∧ ((StartupAt e.pc ∧ warp L g = 0 ∧ (act = .alloc 512 ∨ act = .relinquish)) ∨
      (Wg0At L g e.pc ∧ e.pc = 1840)) := by
  rcases hR.place hg he hk with h | h | h | h | h | h | h
  · obtain ⟨hw, ⟨d, hk'⟩ | hk'⟩ := hR.startup hg he h hk <;> rw [hk] at hk' <;> cases hk'
    · exact ⟨rfl, .inl ⟨h, hw, .inl rfl⟩⟩
    · exact ⟨rfl, .inl ⟨h, hw, .inr rfl⟩⟩
  · obtain h1 | h1 | h1 | h1 | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ | ⟨hpc, d, a, h1⟩ :=
      hR.wg0 hg he h hk <;> rw [hk] at h1 <;> cases h1
    exact ⟨rfl, .inr ⟨h, hpc⟩⟩
  · exact (hR.wg1 hg he h hk).elim
  · obtain h1 | ⟨_, _, -, -, h1, -⟩ | ⟨_, h1, -⟩ | ⟨_, _, -, -, h1, -⟩ |
        ⟨_, _, _, -, -, h1, -⟩ := hR.mma hg he h hk <;>
      rw [hk] at h1 <;> cases h1
  · exact (hR.tma hg he h hk).elim
  · exact (hR.index hg he h hk).elim
  · exact (hR.dequant hg he h hk).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
