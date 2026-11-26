-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem

@[expose] public section

/-! # The events at the accumulator loads' pcs

An event of a lane of warpgroup 0 at a pc of `w0OPcs` is a `32x32b` Tensor Memory load at the
column `64 c` of the chunk `c`: of the rescale arm (pcs 716, 817, 918, 1019) or of the epilogue
(pcs 1201, 1361, 1519, 1676). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem site_opc (s : Wg0.Site) (h : s.pc ∈ w0OPcs) :
    (∃ c, s = .rld c) ∨ ∃ c, s = .old c := by
  revert h
  cases s <;> (try (rename_i x; fin_cases x)) <;> (try (rename_i y; fin_cases y)) <;>
    first | (intro; exact Or.inl ⟨_, rfl⟩) | (intro; exact Or.inr ⟨_, rfl⟩) |
      (intro h; exfalso; revert h; decide)

/-- **An accumulator load's event**: a `32x32b` load at the column `64 c`. -/
theorem wg0_opcKind_hub (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : e.pc ∈ w0OPcs) :
    ∃ (a : Nat) (vals : List Value) (c : Fin 4), e.kind = .tc (.ld a vals .s32x32b) ∧
      a = 64 * c.val ∧ (e.pc = [716, 817, 918, 1019].getD c.val 0 ∨
        e.pc = [1201, 1361, 1519, 1676].getD c.val 0) := by
  have hr : 103 ≤ e.pc ∧ e.pc < 1842 := by
    simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
    omega
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc' hr
  have hE2 := hE.2
  have hsp : d.site.pc = e.pc := hpc'.symm
  have hs := site_opc d.site (by rw [hsp]; exact hpc)
  unfold Wg0.EvK at hE2
  rcases hs with ⟨c, hc⟩ | ⟨c, hc⟩ <;> rw [hc] at hE2 hsp <;> unfold Wg0.TcLdEv at hE2 <;>
    rcases hE2 with ⟨vs, hv⟩ | ⟨f, hf⟩
  · exact ⟨_, vs, c, hv, rfl, Or.inl (by simpa [Wg0.Site.pc] using hsp.symm)⟩
  · exact absurd hf (hub f)
  · exact ⟨_, vs, c, hv, rfl, Or.inr (by simpa [Wg0.Site.pc] using hsp.symm)⟩
  · exact absurd hf (hub f)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
