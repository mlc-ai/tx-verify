-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem

@[expose] public section

/-! # The event at the validity read

An event of a lane of warpgroup 0 at pc 289 is a read (`wg0_vmKind`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The validity read's event** is a generic read. -/
theorem wg0_vmKind (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = 289) :
    ∃ (a : Acc) (bs : List (Option Byte)), e.kind = .rd a bs := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc' (by omega)
  have hs : d.site = .vm := Wg0.site_pc_inj (by rw [show d.site.pc = e.pc from hpc'.symm, hpc]; rfl)
  have hE2 := hE.2
  unfold Wg0.EvK at hE2
  rw [hs] at hE2
  rcases hE2 with ⟨a, bs, hk, -⟩ | ⟨f, hf⟩
  · exact ⟨a, bs, hk⟩
  · exact absurd hf (hub f)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
