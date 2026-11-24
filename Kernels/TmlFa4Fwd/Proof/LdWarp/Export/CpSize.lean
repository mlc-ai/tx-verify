-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Open
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSizePrime
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSizeSteady
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSizeWarm
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

import Lemmas.Kernel.FrameU

@[expose] public section

/-! # A row copy reads sixteen bytes or none (`ld_cp_size`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **A row copy reads sixteen bytes or none.** -/
theorem ld_cp_size (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {pc : Nat}
    {sp : AsyncCopy.Spec} (he : X.get (g, k) = some ⟨pc, .copy sp⟩) :
    sp.src.size = 0 ∨ sp.src.size = 16 := by
  have hub : ∀ f, (⟨pc, .copy sp⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n', -, -, -, hi, hev'⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_mem hev' hi.2 trivial).elim
  obtain ⟨a1, -, -, -⟩ := Loader.copy_site hev hub
  have hcpsite : d.site.isCp = true := by rw [← a1]; rfl
  obtain ⟨per, v, i, j, hs⟩ : ∃ per v i j, d.site = .cp per v i j := by
    revert hcpsite
    cases d.site <;> simp [Loader.Site.isCp]
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  obtain ⟨site, v', kk⟩ := d
  simp only at hs
  subst hs
  have h : ∃ x : Prop, ∃ _ : Decidable x, sp.src.size = if x then 16 else 0 := by
    cases per
    · exact ⟨_, _, Loader.cp_size_prime hat hc hf rfl⟩
    · exact ⟨_, _, Loader.cp_size_warm hat hc hf rfl⟩
    · exact ⟨_, _, Loader.cp_size_steady hat hc hf rfl⟩
  obtain ⟨x, _, h⟩ := h
  rw [h]
  split
  · exact .inr rfl
  · exact .inl rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof
