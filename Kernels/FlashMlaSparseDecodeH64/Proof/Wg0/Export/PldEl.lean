-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # The element of a peer load is the parity of the reads before it

A peer load of a lane of warpgroup 0 (pc `477 + 5 k0`) reads the 8 bytes of element `el < 2` of
its slot of the exchange (`204800 + 4096 w + 16 l + 512 k0 + 8 el`), and `el` is the parity of
the number of reads at that pc earlier in the block (`w0Pf` of the block in progress): the first
read of a block is element 0, the second element 1 (the data machine's `InvW.par`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The element of a peer load** (valid rows). -/
theorem w0_pld_el (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : MbarRow.warp L g < 4)
    {j k0 : Nat} {e : Event} (hv : W0Valid P.scale ((X.tr g).take j)) (hk0 : k0 < 8)
    (he : X.get (g, j) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc : e.pc = 477 + 5 * k0) :
    ∃ a bs el, e.kind = .rd a bs ∧ el < 2 ∧
      MemRow.WsAcc L (g / L.block) (204800 + 4096 * (tidOf L g / 32) + 16 * (tidOf L g % 32) +
        512 * k0 + 8 * el) 8 a ∧
      (w0Pf (w0Fin ((X.tr g).take j)).2 k0).length % 2 = el := by
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  obtain ⟨st, hst, hslot, hpre, hI, -⟩ :=
    followW hp hX hFw hw he hub (w0_scale_rd hp) hv j le_rfl
  have hσc := control_of_data hst
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσc
  cases hσc
  obtain ⟨q0, n⟩ := st
  obtain ⟨d', n', hσe, -, hE, -⟩ := wg0_state hJ hi hev hpc' (by omega)
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    exfalso
    simp only [eraseThread, Code.eraseSum, Prod.mk.injEq] at hσe
    obtain ⟨h1, -⟩ := hσe
    cases h1
  · obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
    obtain ⟨hIW, hOk, -⟩ := hI d rfl
    have hdd : d' = d.c := by
      simp only [eraseThread, Code.eraseSum, Code.eraseStubs, eraseFrag, wg0Erase,
        Prod.mk.injEq] at hσe
      obtain ⟨h1, -⟩ := hσe
      simpa using h1.symm
    subst hdd
    have hs : d.c.site = Site.pld ⟨k0, hk0⟩ :=
      Wg0.site_pc_inj (by rw [show d.c.site.pc = e.pc from hpc'.symm, hpc]; rfl)
    have hE2 := hE.2
    unfold Wg0.EvK at hE2
    rw [hs] at hE2
    obtain ⟨hel, hE'⟩ := hE2
    have hk' : ∃ a bs, e.kind = .rd a bs := by
      rcases hE' with ⟨a, bs, hk, -⟩ | ⟨f, hf⟩
      · exact ⟨a, bs, hk⟩
      · exact absurd hf (hub f)
    obtain ⟨a, bs, hk, hw'⟩ :=
      Wg0.rdAt_ws (.inl hk') hE' (Wg0.r17_loc hp (MemRow.wg0_tid hw) hk0)
    refine ⟨a, bs, d.c.el, hk, hel, hw', ?_⟩
    rw [w0Fin_snd]
    have hpar := hIW.par ⟨k0, hk0⟩
    simp only at hpar
    by_cases h1 : d.c.el = 1
    · rw [h1]; exact hpar.mpr ⟨hs, h1⟩
    · have h0 : d.c.el = 0 := by omega
      rw [h0]
      have := mt hpar.mp (fun h => h1 h.2)
      omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
