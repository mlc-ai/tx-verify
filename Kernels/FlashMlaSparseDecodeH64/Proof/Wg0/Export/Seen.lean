-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # What a block has seen when an event of warpgroup 0 fires

At an event of lane `g` at pc `pc` (a pc of warpgroup 0's code, `103 ≤ pc`) the block in progress
(`w0Fin` of the trace before the event) has events at pcs at most `pc` only (`w0_bound`), and, when
`pc` is past the exchange load (`572 < pc ≤ 1122`) or past the epilogue's row-sum load
(`1157 < pc < 1840`), an event at pc 572 resp. 1157 (`w0_seen`). From the data machine's state
(`FollowW`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The block in progress at an event**: bounded by its pc, with the loads it has passed. -/
theorem w0_boundSeen (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hge : 103 ≤ e.pc)
    (hv : W0Valid P.scale ((X.tr g).take k)) :
    (∀ a ∈ (w0Fin ((X.tr g).take k)).2, 103 ≤ a.pc → a.pc ≤ e.pc) ∧
    (572 < e.pc → e.pc ≤ 1122 → ∃ f ∈ (w0Fin ((X.tr g).take k)).2, f.pc = 572) ∧
    (1157 < e.pc → e.pc < 1840 → ∃ f ∈ (w0Fin ((X.tr g).take k)).2, f.pc = 1157) := by
  obtain ⟨st, hst, hslot, hpre, hI, -, hBS⟩ :=
    followW hp hX hFw hw he hub (w0_scale_rd hp) hv k le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he hst hub
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX he hst hub
    have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : e.pc = (thread P L g).pc (.inl b, n) := hpc'
    omega
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  have h2 : e.pc = d.c.site.pc := hpc'
  obtain ⟨hB, hS1, hS2⟩ := hBS d rfl
  exact ⟨fun a ha h => h2 ▸ hB a ha h, fun h h' => hS1 (h2 ▸ h) (h2 ▸ h'),
    fun h h' => hS2 (h2 ▸ h) (h2 ▸ h')⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
