-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceE

@[expose] public section

/-! # The step into an event of warpgroup 0's loop

The data state behind an event at a site of the code's chain follows a state at the pc of the
previous event through the control machine's step (`w0_step_into`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

/-- **The step into an event**: the data state behind the event at index `j + 1` (at a site of
the chain) follows a state at the pc of event `j` through the control step. -/
theorem w0_step_into_hub (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {e' : Event}
    (he' : X.get (g, j + 1) = some e') (hub : ∀ f, e'.kind ≠ .ub f) (hge : 103 ≤ e'.pc)
    (hv : W0Valid P.scale ((X.tr g).take (j + 1))) {s : Site}
    (hs : ∀ s' : Site, s'.pc = e'.pc → s' = s) (hin : innerSite s = true) :
    ∃ (f : Event) (c : Control.D) (d : D), X.get (g, j) = some f ∧ c.site.pc = f.pc ∧
      d.c.site = s ∧ Control.succ P L g (warpW L g) c f = some (some d.c) ∧
      (c.site = .arrS ∨ succOk c d.c = true) := by
  obtain ⟨st, hst, hslot, hpre, hI, hPrev, -⟩ :=
    followW hp hX hFw hw he' hub (w0_scale_rd hp) hv (j + 1) le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he' hst hub
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX he' hst hub
    have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : e'.pc = (thread P L g).pc (.inl b, n) := hpc'
    omega
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  have hsite : d.c.site = s := by
    exact hs _ hpc'.symm
  obtain ⟨hIW, hOk, -⟩ := hI d rfl
  have hok : d.ok = true := hOk (by rw [hsite]; exact hin)
  rcases hPrev d rfl j rfl with ⟨hsm, -⟩ | ⟨f, c, hf, hpcf, hsucc, hok'⟩
  · have h3 := hsite
    rw [hsm] at h3
    subst h3
    simp [innerSite, isStart] at hin
  · exact ⟨f, c, d, hf, hpcf, hsite, hsucc, hok' hok⟩

end Wg0

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
