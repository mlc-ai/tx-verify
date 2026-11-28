-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows

@[expose] public section

/-! # Every named-barrier event, by role

`BarRows P L X` bundles the named-barrier rows of all roles (`Iface/BarRows/<Role>.lean`) and the
dispatch's `BarRow.Place`; each field is the row its producer lane proves (Startup, Wg1, Tma,
Index, Place: lane A; Mma: lane B; Dequant: lane D; Wg0: lane W1).

`bar_use`: every barrier event of a launched lane is one of the uses of its role's row
(`BarUse`), with the role's lane and pc condition. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

/-- **The named-barrier rows of every role.** -/
structure BarRows (P : Params) (L : Launch) (X : Execution) : Prop where
  startup : BarRow.Startup P L X
  wg0 : BarRow.Wg0 P L X
  wg1 : BarRow.Wg1 P L X
  mma : BarRow.Mma P L X
  tma : BarRow.Tma P L X
  index : BarRow.Index P L X
  dequant : BarRow.Dequant P L X
  place : BarRow.Place P L X

/-- **The barrier uses of event `e` of lane `g`**, by role. -/
inductive BarUse (L : Launch) (g : Nat) (e : Event) : Prop where
  | startup (hw : MbarRow.StartupAt e.pc) (hpc : e.pc = 97) (h : BarRow.Cta e)
  | wg0 (hw : MbarRow.Wg0At L g e.pc) (h : BarRow.Wg0Use L g e)
  | wg1 (hw : MbarRow.Wg1At L g e.pc) (h : BarRow.Everyone e 2604)
  | mma (hw : MbarRow.MmaAt L g e.pc) (h : BarRow.Everyone e 2160)
  | tma (hw : MbarRow.TmaAt L g e.pc) (h : BarRow.Everyone e 2330)
  | index (hw : MbarRow.IndexAt L g e.pc) (h : BarRow.Everyone e 2585)
  | dequant (hw : MbarRow.DequantAt L g e.pc) (h : BarRow.Everyone e 3610)

/-- **Every barrier event is one of its role's row.** -/
theorem bar_use {P : Params} {L : Launch} {X : Execution} (hR : BarRows P L X) {g k : Nat}
    {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hb : Execution.isBar e = true) : BarUse L g e := by
  rcases hR.place hg he hb with h | h | h | h | h | h | h
  · obtain ⟨hpc, hc⟩ := hR.startup hg he h hb
    exact .startup h hpc hc
  · exact .wg0 h (hR.wg0 hg he h hb)
  · exact .wg1 h (hR.wg1 hg he h hb)
  · exact .mma h (hR.mma hg he h hb)
  · exact .tma h (hR.tma hg he h hb)
  · exact .index h (hR.index hg he h hb)
  · exact .dequant h (hR.dequant hg he h hb)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
