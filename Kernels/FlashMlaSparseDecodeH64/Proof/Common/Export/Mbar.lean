-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows

@[expose] public section

/-! # Every mbarrier use, by role

`MbarRows P L X` bundles the mbarrier rows of all roles (`Iface/MbarRows/<Role>.lean`) and the
dispatch's `MbarRow.Place`; each field is the row its producer lane proves (Startup, Wg1, Tma,
Index, Place: lane A; Mma: lane B; Dequant: lane D; Wg0: lane W1), so a lane discharges its field
and no statement above changes.

`mbar_use`: every event of a launched lane that names an mbarrier is one of the uses of its
role's row (`MbarUse`), with the role's lane and pc condition. A theorem about who touches an
object takes the cases of `MbarUse` and compares the families. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

/-- **The mbarrier rows of every role.** -/
structure MbarRows (P : Params) (L : Launch) (X : Execution) : Prop where
  startup : MbarRow.Startup P L X
  wg1 : MbarRow.Wg1 P L X
  mma : MbarRow.Mma P L X
  tma : MbarRow.Tma P L X
  index : MbarRow.Index P L X
  dequant : MbarRow.Dequant P L X
  wg0 : MbarRow.Wg0 P L X
  place : MbarRow.Place P L X

/-- **The mbarrier uses of event `e` of lane `g` at index `k` on `l`**, by role. -/
inductive MbarUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | startup (hw : MbarRow.StartupAt e.pc) (h : MbarRow.StartupUse L X g k e l)
  | wg0 (hw : MbarRow.Wg0At L g e.pc) (h : MbarRow.Wg0Use L X g k e l)
  | mma (hw : MbarRow.MmaAt L g e.pc) (h : MbarRow.MmaUse L X g k e l)
  | tma (hw : MbarRow.TmaAt L g e.pc) (h : MbarRow.TmaUse L X g k e l)
  | index (hw : MbarRow.IndexAt L g e.pc) (h : MbarRow.IndexUse L X g k e l)
  | dequant (hw : MbarRow.DequantAt L g e.pc) (h : MbarRow.DequantUse L X g k e l)

/-- **Every mbarrier use is one of its role's row.** -/
theorem mbar_use {P : Params} {L : Launch} {X : Execution} (hR : MbarRows P L X) {g k : Nat}
    {e : Event} {l : Loc} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e l) : MbarUse L X g k e l := by
  rcases hR.place hg he hm with h | h | h | h | h | h | h
  · exact .startup h (hR.startup hg he h hm)
  · exact .wg0 h (hR.wg0 hg he h hm)
  · exact (hR.wg1 hg he h hm).elim
  · exact .mma h (hR.mma hg he h hm)
  · exact .tma h (hR.tma hg he h hm)
  · exact .index h (hR.index hg he h hm)
  · exact .dequant h (hR.dequant hg he h hm)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
