-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Bar9
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.AsyncDq
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce

@[expose] public section

/-! # A staging store is before the tensor store that reads its byte

The output publication (`out_pub_stage`) gives, for a byte of an output tensor store's source
box, a staging store made by a thread of warpgroup 0 that is ordered before the read. Any staging
store of warpgroup 0 covering that byte is that store (`wg0_stage_once`), so it is before the
read (`stage_store_order`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A staging store covering a byte of a tensor store's source is before the store's read.** -/
theorem stage_store_order (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) (hO : OutRows P L X)
    {g k gS kS pcT pcS addr x y j : Nat} {s : TensorStore.Spec} {ac : Acc} {bs : List Byte}
    {l : Loc} (hT : X.get (g, k) = some ⟨pcT, .tensorStore addr s⟩)
    (hrl : TensorStore.readLoc s x y j = some l)
    (hS : X.get (gS, kS) = some ⟨pcS, .wr ac bs⟩) (hatS : MbarRow.Wg0At L gS pcS)
    (hst : MemRow.Wg0Stage L gS pcS ac) (hcov : ac.Covers l)
    (hl : MemRow.LocIn L (g / L.block) (.dequant 1) l) :
    ByteCausality L X l (.thread (gS, kS)) (.async (g, k) (.read (.store x y j))) := by
  unfold TensorStore.readLoc at hrl
  obtain ⟨slot, hslot, rfl⟩ := Option.map_eq_some_iff.mp hrl
  have hxyj : slot.1.val = x ∧ slot.2.1.val = y ∧ slot.2.2.val = j := by
    unfold TensorTransfer.slotAt at hslot
    split_ifs at hslot
    simp only [Option.some.injEq] at hslot
    subst hslot
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨rfl, rfl, rfl⟩ := hxyj
  obtain ⟨yw, iw, b, bs', hwr, hw4, hc, hb⟩ := out_pub_stage hp hX hR hO ⟨pcT, hT⟩ slot
  have hacc : X.Access (yw, iw) b true := Or.inr (Or.inl ⟨bs', hwr, rfl⟩)
  obtain ⟨hls, -, hlo, hhi⟩ := hl
  have hcta := (access_below hp hX hFw hacc hc hls).1
  obtain ⟨-, pcw, bsw, hget, hcls⟩ := access_dequant hp hX hFw hacc hc
    ⟨hls, hcta, hlo, hhi⟩
  rcases hcls with ⟨hatw, -, hstw⟩ | hdq
  · obtain ⟨rfl, rfl⟩ := wg0_stage_once hp hX hFw hatw.1 hatS.1 hget hS hstw hst hc hcov
    exact hb
  · have := hdq.1
    omega

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
