-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqClass
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.StageEpi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Bar9
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.AsyncDq
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Store
import Lemmas.TensorStore.SourceBytes
import Lemmas.TensorStore.StoreWrite

@[expose] public section

/-! # An output slot's byte is the staging store's byte

In a complete execution, the byte a tensor store writes at a slot is the byte it read from its
shared source (`TensorStore.CopyOk`), and the read returns the byte of the one staging store of
warpgroup 0 covering it: the staging store is before the read (`out_pub_stage`), a dequant lane's
store of the byte is before the staging store (`dq_stage`), and a second staging store of the
byte is the first (`wg0_stage_once`), so the staging store is the last write ordered before the
read (`Consistent.store_read_byte`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
  (hnu : ¬ HasUb X) (hBar : BarRows P L X) (hO : OutRows P L X)
include hp hX hFw hR hI hB hN hnu hBar hO

/-- **A tensor store's slot byte is a staging store's byte**: the slot `(x, y, z)` of the
store at `(g, k)` has a global byte `lw` and reads `lsrc`; the store writes there the byte `b`
that the one staging store of warpgroup 0 covering `lsrc` wrote (`some b = wbyte ac bs lsrc`). -/
theorem out_slot_byte (hC : Complete L X) {g k pcT addr x y z : Nat} {s : TensorStore.Spec}
    {lsrc lw : Loc} (hT : X.get (g, k) = some ⟨pcT, .tensorStore addr s⟩)
    (hat : Wg0At L g pcT) (hrl : TensorStore.readLoc s x y z = some lsrc)
    (hwl : TensorStore.writeLoc s x y z = some lw) :
    ∃ b gS kS pcS ac bs, X.MemWrites (.async (g, k) (.write (.store x y z)))
        ⟨lw, 1, false, false, .cta, 0, false⟩ [b] ∧
      X.get (gS, kS) = some ⟨pcS, .wr ac bs⟩ ∧ Wg0At L gS pcS ∧ MemRow.Wg0Stage L gS pcS ac ∧
      ac.Covers lsrc ∧ some b = wbyte ac bs lsrc := by
  have hi : X.TensorStoreIssue (g, k) addr s := ⟨pcT, hT⟩
  obtain ⟨-, -, hred⟩ := tensorStoreForm hX hi
  obtain ⟨o, b, ho, hwb, hmw⟩ := Complete.store_write hX hC hi hwl
  obtain ⟨c0, hc0, -, hsp, hcta, hlo, hhi⟩ := wg0_store_read hp hX hFw hT hat rfl hrl
  obtain ⟨hw2, -, -⟩ := tensor_store_origin hp hX hFw hnu hi
  have hloc : MemRow.LocIn L (g / L.block) (.dequant 1) lsrc := by
    refine ⟨hsp, hcta, ?_, ?_⟩ <;> simp only [Region.lo, Region.size] <;>
      (have ho' : MemRow.wg0OutOff c0 ≤ 40960 := by
        rcases (by omega : c0 = 0 ∨ c0 = 1 ∨ c0 = 2 ∨ c0 = 3) with rfl | rfl | rfl | rfl <;>
          decide
       omega)
  have hrl0 := hrl
  unfold TensorStore.readLoc at hrl
  obtain ⟨slot, hslot, hsl⟩ := Option.map_eq_some_iff.mp hrl
  have hxyj : slot.1.val = x ∧ slot.2.1.val = y ∧ slot.2.2.val = z := by
    unfold TensorTransfer.slotAt at hslot
    split_ifs at hslot
    simp only [Option.some.injEq] at hslot
    subst hslot
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨yw, iw, bw, bsw, hwr, hw4, hcw, hcaus⟩ := out_pub_stage hp hX hBar hO hi slot
  have hacc : X.Access (yw, iw) bw true := Or.inr (Or.inl ⟨bsw, hwr, rfl⟩)
  rw [hsl] at hcw hcaus
  obtain ⟨hlsp, hlcta, hllo, hlhi⟩ := hloc
  have hcta' := (access_below hp hX hFw hacc hcw hlsp).1
  obtain ⟨-, pcw, bsw', hget, hcls⟩ := access_dequant hp hX hFw hacc hcw
    ⟨hlsp, hcta', hllo, hlhi⟩
  rcases hcls with ⟨hatw, -, hstw⟩ | hdq
  swap
  · have := hdq.1
    omega
  obtain ⟨-, hbs⟩ : (X.get (yw, iw) = some ⟨pcw, .wr bw bsw'⟩) ∧ bsw' = bsw := by
    obtain ⟨pc', h'⟩ := hwr
    rw [hget] at h'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at h'
    exact ⟨hget, h'.2.2⟩
  subst hbs
  refine ⟨b, yw, iw, pcw, bw, bsw', hmw, hget, hatw, hstw, hcw, ?_⟩
  have hspec : o.spec = s := by
    obtain ⟨⟨addr', pc', he'⟩, -, -⟩ := hX.store (g, k) o ho
    rw [hT] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at he'
    exact he'.2.2.symm
  rw [← hspec] at hrl0 hred
  refine Consistent.store_read_byte hX ho hred hwb hrl0
    (w := .thread (yw, iw)) (dst := bw) (bs := bsw') ⟨.inl ⟨pcw, hget⟩, hcw, ?_, ?_⟩
  · rw [← hsl] at hrl0
    obtain ⟨rfl, rfl, rfl⟩ := hxyj
    exact hcaus
  · intro w' fp bs' hw' hc'
    have hI' := hw'.intent
    have hc2 : X.Intent w' fp true := hI'
    cases dq_classify hp hX hFw hc2 hc' ⟨hlsp, hlcta, hllo, hlhi⟩ with
    | dq hW2 hat2 hcov2 hc2' =>
      exact .inr (.inl (dq_stage hp hX hFw hR hI hB hN hW2 hat2 hcov2 hlsp
        (hc2'.trans (hcta.symm.trans hcta')) hget hatw hstw hcw))
    | tload hr => exact absurd hr (by decide)
    | stage hS2 hat2 _ hst2 hcov2 _ =>
      obtain ⟨rfl, rfl⟩ := wg0_stage_once hp hX hFw hatw.1 hat2.1 hget hS2 hstw hst2 hcw hcov2
      exact .inl rfl

end

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
