-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputBytes
public import Lemmas.Step.MmaVisible
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Visible
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Visible
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Lib.TmemCells
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Lemmas.Flow.WriteBytes
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMAs' shared operand bytes have visible writes (`operandVisible`)

Operand A of a QK MMA is the Q stage's bytes (`q_visible`), operand B of every MMA a K/V slot's
(`kv_visible`); the MMA warp's MMAs are issued by one lane. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem sized_code :
    kernel.code.all (fun i => !writeOp i.op || sizedWrite i.op) = true := by
  decide +kernel

/-- A covering write has a byte at the location. -/
theorem wbyte_of_write (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {w : Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hw : X.MemWrites w a bs) (hc : a.Covers l) : ∃ v, wbyte a bs l = some v := by
  have hlen : bs.length = a.size → ∃ v, wbyte a bs l = some v := fun h => by
    obtain ⟨-, -, h1, h2⟩ := hc
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  apply hlen
  rcases w with ⟨g, k⟩ | ⟨i, part⟩
  · rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    · rcases get_source hX he with ⟨_, hu⟩ | ⟨t, ins, o, -, hcode, hf⟩
      · cases hu
      have h := List.all_eq_true.mp sized_code ins (List.mem_of_getElem? hcode)
      rw [fires_write_op hf rfl] at h
      exact fires_write_length hf rfl (by simpa using h)
    · exact (no_rmw hX he).elim
  · cases part
    case async.writeStore x y z =>
      obtain ⟨_, _, b, -, -, -, -, hs, rfl, -⟩ := hw
      rw [hs]; rfl
    case async.writeLoad x y z =>
      obtain ⟨_, _, b, -, -, -, -, hs, rfl, -⟩ := hw
      rw [hs]; rfl
    case async.writeCopy =>
      obtain ⟨s, hcp, hwh, rfl, hb⟩ := hw
      obtain ⟨s', hs', hok⟩ := hX.tma.1 i ⟨.write .copy, by
        simp only [AsyncCopy.present, hb, Option.isSome_some]⟩
      obtain ⟨pc, he⟩ := hcp
      have hss : s' = s := by
        simp only [AsyncCopy.issuedBy, he] at hs'
        exact (Option.some.inj hs').symm
      subst hss
      have hshape := actualCopyShape hX ⟨pc, he⟩
      have h1 := hok.2.2.1 bs hb
      rw [hshape.whole] at h1
      simp only [AsyncCopy.sourceBytes, hshape.noData, Option.map_eq_some_iff] at h1
      obtain ⟨rs, hrs, rfl⟩ := h1
      have h2 := (hok.2.1 rs hrs).2
      have h3 := hok.1
      simp only [List.length_append, List.length_replicate]
      omega
    case async.writeElem j =>
      obtain ⟨s, hcp, hj, -⟩ := hw
      simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets,
        (copy_row hp hX hFw hcp).2.whole] at hj
    case async.writeCta =>
      obtain ⟨_, _, ⟨pc, hi⟩, -⟩ := hw
      exact (no_clc hp hX hFw i.1 i.2 pc _ _ hi).elim
    all_goals exact hw.elim

theorem operandVisible (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hIn : InputsUnwritten p X) : OperandVisible L X := by
  refine ⟨?_, fun i d sp acc mask hi _ => ?_⟩
  · rintro ⟨g, k⟩ ⟨h, k'⟩ ⟨d, s, acc, mask, hi⟩ ⟨d', s', acc', mask', hi'⟩ hsw
    have hw := (Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩).1
    have hw' := (Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hi'⟩).1
    exact Mma.mma_lane hp hX hw hw' hsw.1.2.2 hi hi'
  obtain ⟨g, k⟩ := i
  obtain ⟨hw12, st, u, j, hst, h⟩ := Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩
  refine ⟨?_, fun isB idx l hf => ⟨?_, fun w a bs hw hc _ => wbyte_of_write hp hX hFw hw hc⟩⟩
  · rcases h with h | h
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hi; exact Tm.qkDsc_valid
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hi; exact Tm.pvDsc_valid
  · have hint : X.Intent (.async (g, k) (.mmaRead isB idx)) { loc := l, size := 1 } false :=
      ⟨rfl, rfl, hf⟩
    have hcov : AsyncCovers X (g, k) (.mmaRead isB idx) l :=
      ⟨_, _, hint, rfl, rfl, le_refl _, Nat.lt_succ_self _⟩
    have hsh := sh_intent hp hX hFw hint (Execution.mmaFootprint_shared hf)
    cases hsh with
    | mmaA hst' h' hz ho hl =>
      simp only at hl
      subst hl
      obtain ⟨w, a, bs, h1, h2, h3⟩ := q_visible hp hX hFw hIn h' hst' ho hcov
      exact ⟨w, a, bs, h1, h2, .direct h3⟩
    | @mmaB _ _ _ _ st' u' j'' off t hst' h' hz ho hl =>
      simp only at hl
      subst hl
      obtain ⟨w, a, bs, h1, h2, h3⟩ := kv_visible hp hX hFw ⟨st', u', j'', h'⟩ ho hcov
      exact ⟨w, a, bs, h1, h2, .direct h3⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
