-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
public import Lemmas.Flow.TcLdLen

@[expose] public section

/-! # The kernel's Tensor Memory loads

* `code_ldShape` (static): every `tcgen05.ld` of the kernel is `.32x32b`, without reduction, with
  at most 64 destination registers (the score loads are `.x32` at `400 + 32 k`, the chunk loads
  `.x64` at `64 c`: the largest column loaded is `432 + 63 < 512`);
* `ldLen`: so a load event of a consistent execution returns at most 64 words;
* `dataCell`: register `j` of a `32x32b` access of warpgroup 0 at column `a` of thread `g` is in
  `g`'s CTA, in lane `g % 384`, at column `a + j`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **Static check**: every `tcgen05.ld` is `.32x32b`, unreduced, of at most 64 registers. -/
theorem code_ldShape : kernel.code.all (fun ins => match ins.op with
    | .tcLd ds _ .s32x32b none => decide (ds.length ≤ 64)
    | .tcLd .. => false
    | _ => true) = true := by
  decide +kernel

/-- **A Tensor Memory load event returns at most 64 words.** -/
theorem ldLen (hpre : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId} {e : Event}
    (he : X.get i = some e) {a : Nat} {vals : List Value} {sh : TcShape}
    (hk : e.kind = .tc (.ld a vals sh)) : vals.length ≤ 64 := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨ins, ds, ta, sh', red, hc, hop, hl⟩ := Flow.get_tcLd_len hb hX he hk
  have h := List.all_eq_true.mp code_ldShape ins (List.mem_of_getElem? hc)
  rw [hop] at h
  cases sh' <;> cases red <;> simp at h
  rw [hl rfl (by intro s hs; cases hs)]
  exact h

/-- **Static check**: the score loads (pcs 278, 280, 283, 285) are `.32x32b`, unreduced, of 32
registers. -/
theorem code_scoreLd : [278, 280, 283, 285].all (fun pc => match kernel.code[pc]? with
    | some ins => match ins.op with
      | .tcLd ds _ .s32x32b none => decide (ds.length = 32)
      | _ => false
    | none => false) = true := by
  decide +kernel

/-- **A score load returns 32 words.** -/
theorem scoreLdLen (hpre : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId} {e : Event}
    (he : X.get i = some e) {a : Nat} {vals : List Value} {sh : TcShape}
    (hk : e.kind = .tc (.ld a vals sh)) (hpc : e.pc ∈ [278, 280, 283, 285]) :
    vals.length = 32 := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨ins, ds, ta, sh', red, hc, hop, hl⟩ := Flow.get_tcLd_len hb hX he hk
  have h := List.all_eq_true.mp code_scoreLd e.pc hpc
  simp only [hc] at h
  rw [hop] at h
  cases sh' <;> cases red <;> simp at h
  rw [hl rfl (by intro s hs; cases hs)]
  exact h

/-- **The cell of register `j` of a `32x32b` access of warpgroup 0 at column `a`.** -/
theorem dataCell (hpre : Pre P L mem0) {g a j : Nat} (hw : MbarRow.warp L g < 4)
    (ha : a < 65536) :
    (tcDataCell L g .s32x32b a j).cta = g / L.block ∧
      (tcDataCell L g .s32x32b a j).lane = g % 384 ∧
      (tcDataCell L g .s32x32b a j).column = a + j := by
  have hx := tidOf_x_eq hpre g
  unfold MbarRow.warp at hw
  rw [hx] at hw
  have hb := hpre.block
  simp only [tcDataCell, TcShape.base, TcShape.laneIn, TcShape.columnIn, TcShape.lanes,
    laneBase, PTX.laneOf, chunkOffset, hb]
  exact ⟨trivial, by omega, by omega⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
