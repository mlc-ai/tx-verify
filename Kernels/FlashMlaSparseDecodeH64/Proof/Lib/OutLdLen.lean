-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemLoad

@[expose] public section

/-! # The output loads return 64 words

The four chunk loads of the epilogue (pcs 1201, 1361, 1519, 1676) are `.32x32b`, unreduced, of
64 registers, so their events return 64 words. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **Static check**: the epilogue's chunk loads are `.32x32b`, unreduced, of 64 registers. -/
theorem code_outLd : [1201, 1361, 1519, 1676].all (fun pc => match kernel.code[pc]? with
    | some ins => match ins.op with
      | .tcLd ds _ .s32x32b none => decide (ds.length = 64)
      | _ => false
    | none => false) = true := by
  decide +kernel

/-- **An epilogue chunk load returns 64 words.** -/
theorem outLdLen (hpre : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId} {e : Event}
    (he : X.get i = some e) {a : Nat} {vals : List Value} {sh : TcShape}
    (hk : e.kind = .tc (.ld a vals sh)) (hpc : e.pc ∈ [1201, 1361, 1519, 1676]) :
    vals.length = 64 := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨ins, ds, ta, sh', red, hc, hop, hl⟩ := Flow.get_tcLd_len hb hX he hk
  have h := List.all_eq_true.mp code_outLd e.pc hpc
  simp only [hc] at h
  rw [hop] at h
  cases sh' <;> cases red <;> simp at h
  rw [hl rfl (by intro s hs; cases hs)]
  exact h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
