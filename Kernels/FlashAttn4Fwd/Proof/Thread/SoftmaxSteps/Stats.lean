-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxBase
public import Lemmas.Flow.ParamObject

@[expose] public section

/-! # The statistics polls that end a tile

A successful poll after a tile runs its row-sum tree and, entering the loop, loads the scale
parameter again (`ld.param`): `ld_scale` takes that load as one step, from the launch's word
(`Pre.paramScale`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The load of the scale parameter as one step. -/
theorem ld_scale {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    {d : D} {t : TState} {pc dst : Nat} {ty : DType}
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param (param "8") false, 0⟩, dsts := [some dst] }⟩)
    (h : At t pc (factsAt L g pc d)) (hv : valueOf L g d dst = scaleV L)
    (hd : dst ∉ Flow.live pc) (hl : ∀ x ∈ Flow.live (pc + 1), x = dst ∨ x ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc) (hw : ty.width = 32 := by rfl)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param (param "8") false, 0⟩, dsts := [some dst] } = some .threadMove := by
      rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsAt L g (pc + 1) d) := by
  obtain ⟨bits, -, hp, -⟩ := hpre.paramScale
  refine ⟨_, run_local hc rfl h
    (exec_ldParam hp (Assumption.SegFreePc.of_eq h.1 hsf) asms_localRule_none hw hr), ?_⟩
  have h1 := At.set (r := dst) (v := .bits 32 (truncBits 32 (BitVec.ofNat 64 bits))) h
    (facts_ne hd)
  refine At.mono h1 (holds_of_pointwise fun x hx => ?_)
  rcases hl x hx with rfl | hx'
  · rw [hv, scaleV, hp]
    simp [PTX.next, setReg]
  · exact holds_mem h1.2.2.2.2 (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x, hx', rfl⟩))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
