-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkBase

@[expose] public section

/-!
# The warp collectives of the program have immediate operands

Every warp collective of the program (`shfl.sync`, `elect.sync`, `bar.warp.sync`) names its lane
operands and its member mask by immediates, and every member mask is `-1` (all 32 lanes):
`wImm` checks this of one instruction, and `kernel_wImm` of the instruction at every synchronizing
position (`syPcs`, which lists every warp collective, `kernel_syPcs`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

/-- A 32-bit immediate operand as the value `readBits` gives. -/
def tb (v : Int) : Nat := (truncBits 32 (BitVec.ofInt 64 v)).toNat

/-- The warp collective's lane operands and member mask are immediates, and the mask names every
lane. -/
def wImm (w : WarpInstr) : Bool :=
  match w.kind, w.srcs, w.mask with
  | .shfl _, [_, .imm _, .imm _], some (.imm _) => true
  | .elect, _, some (.imm mk) => tb mk == 4294967295
  | .barWarp, _, some (.imm mk) => tb mk == 4294967295
  | _, _, _ => false

/-- `wImm` for a warp collective, `true` for every other operation. -/
def opImm : Op → Bool
  | .warp w => wImm w
  | _ => true

theorem kernel_wImm : syPcs.all (fun pc => match kernel.code[pc]? with
    | some ins => opImm ins.op
    | none => true) = true := by
  decide +kernel

/-- **Every warp collective of the program has immediate operands and a full mask.** -/
theorem wImm_of_code {pc : Nat} {ins : Instr} {w : WarpInstr} (hc : kernel.code[pc]? = some ins)
    (hw : ins.op = .warp w) : wImm w = true := by
  have hm : pc ∈ syPcs := OpPcsFast.mem kernel_syPcs hc (by rw [hw]; rfl)
  have h := List.all_eq_true.mp kernel_wImm pc hm
  rw [hc] at h
  simpa [opImm, hw] using h

end PTX.Kernels.InklingRelDecode.Proof.Lk
