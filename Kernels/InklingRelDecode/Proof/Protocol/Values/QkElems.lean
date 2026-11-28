-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkResults
public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvElement
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Protocol.Values.QkB

@[expose] public section

/-! # The B elements of the QK issues, named

The B element of a QK issue is the cache element of its block (the round of the issue), step and
position (`qk_b_elem`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX

/-- The step index of the QK issue at a program counter. -/
def qkStep (pc : Nat) : Nat := [2483, 2486, 2488, 2490, 2492, 2494, 2496, 2498].idxOf pc

theorem qkStep_qkIssue : ∀ j : Fin 8, qkStep (Lib.qkIssue j) = j.val := by decide

/-- The step of the QK issue `i`. -/
def qkStepOf (X : Execution) (i : EvId) : Nat := ((X.get i).map (fun e => qkStep e.pc)).getD 0

/-- The B element of the QK issue `i` at row `row`, column `k`. -/
noncomputable def qkB (Q : Params) (L : Launch) (X : Execution) (i : EvId) (row k : Nat) : ℝ :=
  kvElem Q L (i.1 / L.block) (pollRound 2462 ((X.tr i.1).take i.2) - 1) 0 (row / 64)
    (qkStepOf X i / 4) (16 * (qkStepOf X i % 4) + k) (row % 64)

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The `Eb` hypothesis of `ld_s_real`.** -/
theorem qk_b_ideal (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {i d s acc mask ops row k} (hq : QkIssue X i) (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (hrow : row < 128) (hk : k < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok (qkB Q L X i row k) := by
  obtain ⟨g, k0⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨pc', d', s', acc', mask', he', j, hj⟩ := hq
  obtain ⟨rfl, -⟩ := Event.mk.inj (Option.some.inj (he.symm.trans he'))
  obtain ⟨b, -, hb, -⟩ := Mma.Export.qk_block hp hX hf base he ⟨j, hj⟩
  have := qk_b_elem hp hX hf rows init words hu nub form base he hops hj hrow hk hb
  simp only [qkB, qkStepOf, he, Option.map_some, Option.getD_some, hj, qkStep_qkIssue]
  rw [this]
  simp [hb]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
