-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvTrace
public import Kernels.TmlFa4Fwd.Proof.MmaElect
public import Lemmas.Flow.Join

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

def pvElection : Fin 4 → Fin 20
  | 0 => 5
  | 1 => 8
  | 2 => 15
  | 3 => 16

def pvSrcRegs : Fin 4 → Nat × Nat × Nat
  | 0 => (2570, 2569, 2595)
  | 1 => (2596, 2594, 2595)
  | 2 => (2613, 2611, 2612)
  | 3 => (2617, 2616, 2612)

/-- Inputs to the leader election and local packing of a V slot. -/
def pvEntryFacts (l : Launch) (block : Fin 4) (use phase : Nat) (accumulated : Bool) :
    List (Nat × Value) :=
  let s := pvSite block
  let src := pvSrcRegs block
  [(src.1, b32 (outputColumn s.stage)), (src.2.1, b32 (probabilityColumn s.stage)),
    (src.2.2, b32 (kvStart l use / 16 + 67108864)), (7206, b32 (if accumulated then 1 else 0)),
    ((waitSite (pvTailWait block)).base, b32 (pvTailAddress l block)),
    ((waitSite (pvTailWait block)).phase, b32 phase)]

/-- The election and its straight-line setup precede the first PV issue. -/
theorem pvEntrySites (block : Fin 4) :
    (electSite (pvElection block)).pc + 1 + 7 = pvPc block 0 ∧
      (electSite (pvElection block)).pred = (pvSite block).guard ∧
      (electSite (pvElection block)).result = none ∧
      1904 ≤ (electSite (pvElection block)).pc + 1 ∧ pvPc block 0 ≤ 2768 := by
  fin_cases block <;> decide

private theorem pvEntryWord (l : Launch) (use : Nat) :
    sharedDescriptorWord (kvStart l use + pvFragment 0) 16384 =
      kvStart l use / 16 + 67108864 + 2 ^ 32 * 0x40004040 := by
  unfold sharedDescriptorWord pvFragment
  rfl

/-- Assemble the physical PV issue words after the election. -/
theorem pvLocalSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (block : Fin 4) (use phase : Nat) (accumulated lead : Bool) :
    Seg kernel [] l g 7 ((electSite (pvElection block)).pc + 1)
      (((pvSite block).guard, .pred lead) :: pvEntryFacts l block use phase accumulated)
      (pvPc block 0) (pvIssueFrame l block use phase accumulated lead 0) := by
  let lo := kvStart l use / 16 + 67108864
  have hTag : lo < 2 ^ 32 := by
    have hs := hp.shared.2.1
    have hm : kvSlot use < 3 := Nat.mod_lt _ (by decide)
    dsimp only [lo, kvStart]
    omega
  have hPack : joinValue (b32 lo) (b32 0x40004040) =
      b64 (lo + 2 ^ 32 * 0x40004040) := by
    unfold b32 b64
    rw [Nat.mul_comm (2 ^ 32) 0x40004040]
    exact join_bits32 rfl rfl hTag (by decide)
  have hPack' : joinValue (b32 (kvStart l use / 16 + 67108864))
      (.bits 32 (truncBits 32 (BitVec.ofInt 64 1073758272))) =
      b64 (kvStart l use / 16 + 67108864 + 2 ^ 32 * 0x40004040) := hPack
  fin_cases block <;> cases accumulated <;> intro t ht <;>
    simp only [pvEntryFacts, pvIssueFrame, pvCarry, pvEntryWord, List.cons_append,
      List.nil_append, Fin.val_zero, ↓reduceIte] at ht ⊢ <;>
    seg_fp ht using first | exact hPack' | rfl

end
end PTX.Kernels.TmlFa4Fwd.Mma
