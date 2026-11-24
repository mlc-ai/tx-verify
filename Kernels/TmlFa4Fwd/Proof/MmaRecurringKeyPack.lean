-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaInitialKeyPack
import Kernels.TmlFa4Fwd.Proof.MmaQkSetup
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheBroadcasts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Thread (keyDescriptorLow)

noncomputable section

/-- The two recurring QK blocks copy the current ring descriptor into their own registers. -/
def recurringKeyBlock (stage : Fin 2) : Fin 4 := ⟨stage.val+2,by have := stage.isLt; omega⟩

/-- The packed B base's low word and constant high word are staged per block. -/
def recurringKeyPackFrame (l : Launch) (block : Fin 4) (use : Nat) : List (Nat × Value) :=
  [(qkBReg block-5,b32 (keyDescriptorLow l use)),
    (qkBReg block-1,b32 0x40004040),(1062,b32 12),(2600,b32 (keyDescriptorLow l use))]

theorem recurringKeyPackSeed (l : Launch) (g : Nat) (stage : Fin 2) (use : Nat) :
    let block := recurringKeyBlock stage
    Seg kernel [] l g 2 (qkSetupPc block 0-2)
      [(2600,b32 (keyDescriptorLow l use)),(1062,b32 12)]
      (qkSetupPc block 0) (recurringKeyPackFrame l block use) := by
  dsimp only
  fin_cases stage <;> intro s hs <;>
    seg_fp hs using rfl

/-- The low and high words immediately before the recurring key pack. -/
def recurringKeyWordFrame (l : Launch) (block : Fin 4) (step : Fin 8) (use : Nat) :
    List (Nat × Value) :=
  [(initialKeyLowReg block step,b32 (keyDescriptorLow l use+qkFragment step/16)),
    (qkBReg block-1,b32 0x40004040),(1062,b32 12),(2600,b32 (keyDescriptorLow l use))]

private theorem recurringKeyPackedWord (l : Launch) (step : Fin 8) (use : Nat) :
    sharedDescriptorWord (kvStart l use+qkFragment step) 16 =
      keyDescriptorLow l use+qkFragment step/16+2^32*0x40004040 := by
  have hFrag : qkFragment step % 16 = 0 := by fin_cases step <;> decide
  unfold sharedDescriptorWord keyDescriptorLow
  omega

private theorem keyAdd {lo add : Nat} {imm : Int} (hImm : imm = (add : Int))
    (h : lo+add < 2^32) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 lo) +
        truncBits 32 (BitVec.ofInt 64 imm))) = b32 (lo+add) := by
  unfold b32
  rw [hImm,BitVec.ofInt_natCast,truncBits_ofNat (by omega : lo < 2^32) (by decide),
    truncBits_ofNat (by omega : add < 2^32) (by decide),← BitVec.ofNat_add,
    truncBits_ofNat h (by decide)]

private theorem keyJoin {lo : Nat} (h : lo < 2^32) :
    joinValue (b32 lo) (b32 0x40004040) = b64 (lo+2^32*0x40004040) := by
  unfold b32 b64
  rw [Nat.mul_comm (2^32) 0x40004040]
  exact join_bits32 rfl rfl h (by decide)

private theorem recurringKWordBound {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (use : Nat) :
    keyDescriptorLow l use+1030 < 2^32 := by
  have := hp.shared.2.1
  have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
  unfold keyDescriptorLow kvStart
  omega

/-- The nonzero fragment computes its K displacement before the adjacent Q pack. -/
theorem recurringKeyAddLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (step : Fin 8) (use : Nat) (hStep : step.val ≠ 0) :
    let block := recurringKeyBlock stage
    let start := initialKeyPackStart block step
    Seg kernel [] l g 1 start (recurringKeyPackFrame l block use)
      (start+1) (recurringKeyWordFrame l block step use) := by
  have hBound := recurringKWordBound hp use
  have hx : qkFragment step / 16 ≤ 1030 := by fin_cases step <;> decide
  have hAdd := keyAdd rfl (show keyDescriptorLow l use+qkFragment step/16 < 2^32 by omega)
  dsimp only
  fin_cases stage <;> fin_cases step <;> try (exact (hStep rfl).elim)
  all_goals
    intro s hs
    simp only [recurringKeyPackFrame,initialKeyPackStart,recurringKeyWordFrame,initialKeyLowReg,
      recurringKeyBlock,qkSetupPc,qkBReg] at hs ⊢
    seg_fp hs using
      (simp only [qkFragment,Nat.reduceMod,Nat.reduceDiv,Nat.reduceMul,Nat.add_zero] at hAdd ⊢
       exact hAdd)

/-- The last local move joins the physical key descriptor's two words. -/
theorem recurringKeyPackFragment {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (step : Fin 8) (use : Nat) :
    let block := recurringKeyBlock stage
    let finish := qkSetupPc block step+qkFirstSetupCount step
    Seg kernel [] l g 1 (finish-1) (recurringKeyWordFrame l block step use) finish
      [(qkBReg block+step.val,b64 (sharedDescriptorWord (kvStart l use+qkFragment step) 16)),
        (1062,b32 12),(2600,b32 (keyDescriptorLow l use))] := by
  have hBound := recurringKWordBound hp use
  have hx : qkFragment step / 16 ≤ 1030 := by fin_cases step <;> decide
  have hJoin := keyJoin (show keyDescriptorLow l use+qkFragment step/16 < 2^32 by omega)
  have hWord := recurringKeyPackedWord l step use
  dsimp only
  fin_cases stage <;> fin_cases step <;> intro s hs <;>
    simp only [recurringKeyWordFrame,initialKeyLowReg,recurringKeyBlock,qkSetupPc,
      qkFirstSetupCount,qkBReg,hWord] at hs ⊢ <;>
    seg_fp hs using exact hJoin

end
end PTX.Kernels.TmlFa4Fwd.Mma
