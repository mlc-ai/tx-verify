-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkAssembly
public import Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay
import Kernels.TmlFa4Fwd.Proof.MmaQkSetup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The two initial QK copies use the same key reply and distinct B registers. -/
def initialKeyPackFrame (l : Launch) (block : Fin 4) : List (Nat × Value) :=
  [(qkBReg block-5,b32 (firstKLow l)),(qkBReg block-1,b32 0x40004040),(1062,b32 12)]

/-- Two local moves initialize the low and high words of the initial key descriptor. -/
theorem initialKeyPackSeed (l : Launch) (g : Nat) (stage : Fin 2) :
    let block := initialQkBlock stage
    Seg kernel [] l g 2 (qkSetupPc block 0-2)
      [(2564,b32 (firstKLow l)),(1062,b32 12)]
      (qkSetupPc block 0) (initialKeyPackFrame l block) := by
  dsimp only
  fin_cases stage <;> intro s hs <;>
    simp only [initialKeyPackFrame,initialQkBlock,qkSetupPc,qkBReg,Fin.val_zero,
      Nat.reduceSub,↓reduceIte] at hs ⊢ <;>
    seg_fp hs using rfl

/-- The K-only operations at the end of a QK fragment's setup. -/
def initialKeyPackStart (block : Fin 4) (step : Fin 8) : Nat :=
  qkSetupPc block step + if step.val = 0 then 3 else 2

/-- The live register holding the low word immediately before the pack. -/
def initialKeyLowReg (block : Fin 4) (step : Fin 8) : Nat :=
  if step.val = 0 then qkBReg block-5 else qkBReg block-3

def initialKeyWordFrame (l : Launch) (block : Fin 4) (step : Fin 8) : List (Nat × Value) :=
  [(initialKeyLowReg block step,b32 (firstKLow l+qkFragment step/16)),
    (qkBReg block-1,b32 0x40004040),(1062,b32 12)]

/-- Four K fragments use each half of the tile, with a two-byte descriptor increment. -/
theorem initialKeyPackedWord (l : Launch) (step : Fin 8) :
    sharedDescriptorWord (kvStart l 0+qkFragment step) 16 =
      firstKLow l+qkFragment step/16+2^32*0x40004040 := by
  have hFrag : qkFragment step % 16 = 0 := by fin_cases step <;> decide
  unfold sharedDescriptorWord firstKLow
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

private theorem firstKWordBound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    firstKLow l+1030 < 2^32 := by
  have := hp.shared.2.1
  simp only [firstKLow,kvStart,show kvSlot 0 = 0 from rfl,Nat.mul_zero,Nat.add_zero]
  omega

/-- The nonzero fragment computes its K displacement before the adjacent Q pack. -/
theorem initialKeyAddLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (step : Fin 8) (hStep : step.val ≠ 0) :
    let block := initialQkBlock stage
    let start := initialKeyPackStart block step
    Seg kernel [] l g 1 start (initialKeyPackFrame l block)
      (start+1) (initialKeyWordFrame l block step) := by
  have hBound := firstKWordBound hp
  have hx : qkFragment step / 16 ≤ 1030 := by fin_cases step <;> decide
  have hAdd := keyAdd rfl (show firstKLow l+qkFragment step/16 < 2^32 by omega)
  dsimp only
  fin_cases stage <;> fin_cases step <;> try (exact (hStep rfl).elim)
  all_goals
    intro s hs
    simp only [initialKeyPackFrame,initialKeyPackStart,initialKeyWordFrame,initialKeyLowReg,
      initialQkBlock,qkSetupPc,qkBReg] at hs ⊢
    seg_fp hs using
      (simp only [qkFragment,Nat.reduceMod,Nat.reduceDiv,Nat.reduceMul,Nat.add_zero] at hAdd ⊢
       exact hAdd)

/-- The last local move joins the physical key descriptor's two words. -/
theorem initialKeyPackFragment {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (step : Fin 8) :
    let block := initialQkBlock stage
    let finish := qkSetupPc block step+qkFirstSetupCount step
    Seg kernel [] l g 1 (finish-1) (initialKeyWordFrame l block step) finish
      [(qkBReg block+step.val,b64 (sharedDescriptorWord (kvStart l 0+qkFragment step) 16)),
        (1062,b32 12)] := by
  have hBound := firstKWordBound hp
  have hx : qkFragment step / 16 ≤ 1030 := by fin_cases step <;> decide
  have hJoin := keyJoin (show firstKLow l+qkFragment step/16 < 2^32 by omega)
  have hWord := initialKeyPackedWord l step
  dsimp only
  fin_cases stage <;> fin_cases step <;> intro s hs <;>
    simp only [initialKeyWordFrame,initialKeyLowReg,initialQkBlock,qkSetupPc,
      qkFirstSetupCount,qkBReg,hWord] at hs ⊢ <;>
    seg_fp hs using exact hJoin

end
end PTX.Kernels.TmlFa4Fwd.Mma
