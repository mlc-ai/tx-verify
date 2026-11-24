-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.TileNum
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Lemmas.Flow.Arith32WordW

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Flow.Arith32
set_option maxRecDepth 20000

/-- The end of the packed bias window of the first 128-row stage, in key blocks. -/
def stageZeroBlocks (p : Params) (b t : Nat) : Nat :=
  min ((p.kLength b+127)/128) ((256*t+p.kLength b-p.qLength b+255)/128)

/-- The loader's signed bias displacement is zero or minus one. It is minus one
when the first stage's bias window ends one block before the CTA's. -/
theorem bias_gap {p L m g v b} (hp : Pre p L m) (hN : TileNum p L g v (setup p L g v) b) :
    let t := (Epilogue.assignedCoordinates p b (g/L.block)).1
    let n := tileBlocks p b t
    let n0 := stageZeroBlocks p b t
    (n0 = n ∨ n0+1=n) ∧
      (setup p L g v).r29 = if n0<n then i32 (-1) else i32 0 := by
  let t := (Epilogue.assignedCoordinates p b (g/L.block)).1
  let n := tileBlocks p b t
  let n0 := stageZeroBlocks p b t
  change (n0=n ∨ n0+1=n) ∧ _
  have alt : n0=n ∨ n0+1=n := by dsimp [n,n0,tileBlocks,stageZeroBlocks]; omega
  refine ⟨alt,?_⟩
  have raw : (setup p L g v).r29 = sub32
      (min32 (Mma.ceil128 v.ukw) (Mma.ceil128 (addi
        (add32 (add32 (setup p L g v).r741 v.ukw) (sub32 v.sc.c0 v.sc.c1)) 128)))
      (setup p L g v).r28 := rfl
  obtain ⟨hle,hk,hsize⟩ := hp.lengths b hN.batch
  have hrow := (Epilogue.assignedCoordinates_valid hp hN.lo hN.hi).1
  have hb := hN.batch
  have hQ := hp.qOffset_le_total (show b+1≤p.batch by omega)
  obtain ⟨_,_,_,_,_,total⟩ := hp.shape
  have len : p.qLength b = p.qOffset (b+1)-p.qOffset b := rfl
  have erow : 256*t < p.qLength b := hrow
  have add : add32 (add32 (W (256*t)) (W (p.kLength b)))
      (sub32 (W (p.qOffset b)) (W (p.qOffset (b+1)))) = W (256*t+p.kLength b-p.qLength b) := by
    rw [add32_W (by omega),sub32_Wm,add32_Wm]
    exact congrArg W (by omega)
  rw [raw,hN.row,hN.ukw,hN.c0,hN.c1,hN.r28,add,show (128 : Int) = ((128 : Nat) : Int) from rfl,
    addi_W (by decide) (by omega), show Mma.ceil128 (W (p.kLength b)) = _ from cdiv_W (by omega),
    show Mma.ceil128 (W (256*t+p.kLength b-p.qLength b+128)) = _ from cdiv_W (by omega),
    min32_W (by omega) (by omega)]
  change sub32 (W n0) (W n) = if n0<n then _ else _
  have small : n<2^31 := by dsimp [n,tileBlocks]; omega
  rw [sub32_Wm]
  rcases alt with same | succ
  · rw [ite_eq_right (by omega)]
    change W _ = W 0
    exact congrArg W (by omega)
  · rw [ite_eq_left (by omega)]
    change W _ = W 4294967295
    exact congrArg W (by omega)

end PTX.Kernels.TmlFa4Fwd.Proof.Loader
