-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.MaskRow
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Diagonal
import Kernels.TmlFa4Fwd.Proof.Lib.BiasRounds
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.TileGeom
import Lemmas.Flow.Arith32WordW
import Kernels.TmlFa4Fwd.Proof.Lib.Interval

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow.Arith32

private theorem count_signed (x : BitVec 64) : toSigned 32 x = S x := by
  simp only [S,toSigned,r32,truncBits,BitVec.toNat_ofNat]
  split <;> split <;> omega

private theorem signed_W {n : Nat} (h : n<2^31) : S (W n) = n := by
  rw [← count_signed,toSigned_W h]

private theorem key_test (n c j k : Nat) :
    decide ((32*c+j : Nat) < (k : Int)-128*((n-1 : Nat) : Int)) =
      decide (128*(n-1)+32*c+j<k) := by
  simp only [decide_eq_decide]
  omega

private theorem block_count {a z k r : Nat} (hz : a≤z) (hK : z-a≤k)
    (hr : r<z-a) (_hb : z<2^30) (hk : k+256<2^31) :
    min32 (Mma.ceil128 (W k)) (Mma.ceil128 (addi
      (add32 (add32 (W r) (W k)) (sub32 (W a) (W z))) 256)) =
      W (min ((k+127)/128) ((r+k-(z-a)+383)/128)) := by
  have hsum : add32 (add32 (W r) (W k)) (sub32 (W a) (W z)) = W (r+k-(z-a)) := by
    rw [add32_W (by omega),sub32_Wm,add32_Wm]
    congr 1
    omega
  rw [hsum,show (256 : Int) = ((256 : Nat) : Int) from rfl,addi_W (by decide) (by omega),
    show Mma.ceil128 (W k) = _ from Loader.cdiv_W (by omega),
    show Mma.ceil128 (W (r+k-(z-a)+256)) = _ from Loader.cdiv_W (by omega),
    min32_W (by omega) (by omega)]

private theorem previous_offset {n : Nat} (hn : 0<n) (h : 128*(n-1)<2^31) :
    shl (maxi (addi (W n) (-1)) 0) 7 = W (128*(n-1)) := by
  have prev : addi (W n) (-1) = W (n-1) := by
    have e := toNat_W (n := n) (by omega)
    have iv := iv_addi_neg (show Iv n n (W n) from ⟨e.ge,e.le⟩) 1 hn (by omega)
    exact BitVec.eq_of_toNat_eq ((Nat.le_antisymm iv.2 iv.1).trans (toNat_W (by omega)).symm)
  have mx : maxi (W (n-1)) 0 = W (n-1) := by
    change max32 _ (W 0) = _
    rw [max32,scmp_gt_W (by omega) (by decide),r32_W (by omega),r32_W (by decide)]
    simp only [sel,decide_eq_true_eq]
    split
    · rfl
    · exact congrArg W (by omega)
  rw [prev,mx,show (7 : Int) = ((7 : Nat) : Int) from rfl,shl_W (by decide) (by omega)]
  exact congrArg W (Nat.mul_comm (n-1) 128)

private theorem signed_min {a z row rest : Nat} (hz : a ≤ z) (hq : z < 2^30)
    (hr : row < z-a) (hk : rest+1 < 2^31) :
    S (min32 (addi (add32 (add32 (W row) (sub32 (W a) (W z))) (W rest)) 1) (W rest)) =
      min ((row : Int)-(z-a : Nat)+rest+1) rest := by
  have sr : S (W row) = row := signed_W (by omega)
  have sd : S (sub32 (W a) (W z)) = -((z-a : Nat) : Int) := by
    rw [S_sub (by rw [signed_W (by omega),signed_W (by omega)]; omega)
      (by rw [signed_W (by omega),signed_W (by omega)]; omega),
      signed_W (by omega),signed_W (by omega)]
    omega
  have srst : S (W rest) = rest := signed_W (by omega)
  have sa : S (add32 (W row) (sub32 (W a) (W z))) = (row : Int)-(z-a : Nat) := by
    rw [S_add (by rw [sr,sd]; omega) (by rw [sr,sd]; omega),sr,sd]
    omega
  have sb : S (add32 (add32 (W row) (sub32 (W a) (W z))) (W rest)) =
      (row : Int)-(z-a : Nat)+rest := by
    rw [S_add (by rw [sa,srst]; omega) (by rw [sa,srst]; omega),sa,srst]
  rw [S_min,S_addi (by decide) (by rw [sb]; omega) (by rw [sb]; omega),sb,srst]

/-- The first block's bit test at a valid request row is the causal key test. -/
theorem mask_signed {p L m g v b t} (hp : Pre p L m) (hw : g%L.block/32<8) (hb : b<p.batch)
    (h0 : v.sc.c0 = W (p.qOffset b)) (h1 : v.sc.c1 = W (p.qOffset (b+1)))
    (hu : v.ukw = W (p.kLength b)) (hr : shl (rowOff p L g v.sc) 8 = W (256*t))
    (valid : 256*t+128*(g%L.block/32/4)+g%L.block%128 < p.qLength b) :
    let n := min ((p.kLength b+127)/128) ((256*t+p.kLength b-p.qLength b+383)/128)
    let row := 256*t+128*(g%L.block/32/4)+g%L.block%128
    toSigned 32 (mcnt p L g v) = (p.keyCount b row : Int)-128*(n-1 : Nat) := by
  let row := 256*t+128*(g%L.block/32/4)+g%L.block%128
  let n := min ((p.kLength b+127)/128) ((256*t+p.kLength b-p.qLength b+383)/128)
  obtain ⟨leQ,leK,bound⟩ := hp.lengths b hb
  have q1 := hp.qOffset_le_total (show b+1 ≤ p.batch by omega)
  obtain ⟨_,_,_,_,_,total⟩ := hp.shape
  have len : p.qLength b = p.qOffset (b+1)-p.qOffset b := rfl
  have npos : 0<n := by dsimp [n]; omega
  have nbound : 128*(n-1)<p.kLength b := by dsimp [n]; omega
  have hn : r166 p L g v = W n := by
    rw [r166,r165,hr,hu,h0,h1]
    exact block_count leQ leK (by omega) (by omega) bound
  have pr := previous_offset npos (by omega : 128*(n-1)<2^31)
  rw [count_signed,mcnt,mask_row hp hw hr (by omega),r169,hn,pr,hu,sub32_W nbound.le (by omega),
    h0,h1,signed_min leQ (by omega) (by omega) (by omega)]
  unfold Params.keyCount
  omega

/-- The first block's bit test at a valid request row is the causal key test. -/
theorem mask_key {p L m g v b t} (hp : Pre p L m) (hw : g%L.block/32<8) (hb : b<p.batch)
    (h0 : v.sc.c0 = W (p.qOffset b)) (h1 : v.sc.c1 = W (p.qOffset (b+1)))
    (hu : v.ukw = W (p.kLength b)) (hr : shl (rowOff p L g v.sc) 8 = W (256*t))
    (valid : 256*t+128*(g%L.block/32/4)+g%L.block%128 < p.qLength b) (c : Fin 4) (j : Fin 32) :
    let n := min ((p.kLength b+127)/128) ((256*t+p.kLength b-p.qLength b+383)/128)
    let row := 256*t+128*(g%L.block/32/4)+g%L.block%128
    diagonal (mcnt p L g v) c.val j.val =
      decide (128*(n-1)+32*c.val+j.val < p.keyCount b row) := by
  let row := 256*t+128*(g%L.block/32/4)+g%L.block%128
  let n := min ((p.kLength b+127)/128) ((256*t+p.kLength b-p.qLength b+383)/128)
  have cut := mask_signed hp hw hb h0 h1 hu hr valid
  change toSigned 32 (mcnt p L g v) = (p.keyCount b row : Int)-128*(n-1 : Nat) at cut
  obtain ⟨_,leK,bound⟩ := hp.lengths b hb
  have hcut : -256 ≤ toSigned 32 (mcnt p L g v) ∧ toSigned 32 (mcnt p L g v) ≤ 128 := by
    rw [cut]
    unfold Params.keyCount n row
    omega
  rw [diagonal_iff hcut.1 hcut.2,cut]
  exact key_test n c.val j.val (p.keyCount b row)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
