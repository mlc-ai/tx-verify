-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Lib.RowBias
import Lemmas.Flow.Arith32WordW
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The tile words of a loader lane in numbers

The words of the picked tile (`refVL`, `setup`): the request, its offsets and used-K length, the
tile's first row and head of the scheduler's coordinates, and its number of K/V blocks
(`tileBlocks`): the blocks of the used keys and of the keys up to the tile's last row. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The K/V blocks of tile `t` of request `b`. -/
def tileBlocks (p : Params) (b t : Nat) : Nat :=
  min ((p.kLength b + 127) / 128) ((256 * t + p.kLength b - p.qLength b + 256 + 127) / 128)

/-- **The tile words in numbers.** -/
structure TileNum (p : Params) (L : Launch) (g : Nat) (v : V) (su : Setup) (b : Nat) : Prop where
  batch : b < p.batch
  lo : tilePrefix p b * p.heads ≤ g / L.block
  hi : g / L.block < tilePrefix p (b + 1) * p.heads
  chosen : Epilogue.chosen v.sc = W b
  c0 : v.sc.c0 = W (p.qOffset b)
  c1 : v.sc.c1 = W (p.qOffset (b + 1))
  ukw : v.ukw = W (p.kLength b)
  head : v.co.head = W (Epilogue.assignedCoordinates p b (g / L.block)).2
  row : su.r741 = W (256 * (Epilogue.assignedCoordinates p b (g / L.block)).1)
  r28 : su.r28 = W (tileBlocks p b (Epilogue.assignedCoordinates p b (g / L.block)).1)

/-- The code's ceiling of a quotient by 128. -/
theorem cdiv_W {k : Nat} (hk : k < 2 ^ 31) :
    add32 (cdivS (W k)) (sel (cdivP (W k)) (i32 1) (i32 0)) = W ((k + 127) / 128) := by
  have h1 : shrs (W k) 31 = W 0 := by
    have := toNat_shrs_W (show k < 2 ^ 31 by omega) (k := 31) (by decide)
    rw [show k / 2 ^ 31 = 0 by omega] at this
    exact this
  have h2 : shru (W 0) 25 = W 0 := by decide
  have h3 : add32 (W k) (W 0) = W k := by rw [add32_W (by omega)]; rfl
  have h4 : andi (W k) (-128) = W (k - k % 128) :=
    andi_W_neg (k := 7) (by omega) (by decide)
  have h5 : scmpi .gt .s (W k) (-1) = true := by
    simp only [scmpi, PTX.compare]
    rw [r32_W (by omega), toSigned_W (by omega), show toSigned 32 (i32 (-1)) = -1 by decide]
    simp
    omega
  have h6 : scmp .ne .b (W k) (W (k - k % 128)) = decide (k % 128 ≠ 0) := by
    rw [scmp_ne_b_W (by omega) (by omega)]
    simp only [decide_eq_decide]
    omega
  have hP : cdivP (W k) = decide (k % 128 ≠ 0) := by
    simp only [cdivP, h1, h2, h3, h4, h5, h6, Bool.true_and]
  rw [cdivS_W (by omega), hP]
  by_cases h : k % 128 = 0
  · rw [show decide (k % 128 ≠ 0) = false by simp [h], show sel false (i32 1) (i32 0) = W 0 from
      rfl,
      add32_W (by omega)]
    congr 1; omega
  · rw [show decide (k % 128 ≠ 0) = true by simp [h], show sel true (i32 1) (i32 0) = W 1 from rfl,
      add32_W (by omega)]
    congr 1; omega

/-- The signed difference of the request's offsets, in a wrapping sum. -/
private theorem sum_W {r k c0 c1 : Nat} (h01 : c0 ≤ c1) (h1 : c1 < 2 ^ 32) (hk : c1 - c0 ≤ r + k)
    (hr : r < 2 ^ 31) (hk2 : k < 2 ^ 31) :
    add32 (add32 (W r) (W k)) (sub32 (W c0) (W c1)) = W (r + k - (c1 - c0)) := by
  rw [add32_W (by omega), sub32_Wm, add32_Wm]
  congr 1
  omega

/-- **The picked tile's words in numbers.** -/
theorem tile_num (hp : Pre p L m) (hg : g < L.threads) {R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L g R bal) :
    ∃ b, TileNum p L g (refVL p L g R bal) (setup p L g (refVL p L g R bal)) b := by
  have hC : Epilogue.ChosenVals p L g R bal (Epilogue.chosenD p (g / L.block) R bal)
      (3 + 7 * (R + 1) + Epilogue.selN bal) 1 := ⟨hP, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨b, hb, hlo, hhi, hc, hco⟩ := Epilogue.chosen_spec hp hg hC
  obtain ⟨hv1, hv2⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  set t := (Epilogue.assignedCoordinates p b (g / L.block)).1 with ht
  set h := (Epilogue.assignedCoordinates p b (g / L.block)).2 with hh
  obtain ⟨hl1, hl2, hl3⟩ := hp.lengths b hb
  have hbb : b < 2 ^ 31 := by have := hp.shape.2.1; omega
  have hq1 := hp.qOffset_le_total (show b + 1 ≤ p.batch by omega)
  have htq := hp.shape.2.2.2.2.2
  have hqt : p.qOffset (b + 1) < 2 ^ 30 := by omega
  have hql : p.qLength b = p.qOffset (b + 1) - p.qOffset b := rfl
  have e0 : (refVL p L g R bal).sc.c0 = W (p.qOffset b) := by
    show Epilogue.qv p (chosen (Epilogue.chosenD p (g / L.block) R bal)) = _
    rw [hc, Epilogue.qv_W hp (by omega)]
  have e1 : (refVL p L g R bal).sc.c1 = W (p.qOffset (b + 1)) := by
    show Epilogue.qv p (addi (chosen (Epilogue.chosenD p (g / L.block) R bal)) 1) = _
    rw [hc, show (1 : Int) = ((1 : Nat) : Int) from rfl, addi_W (by decide) (by omega),
      Epilogue.qv_W hp (by omega)]
  have eu : (refVL p L g R bal).ukw = W (p.kLength b) := by
    show Mma.ukv p (chosen (Epilogue.chosenD p (g / L.block) R bal)) = _
    rw [hc, Mma.ukv, show Epilogue.r32 (W b) = W b from r32_W (by omega), toNat_W (by omega)]
  have ehd : (refVL p L g R bal).co.head = W h := by
    have := congrArg Epilogue.Coords.head hco
    exact this
  have erow : shl (refVL p L g R bal).co.row 8 = W (256 * t) := by
    have h1 := congrArg Epilogue.Coords.row hco
    dsimp only at h1
    rw [show (Epilogue.coords p L g (Epilogue.chosenD p (g / L.block) R bal)).row =
      addi (shl (refVL p L g R bal).co.row 8) 1073741824 from rfl] at h1
    exact row_unbias (shl8_lt _) (by omega) h1
  have e741 : (setup p L g (refVL p L g R bal)).r741 = W (256 * t) := by
    simp only [setup]; exact erow
  refine ⟨b, hb, hlo, hhi, hc, e0, e1, eu, ehd, e741, ?_⟩
  have e28 : (setup p L g (refVL p L g R bal)).r28 = min32
      (add32 (cdivS (refVL p L g R bal).ukw)
        (sel (cdivP (refVL p L g R bal).ukw) (i32 1) (i32 0)))
      (add32 (cdivS (addi (add32 (add32 (shl (refVL p L g R bal).co.row 8)
          (refVL p L g R bal).ukw) (sub32 (refVL p L g R bal).sc.c0 (refVL p L g R bal).sc.c1))
              256))
        (sel (cdivP (addi (add32 (add32 (shl (refVL p L g R bal).co.row 8)
          (refVL p L g R bal).ukw) (sub32 (refVL p L g R bal).sc.c0 (refVL p L g R bal).sc.c1))
            256)) (i32 1) (i32 0))) := by
    simp only [setup]
  rw [e28, erow, eu, e0, e1, sum_W hl1 (by omega) (by omega) (by omega) (by omega),
    show (256 : Int) = ((256 : Nat) : Int) from rfl, addi_W (by decide) (by omega),
    cdiv_W (by omega), cdiv_W (by omega), min32_W (by omega) (by omega)]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
