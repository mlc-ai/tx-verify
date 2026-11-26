-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Inv
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Arith
public import Lemmas.Flow.Arith32WordWide

@[expose] public section

/-! # The arithmetic of the Producer phase, in closed form

Each computation of the tile loop of the load leader, proved once: the code's term (in the
32-bit vocabulary of the generated thread machine) is the word of a number.

* launch words: the workspace capacity (parameter 16), the number of tokens (parameter 12) and
  the scale of the first coordinate of `v` (the 32-bit word at offset 128 of parameter object 0,
  which is 1);
* the stage and the parity of the next tile (`stage_word`, `par_word`): the code keeps the
  stage `t % 3` and flips the parity when the stage wraps;
* shared addresses of the stage `t % 3` of a tile `t`: its "empty" mbarrier (`emptyAddr`), its
  "full" mbarrier (`fullAddr`), its input buffer (`bufBase`);
* the tile's first token (`token_word`), the workspace slot of the block's first tile
  (`slotBase_word`, bound `slotBase_lt`), the first coordinate of the load of `beta`
  (`beta_word`), the scaled first coordinates of the loads of `v` (`scale_shl3` ...);
* the loop's bound: `max(T, 1) & 0x7FFFFFE` is `T` rounded down to an even number
  (`evenTiles`), `max(T, 1) & 1` its parity (`oddTiles`);
* ranges: the tiles of a sequence, its tokens and its workspace slots fit 31 bits. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (cu ft cu_succ ft_succ cu_le ft_mono total_lt)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-! ### Ranges -/

/-- The tokens of a sequence are tokens of the batch. -/
theorem len_le (hpre : Pre P L mem0) (g : Nat) :
    cu P (seqOf P g) + P.length (seqOf P g) ≤ P.total := by
  have h := cu_le P (show seqOf P g + 1 ≤ P.sequences from seqOf_lt hpre g)
  rwa [cu_succ] at h

/-- The number of tiles of a sequence is below `2 ^ 27`. -/
theorem tiles_lt (hpre : Pre P L mem0) (g : Nat) : tilesOf P g < 2 ^ 27 := by
  have h1 := len_le hpre g
  have h2 := total_lt hpre
  simp only [tilesOf, tiles]
  omega

/-- The first token of tile `t < T` of the block's sequence is a token of the sequence. -/
theorem token_lt (hpre : Pre P L mem0) {t : Nat} (ht : t < tilesOf P g) :
    cu P (seqOf P g) + 16 * t < P.total := by
  have h1 := len_le hpre g
  simp only [tilesOf, tiles] at ht
  omega

/-- The index of a tile's first token in the `[heads, tokens]` array of gate logits. -/
theorem beta_lt (hpre : Pre P L mem0) (hg : g < L.threads) {t : Nat} (ht : t < tilesOf P g) :
    P.total * headOf P g + (cu P (seqOf P g) + 16 * t) < P.heads * P.total := by
  have h1 := token_lt hpre ht
  have h3 := headOf_lt hpre hg
  have h4 : P.total * (headOf P g + 1) ≤ P.total * P.heads := Nat.mul_le_mul_left _ h3
  rw [Nat.mul_comm P.heads]
  rw [Nat.mul_add, Nat.mul_one] at h4
  omega

/-! ### Launch words -/

/-- Parameter 16 (the workspace capacity in tiles per head), as `ld.param.b32` reads it. -/
theorem tilesParam (hpre : Pre P L mem0) : r32 (paramBits L 16) = W P.totalTiles := by
  have h1 := hpre.slotsRange
  have h2 : P.totalTiles ≤ P.heads * P.totalTiles := Nat.le_mul_of_pos_left _ hpre.headsPos
  rw [paramBits, paramName_16, hpre.paramTiles]
  exact r32_W (by omega)

/-- Parameter 12 (the number of tokens of the batch), as `ld.param.b32` reads it. -/
theorem totalParam (hpre : Pre P L mem0) : r32 (paramBits L 12) = W P.total := by
  have h1 := total_lt hpre
  rw [paramBits, paramName_12, hpre.paramTokens]
  exact r32_W (by omega)

/-- The 32-bit word at offset 128 of parameter object 0 (the scale of the first coordinate of
the map of `v`) is 1. -/
theorem scaleWord (hpre : Pre P L mem0) : objField L 0 = W 1 := by
  have h := hpre.scaleV
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.add_zero] at h0
  have e0 : (leByte 1 0).toNat = 1 := by decide
  have e1 : (leByte 1 1).toNat = 0 := by decide
  have e2 : (leByte 1 2).toNat = 0 := by decide
  have e3 : (leByte 1 3).toNat = 0 := by decide
  simp only [objField, paramName_0, paramNat, Nat.reduceDiv, h0, h1, h2, h3, Option.getD_some,
    e0, e1, e2, e3, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

/-! ### The stage and the parity of the next tile -/

theorem par_zero : par 0 = 1 := rfl

theorem par_lt (t : Nat) : par t < 2 := Nat.mod_lt _ (by decide)

/-- The stage of the next tile: `s + 1`, or 0 when that is 3. -/
theorem stage_word (t : Nat) :
    sel (scmpi .eq .b (addi (W (t % 3)) 1) 3) (i32 0) (addi (W (t % 3)) 1) =
      W ((t + 1) % 3) := by
  have h : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have h3 : (t + 1) % 3 = (t % 3 + 1) % 3 := by omega
  rw [h3]
  generalize t % 3 = s at h
  interval_cases s <;> decide

/-- The parity of the poll for the next tile: flipped when the stage wraps. -/
theorem par_word (t : Nat) :
    xor32 (W (par t)) (sel (scmpi .eq .b (addi (W (t % 3)) 1) 3) (i32 1) (i32 0)) =
      W (par (t + 1)) := by
  have h : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have hp : par t < 2 := par_lt t
  have hn : par (t + 1) = if t % 3 = 2 then 1 - par t else par t := by
    unfold par
    split_ifs <;> omega
  rw [hn]
  generalize t % 3 = s at h
  generalize par t = q at hp
  interval_cases s <;> interval_cases q <;> decide

/-! ### Shared addresses of a stage

The stage is always held as `t % 3` for a tile index `t`; the lemmas are stated in that form,
without side conditions, so that they rewrite the code's terms directly. -/

/-- `shl.b32 %r, stage, 3`. -/
theorem shl3 (t : Nat) : shl (W (t % 3)) 3 = W (8 * (t % 3)) := by
  have h : t % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize t % 3 = s at h
  interval_cases s <;> decide

/-- The address of the "empty" mbarrier of the stage of tile `t`. -/
theorem emptyAddr (hpre : Pre P L mem0) (t : Nat) :
    addi (add32 (W P.sharedBase) (W (8 * (t % 3)))) 98328 =
      W (P.sharedBase + 98328 + 8 * (t % 3)) := by
  have h := shared_lt hpre
  have hs : t % 3 < 3 := Nat.mod_lt _ (by decide)
  w32_norm
  congr 1
  omega

/-- The address of the "full" mbarrier of the stage of tile `t`. -/
theorem fullAddr (hpre : Pre P L mem0) (t : Nat) :
    addi (add32 (W P.sharedBase) (W (8 * (t % 3)))) 98304 =
      W (P.sharedBase + 98304 + 8 * (t % 3)) := by
  have h := shared_lt hpre
  have hs : t % 3 < 3 := Nat.mod_lt _ (by decide)
  w32_norm
  congr 1
  omega

/-- The base of the input buffer of the stage of tile `t`, less 32768:
`stage * 18040 + (shared + 8 * stage)`. -/
theorem bufBase (hpre : Pre P L mem0) (t : Nat) :
    mad32 (W (t % 3)) (i32 18040) (add32 (W P.sharedBase) (W (8 * (t % 3)))) =
      W (P.sharedBase + 18048 * (t % 3)) := by
  have h := shared_lt hpre
  have hs : t % 3 < 3 := Nat.mod_lt _ (by decide)
  w32_norm
  congr 1
  omega

/-- The constant 0 as the word of stage `0 % 3` (the stage register at the loop's entry). -/
theorem i32_zero_stage : i32 0 = W (0 % 3) := rfl

/-! ### The tile -/

/-- The workspace slot of the block's first tile fits 31 bits. -/
theorem slotBase_lt (hpre : Pre P L mem0) (hg : g < L.threads) :
    P.totalTiles * headOf P g + ft P (seqOf P g) + tilesOf P g ≤ P.heads * P.totalTiles := by
  have h1 := ft_mono P (show seqOf P g + 1 ≤ P.sequences from seqOf_lt hpre g)
  rw [ft_succ] at h1
  have h2 := hpre.tilesFit
  have h3 := headOf_lt hpre hg
  have h4 : P.totalTiles * (headOf P g + 1) ≤ P.totalTiles * P.heads :=
    Nat.mul_le_mul_left _ h3
  simp only [ft, tilesOf] at *
  rw [Nat.mul_comm P.heads]
  rw [Nat.mul_add, Nat.mul_one] at h4
  omega

/-- The workspace slot of tile `t < T` of the block is a slot of the workspace. -/
theorem slot_lt (hpre : Pre P L mem0) (hg : g < L.threads) {t : Nat} (ht : t < tilesOf P g) :
    P.totalTiles * headOf P g + ft P (seqOf P g) + t < P.heads * P.totalTiles := by
  have h := slotBase_lt hpre hg
  omega

/-- The workspace slot of the block's first tile: `total_tiles * head + tile_base`. -/
theorem slotBase_word (hpre : Pre P L mem0) (hg : g < L.threads) :
    mad32 (W P.totalTiles) (W (headOf P g)) (W (ft P (seqOf P g))) =
      W (P.totalTiles * headOf P g + ft P (seqOf P g)) := by
  have h1 := slotBase_lt hpre hg
  have h2 := hpre.slotsRange
  have h3 : P.totalTiles ≤ P.heads * P.totalTiles := Nat.le_mul_of_pos_left _ hpre.headsPos
  have h4 := hpre.headsLt
  have h5 := headOf_lt hpre hg
  exact mad32_W (by omega) (by omega) (by omega)

/-- The scaled first coordinates of the loads of `v`: `scale << k` with scale 1. -/
theorem scale_shl3 : shl (W 1) 3 = W 8 := by decide
theorem scale_shl4 : shl (W 1) 4 = W 16 := by decide
theorem scale_shl5 : shl (W 1) 5 = W 32 := by decide
theorem scale_shl6 : shl (W 1) 6 = W 64 := by decide


/-- The tile's first token: `(tile << 4) + cu_seqlens[seq]`. -/
theorem token_word (hpre : Pre P L mem0) {t : Nat} (ht : t < tilesOf P g) :
    add32 (shl (W t) 4) (low32 (W (cu P (seqOf P g)))) = W (cu P (seqOf P g) + 16 * t) := by
  have h1 := token_lt hpre ht
  have h2 := total_lt hpre
  have h3 : shl (W t) 4 = W (t * 2 ^ 4) := shl_W (k := 4) (by decide) (by omega)
  rw [h3, Startup.cu_r32 hpre (Nat.le_of_lt (seqOf_lt hpre g)), add32_W (by omega)]
  congr 1
  omega

/-- `and.b32 %r, %r, -8`: rounding down to a multiple of 8. -/
theorem andi_neg8 {a : Nat} (ha : a < 2 ^ 32) : andi (W a) (-8) = W (a - a % 8) :=
  andi_W_neg (k := 3) ha (by norm_num)

/-- The first coordinate of the load of `beta`: `(tokens * head + token) & -8`. -/
theorem beta_word (hpre : Pre P L mem0) (hg : g < L.threads) {t : Nat} (ht : t < tilesOf P g) :
    andi (mad32 (W P.total) (W (headOf P g)) (W (cu P (seqOf P g) + 16 * t))) (-8) =
      W (betaIdx P g t) := by
  have h1 := beta_lt hpre hg ht
  have h2 := hpre.headTokensRange
  have h3 := total_lt hpre
  have h4 := hpre.headsLt
  have h5 := headOf_lt hpre hg
  rw [mad32_W (by omega) (by omega) (by omega), andi_neg8 (by omega)]
  rfl

/-! ### The bound of the unrolled loop -/

/-- `max.s32 %r, tiles, 1` for a sequence with a tile. -/
theorem maxTiles {T : Nat} (h1 : 1 ≤ T) (hT : T < 2 ^ 27) : max32 (W T) (i32 1) = W T := by
  rw [show i32 1 = W 1 from rfl, max32_W (by omega) (by omega)]
  congr 1
  omega

/-- `and.b32 %r, tiles, 134217726`: the number of tiles rounded down to an even number. -/
theorem evenTiles {T : Nat} (hT : T < 2 ^ 27) : andi (W T) 134217726 = W (T - T % 2) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : T &&& 134217726 = T - T % 2 := by
    have h2 : T &&& 134217727 = T := by
      rw [show 134217727 = 2 ^ 27 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt hT]
    have h3 := and_negpow (a := T) (k := 1) (by omega) (by norm_num)
    have h4 : (134217727 : Nat) &&& (2 ^ 32 - 2 ^ 1) = 134217726 := by decide
    rw [← h4, ← Nat.and_assoc, h2, h3]
    norm_num
  have h5 : T - T % 2 < 2 ^ 64 := by omega
  have hi : (i32 134217726).toNat = 134217726 := by decide
  simp only [andi, BitVec.toNat_and, r32_W (show T < 2 ^ 32 by omega), hi,
    toNat_W (show T < 2 ^ 64 by omega), toNat_W h5, h1]

/-- `and.b32 %r, tiles, 1`: whether the number of tiles is odd. -/
theorem oddTiles {T : Nat} (hT : T < 2 ^ 27) : andi (W T) 1 = W (T % 2) :=
  Startup.and1 (by omega)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
