-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Inv
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Arith
public import Lemmas.Flow.Arith32WordWide
public import Lemmas.Flow.Arith32WordW

@[expose] public section

/-! # The arithmetic of the Compute phase, in closed form

Each lemma states once what a group of integer instructions of the tile loop computes, as an
equation between the term of the generated thread machine (in the 32-bit vocabulary of
`Lemmas/Flow/Arith32.lean`) and the word `W n` of a number. The step lemmas of the phase
(`Steps*.lean`) rewrite with them.

* **Launch words**: the number of tokens of the batch as `ld.param.b32` reads it
  (`totalParam`), the gate offset (`gate_word`, `gateOff_word`: instructions 2117 to 2124 and
  2131), the loop counter (`counter_word`: instructions 2126 and 2127).
* **Thread-index words**: the parts of the addresses that depend on the thread's index in its
  block. The index is below 128, so each is one statement about the 128 numbers, checked by
  evaluation (`decide`): `warp_w`, `bit3_w`, `pair_w`, `acc_w`, `lane_w`, `warp10_w`,
  `warpLane_w`, `kr_w`, `gt_w`, `half_w`; `tid_*` are their instances at `tid g`.
* **Stage and parity words**: the mbarrier offsets `8 * stage` (`shl3_3`, `shl3_2`), the two
  stage bases (`mad18040`, `mad4088`), and the update of the stages, the parities and the loop
  counter at the end of a tile (`stage3_next`, `par3_next`, `stage2_next`, `par2_next`,
  `counter_next`, `counter_last`).
* **`mapa`**: with rank 0 it returns the address it is given (`mapaPeer_own`; a block is its
  own cluster).

`W n` is the 64-bit word of the number `n`; `T = tilesOf P g`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g t : Nat}

/-! ### Ranges -/

/-- The tokens of a thread's sequence are tokens of the batch. -/
theorem first_le (hpre : Pre P L mem0) (g : Nat) :
    firstToken P.length (seqOf P g) + P.length (seqOf P g) ≤ P.total := by
  have h := Startup.cu_succ P (seqOf P g)
  have h2 := Startup.cu_le P (i := seqOf P g + 1) (Startup.seq_lt hpre g)
  simp only [Startup.cu] at h h2
  omega

/-- The number of tiles of a sequence is below `2 ^ 27`. -/
theorem tiles_lt (hpre : Pre P L mem0) (g : Nat) : tilesOf P g < 2 ^ 27 := by
  have h1 := first_le hpre g
  have h2 := Startup.total_lt hpre
  simp only [tilesOf, tiles]
  omega

/-- A sequence with a token has a tile, and conversely. -/
theorem tiles_pos_iff (P : Params) (g : Nat) : 0 < tilesOf P g ↔ 0 < P.length (seqOf P g) := by
  simp only [tilesOf, tiles]
  omega

/-- The global index of the sequence's first token in the `[heads, tokens]` array. -/
theorem gateIdx_lt (hpre : Pre P L mem0) (hg : g < L.threads) :
    P.total * headOf P g + firstToken P.length (seqOf P g) < 2 ^ 31 := by
  have h1 := first_le hpre g
  have h3 := headOf_lt hpre hg
  have h4 : P.total * (headOf P g + 1) ≤ P.total * P.heads := Nat.mul_le_mul_left _ h3
  have h5 := hpre.headTokensRange
  rw [Nat.mul_comm P.heads] at h5
  rw [Nat.mul_add, Nat.mul_one] at h4
  omega

/-! ### Launch words -/

/-- Parameter 12 (the number of tokens of the batch), as `ld.param.b32` reads it. -/
theorem totalParam (hpre : Pre P L mem0) : r32 (paramBits L 12) = W P.total := by
  have h1 := Startup.total_lt hpre
  rw [paramBits, paramName_12, hpre.paramTokens]
  exact r32_W (by omega)

/-- **The gate position** (instructions 2117 to 2121): `(T_total * head + first token) & 7`. -/
theorem gate_word (hpre : Pre P L mem0) (hg : g < L.threads) :
    andi (mad32 (r32 (paramBits L 12)) (sreg ((L.ctaidOf (g / L.block)).get .y))
      (low32 (W (firstToken P.length (seqOf P g))))) 7 = W (gate P g) := by
  have h1 := gateIdx_lt hpre hg
  have h2 := Startup.total_lt hpre
  have h3 := headOf_lt hpre hg
  have h4 := hpre.headsLt
  have h5 := Startup.cu_r32 hpre (i := seqOf P g) (Startup.seq_lt hpre g).le
  simp only [Startup.cu] at h5
  rw [totalParam hpre, ctaidY hpre hg, h5,
    mad32_W (by omega) (by omega) (by omega), Startup.and7 (by omega)]
  rfl

/-- The shift and the mask of instructions 2122 to 2124 and 2131, for the 8 gate positions and
the 128 thread indices. -/
theorem half_w : ∀ k < 8, ∀ n < 128, shl (add32 (W k) (andi (shru (W n) 2) 7)) 1 =
    W (2 * (k + n / 4 % 8)) := by
  decide +kernel

/-- **The gate offset** `%r1641` (instructions 2122 to 2124 and 2131). -/
theorem gateOff_word (hc : tid g < 128) :
    shl (add32 (W (gate P g)) (andi (shru (W (tid g)) 2) 7)) 1 = W (gateOff P g) :=
  half_w _ (gate_lt P g) _ hc

/-- **The loop counter at the first tile** `%r1800` (instructions 2126 and 2127): minus the
number of tiles, as a 32-bit word. -/
theorem counter_word {T : Nat} (h1 : 1 ≤ T) (hT : T < 2 ^ 27) :
    neg32 (max32 (W T) (i32 1)) = W (4294967296 - (T - 0)) := by
  have e1 : (i32 1 : BitVec 64) = W 1 := rfl
  rw [e1, max32_W (by omega) (by omega), Nat.max_eq_left h1, neg32_W (by omega)]
  congr 1
  omega

/-! ### Thread-index words -/

theorem warp_w : ∀ n < 128, shru (W n) 5 = W (n / 32) := by decide +kernel

theorem bit3_w : ∀ n < 128, andi (shru (W n) 3) 1 = W (n / 8 % 2) := by decide +kernel

theorem pair_w : ∀ n < 128, or32 (or32 (andi (shl (W n) 3) 56) (andi (shl (W n) 2) 64))
    (andi (shl (W n) 7) 1024) = W (8 * (n % 8) + 64 * (n / 16 % 2) + 1024 * (n / 8 % 2)) := by
  decide +kernel

theorem acc_w : ∀ n < 128, shl (add32 (shl (W (n / 32)) 8)
    (W (8 * (n % 8) + 64 * (n / 16 % 2) + 1024 * (n / 8 % 2)))) 1 =
    W (512 * (n / 32) + 16 * (n % 8) + 128 * (n / 16 % 2) + 2048 * (n / 8 % 2)) := by
  decide +kernel

theorem lane_w : ∀ n < 128, andi (shl (W n) 4) 496 = W (16 * (n % 32)) := by decide +kernel

theorem warp10_w : ∀ n < 128, shl (W (n / 32)) 10 = W (1024 * (n / 32)) := by decide +kernel

theorem warpLane_w : ∀ n < 128, or32 (W (1024 * (n / 32))) (W (16 * (n % 32))) =
    W (1024 * (n / 32) + 16 * (n % 32)) := by
  decide +kernel

theorem kr_w : ∀ n < 128, shl (mad32 (W (n / 8 % 2)) (i32 (-896))
    (W (8 * (n % 8) + 64 * (n / 16 % 2) + 1024 * (n / 8 % 2)))) 1 =
    W (16 * (n % 8) + 256 * (n / 8 % 2) + 128 * (n / 16 % 2)) := by
  decide +kernel

theorem gt_w : ∀ n < 128, andi (W n) 28 = W (4 * (n / 4 % 8)) := by decide +kernel

/-- `%r1618 = %tid.x >> 5`: the warp. -/
theorem tid_warp (hc : tid g < 128) : shru (W (tid g)) 5 = W (tid g / 32) := warp_w _ hc

/-- `%r1626 = (%tid.x >> 3) & 1`. -/
theorem tid_bit3 (hc : tid g < 128) : andi (shru (W (tid g)) 3) 1 = W (tid g / 8 % 2) :=
  bit3_w _ hc

/-- `%r1629` (instructions 2152 to 2161). -/
theorem tid_pair (hc : tid g < 128) :
    or32 (or32 (andi (shl (W (tid g)) 3) 56) (andi (shl (W (tid g)) 2) 64))
      (andi (shl (W (tid g)) 7) 1024) = W (pairOff g) := pair_w _ hc

/-- `%r1631` (instructions 2151, 2162 and 2163): the offset of the lane's first row of the
bfloat16 state copy. -/
theorem tid_acc (hc : tid g < 128) :
    shl (add32 (shl (W (tid g / 32)) 8) (W (pairOff g))) 1 = W (accOff g) := acc_w _ hc

/-- `%r1637 = (%tid.x << 4) & 496`. -/
theorem tid_lane (hc : tid g < 128) : andi (shl (W (tid g)) 4) 496 = W (laneOff g) :=
  lane_w _ hc

/-- `%r1639 = %r1618 << 10`. -/
theorem tid_warp10 (hc : tid g < 128) : shl (W (tid g / 32)) 10 = W (warpOff g) :=
  warp10_w _ hc

/-- `%r1702 = %r1639 | %r1637`. -/
theorem tid_warpLane (hc : tid g < 128) :
    or32 (W (warpOff g)) (W (laneOff g)) = W (warpOff g + laneOff g) := warpLane_w _ hc

/-- `%r1705` (instructions 2506 and 2507): the lane's row of `k_restored`. -/
theorem tid_kr (hc : tid g < 128) :
    shl (mad32 (W (tid g / 8 % 2)) (i32 (-896)) (W (pairOff g))) 1 = W (krOff g) := kr_w _ hc

/-- `%r1707 = %tid.x & 28`. -/
theorem tid_gt (hc : tid g < 128) : andi (W (tid g)) 28 = W (gtOff g) := gt_w _ hc

/-! ### Stage and parity words -/

theorem shl3_small : ∀ a < 3, shl (W a) 3 = W (8 * a) := by decide +kernel

/-- `8 * stage` of an input stage (`shl.b32 %r1633, %r1802, 3`). -/
theorem shl3_3 (t : Nat) : shl (W (t % 3)) 3 = W (8 * (t % 3)) :=
  shl3_small _ (Nat.mod_lt _ (by decide))

/-- `8 * stage` of an output stage (`shl.b32 %r847, %r1804, 3`). -/
theorem shl3_2 (t : Nat) : shl (W (t % 2)) 3 = W (8 * (t % 2)) :=
  shl3_small _ (by omega)

/-- `i32` of a small literal is its word. -/
theorem i32_lit {n : Nat} (hn : n < 2 ^ 31) : i32 (n : Int) = W n := i32_W hn

/-- **The base of the input stage** `%r1635` (`mad.lo.s32 %r1635, %r1802, 18040, %r1634`). -/
theorem mad18040 {S : Nat} (hS : S + 98392 ≤ 2 ^ 18) (t : Nat) :
    mad32 (W (t % 3)) (i32 18040) (W (S + 8 * (t % 3))) = W (S + 18048 * (t % 3)) := by
  have e : (i32 18040 : BitVec 64) = W 18040 := rfl
  have h3 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [e, mad32_W (by omega) (by omega) (by omega)]
  congr 1
  omega

/-- **The base of the output stage** `%r1701` (`mad.lo.s32 %r1701, %r1804, 4088, %r1700`). -/
theorem mad4088 {S : Nat} (hS : S + 98392 ≤ 2 ^ 18) (t : Nat) :
    mad32 (W (t % 2)) (i32 4088) (W (S + 8 * (t % 2))) = W (S + 4096 * (t % 2)) := by
  have e : (i32 4088 : BitVec 64) = W 4088 := rfl
  have h3 : t % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [e, mad32_W (by omega) (by omega) (by omega)]
  congr 1
  omega

theorem stage3_small : ∀ a < 3, sel (scmpi .eq .b (addi (W a) 1) 3) (i32 0) (addi (W a) 1) =
    W (if a = 2 then 0 else a + 1) := by decide +kernel

theorem par3_small : ∀ a < 3, ∀ b < 2,
    xor32 (W b) (sel (scmpi .eq .b (addi (W a) 1) 3) (i32 1) (i32 0)) =
      W (if a = 2 then 1 - b else b) := by decide +kernel

theorem stage2_small : ∀ a < 2, sel (scmpi .eq .b (addi (W a) 1) 2) (i32 0) (addi (W a) 1) =
    W (if a = 1 then 0 else a + 1) := by decide +kernel

theorem par2_small : ∀ a < 2, ∀ b < 2,
    xor32 (W b) (sel (scmpi .eq .b (addi (W a) 1) 2) (i32 1) (i32 0)) =
      W (if a = 1 then 1 - b else b) := by decide +kernel

/-- **The input stage of the next tile** (instructions 2931 to 2933). -/
theorem stage3_next (t : Nat) :
    sel (scmpi .eq .b (addi (W (t % 3)) 1) 3) (i32 0) (addi (W (t % 3)) 1) = W ((t + 1) % 3) := by
  rw [stage3_small _ (Nat.mod_lt _ (by decide))]
  congr 1
  split <;> omega

/-- **The parity of the next tile's poll of the input pipeline** (instructions 2934, 2935): it
flips when the stage wraps. -/
theorem par3_next (t : Nat) :
    xor32 (W (t / 3 % 2)) (sel (scmpi .eq .b (addi (W (t % 3)) 1) 3) (i32 1) (i32 0)) =
      W ((t + 1) / 3 % 2) := by
  rw [par3_small _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))]
  congr 1
  split <;> omega

/-- **The output stage of the next tile** (instructions 2936 to 2938). -/
theorem stage2_next (t : Nat) :
    sel (scmpi .eq .b (addi (W (t % 2)) 1) 2) (i32 0) (addi (W (t % 2)) 1) = W ((t + 1) % 2) := by
  rw [stage2_small _ (Nat.mod_lt _ (by decide))]
  congr 1
  split <;> omega

/-- **The parity of the next tile's poll of the output pipeline** (instructions 2939, 2940). -/
theorem par2_next (t : Nat) :
    xor32 (W ((t / 2 + 1) % 2)) (sel (scmpi .eq .b (addi (W (t % 2)) 1) 2) (i32 1) (i32 0)) =
      W (((t + 1) / 2 + 1) % 2) := by
  rw [par2_small _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))]
  congr 1
  split <;> omega

/-- **The loop counter of the next tile** (`add.s32 %r1800, %r1800, 1`), when a tile is left. -/
theorem counter_next {T t : Nat} (ht : t + 1 < T) (hT : T < 2 ^ 27) :
    addi (W (4294967296 - (T - t))) 1 = W (4294967296 - (T - (t + 1))) := by
  rw [addi1_W (by omega)]
  congr 1
  omega

/-- **The loop counter after the last tile** is zero. -/
theorem counter_last {T t : Nat} (ht : t + 1 = T) :
    addi (W (4294967296 - (T - t))) 1 = W 0 := by
  have e : 4294967296 - (T - t) = 4294967295 := by omega
  rw [e]
  decide +kernel

/-- The loop counter of a tile that is not the last is not zero. -/
theorem counter_ne {T t : Nat} (ht : t < T) (hT : T < 2 ^ 27) :
    scmpi .eq .b (W (4294967296 - (T - t))) 0 = false := by
  rw [Startup.cmp_eq0 (by omega)]
  exact decide_eq_false (by omega)

/-! ### `mapa` -/

/-- **`mapa` with rank 0 returns the address it is given**: a block is its own cluster. (The
Store phase has the same lemma in `Ref/Store/Arith.lean`; the two phases do not import each
other.) -/
theorem mapaPeer_own (hpre : Pre P L mem0) (hg : g < L.threads) {a : Nat} (ha : a < 2 ^ 32) :
    mapaPeer L g (W a) (W 0) = some ⟨.shared, g / L.block, a⟩ := by
  have hc : g / L.block < L.grid := by
    rw [block_div hpre, hpre.grid]
    exact cta_lt hpre hg
  have h0 : (truncBits 32 (W 0)).toNat = 0 := by decide
  have h1 : (truncBits 32 (W a)).toNat = a := by
    simp only [truncBits, W, BitVec.toNat_ofNat]; omega
  simp only [mapaPeer, hg, hc, and_self, ↓reduceIte, h0, h1, Launch.mapShared,
    Launch.peerCta_unit (unitClusters hpre) (cta_lt_nclusters hpre hg) hc, Option.map_some]

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
