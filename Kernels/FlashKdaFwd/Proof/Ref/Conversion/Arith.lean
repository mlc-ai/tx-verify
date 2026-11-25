-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Inv
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Lib

@[expose] public section

/-! # The arithmetic of the Conversion phase, in closed form

Each computation of the phase's code, proved once as an equation between the term of the
generated transition functions and the word of a number (`W n`):

* the three words of the lane (`lane_words`), the remainder word of the first loop and its
  16-bit test (`rem_word`, `rem_test`, `rem_zext`);
* the element index of a pair and of its second element (`PairWords`, `pair_words`): the code
  assembles them from the pair index and the lane with shifts, masks and `or`; the equations
  are checked by evaluation for every pair index below 256 and every lane (`elem_words`,
  8192 cases, decided by the kernel);
* the address of a slot of `state_acc` (`wr_word`) and the facts about the swizzled address of
  an FP32 entry (`rdAddr_frame`);
* the loop variables and the two loop tests (`pairIx_step`, `first_test`, `second_test`,
  `second_iff`);
* the base of the carry loads (`carry_word`).

The last part is about the elements themselves: every element of a thread is below 16384
(`slot0_lt`), and an element determines the thread that converts it (`convOwner`,
`slot0_owner`) and its ordinal (`slot_cover`): each of the 16384 elements of a block is
converted by exactly one thread, once. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-! ### Bounds -/

theorem head_eq (g : Nat) : head g = rem4 g + 2 := by
  unfold head rem4
  split_ifs <;> rfl

theorem head_le (g : Nat) : head g ≤ 3 ∧ 2 ≤ head g := by
  unfold head
  split_ifs <;> omega

/-- The pair index of every pair of a thread is below 256. -/
theorem pairIx_lt {u : Nat} (hu : u < pairs g) : pairIx g u < 256 := by
  have := warp_lt g
  unfold pairs head at hu
  unfold pairIx
  split_ifs at hu <;> omega

/-- Both elements of every pair of a thread are below 16384. -/
theorem slot0_lt {u : Nat} (hu : u < pairs g) : slot0 g u + 1 < 16384 := by
  have := pairIx_lt hu
  have := lane_lt g
  unfold slot0
  omega

/-! ### The words of the lane and of the first loop's test -/

theorem lane_words_all : ∀ t < 192,
    or32 (andi (shl (W t) 1) 62) (i32 1) = W (2 * (t % 32) + 1) ∧
    shru (andi (W t) 31) 2 = W (t % 32 / 4) ∧
    andi (shl (W t) 1) 6 = W (2 * (t % 32 % 4)) := by decide +kernel

/-- The three words of the lane (`%r10`, `%r11`, `%r12`, instructions 388 to 393). -/
theorem lane_words (g : Nat) :
    or32 (andi (shl (W (tid g)) 1) 62) (i32 1) = W (2 * lane g + 1) ∧
    shru (andi (W (tid g)) 31) 2 = W (lane g / 4) ∧
    andi (shl (W (tid g)) 1) 6 = W (2 * (lane g % 4)) :=
  lane_words_all (tid g) (tid_lt g)

theorem rem_word_all : ∀ w < 6,
    andi16 (shrui16 (muli16 (andi16 (isub16 (-7) (low16 (W w))) 255) 171) 10) 3 =
      W (if w < 4 then 1 else 0) := by decide +kernel

/-- The pair count modulo 4 (`%rs1`, the 16-bit code of instructions 394 to 399). -/
theorem rem_word (g : Nat) :
    andi16 (shrui16 (muli16 (andi16 (isub16 (-7) (low16 (W (warp g)))) 255) 171) 10) 3 =
      W (rem4 g) :=
  rem_word_all (warp g) (warp_lt g)

theorem rem_all : ∀ r < 2, scmpi16 .eq (W r) 2 = false ∧ zext16 (W r) = W r := by
  decide +kernel

theorem rem4_lt (g : Nat) : rem4 g < 2 := by
  unfold rem4
  split_ifs <;> omega

/-- The first loop is never skipped (`setp.eq.b16 %p27, %rs1, 2`, instruction 400). -/
theorem rem_test (g : Nat) : scmpi16 .eq (W (rem4 g)) 2 = false := (rem_all _ (rem4_lt g)).1

theorem rem_zext (g : Nat) : zext16 (W (rem4 g)) = W (rem4 g) := (rem_all _ (rem4_lt g)).2

/-! ### The element indices of a pair -/

theorem elem_words : ∀ i < 256, ∀ l < 32,
    shl (or32 (andi (shl (W i) 3) 120) (W (2 * (l % 4)))) 7 =
      W (1024 * (i % 16) + 256 * (l % 4)) ∧
    or32 (or32 (andi (W (1024 * (i % 16) + 256 * (l % 4))) 15360) (W (2 * (l % 4))))
        (shl (or32 (andi (shru (W i) 1) 120) (W (l / 4))) 3) =
      W (1024 * (i % 16) + 64 * (i / 16) + 2 * l) ∧
    or32 (or32 (W (2 * l + 1)) (andi (shl (W i) 2) 960))
        (andi (addi (W (1024 * (i % 16) + 256 * (l % 4))) 128) 15360) =
      W (1024 * (i % 16) + 64 * (i / 16) + 2 * l + 1) := by decide +kernel

theorem quad_word {e : Nat} (he : e < 16384) : mulWide .u (W e) 4 = W (4 * e) := by
  rw [mulWide_u_W (by omega) (by decide) (by decide)]
  show W (e * 4) = W (4 * e)
  rw [Nat.mul_comm]

/-- **The words the code computes for the pair `r`**: the upper part of the element index
(`%r242`), the index of the first element (`%r245`) and of the second (`%r254`), and the two
byte offsets in the FP32 buffer (`mul.wide.u32 …, 4`). -/
structure PairWords (g r : Nat) : Prop where
  hi : shl (or32 (andi (shl (W (pairIx g r)) 3) 120) (W (2 * (lane g % 4)))) 7 = W (hiOf g r)
  s0 : or32 (or32 (andi (W (hiOf g r)) 15360) (W (2 * (lane g % 4))))
      (shl (or32 (andi (shru (W (pairIx g r)) 1) 120) (W (lane g / 4))) 3) = W (slot0 g r)
  s1 : or32 (or32 (W (2 * lane g + 1)) (andi (shl (W (pairIx g r)) 2) 960))
      (andi (addi (W (hiOf g r)) 128) 15360) = W (slot0 g r + 1)
  q0 : mulWide .u (W (slot0 g r)) 4 = W (4 * slot0 g r)
  q1 : mulWide .u (W (slot0 g r + 1)) 4 = W (4 * (slot0 g r + 1))

theorem pair_words {r : Nat} (hr : r < pairs g) : PairWords g r := by
  obtain ⟨h1, h2, h3⟩ := elem_words _ (pairIx_lt hr) _ (lane_lt g)
  have := slot0_lt hr
  exact ⟨h1, h2, h3, quad_word (by omega), quad_word (by omega)⟩

/-- The address of the slot of element `e` (`shl.b32 …, 1` and `add.s32` on `shared_mem`). -/
theorem wr_word (hpre : Pre P L mem0) {e : Nat} (he : e < 16384) :
    add32 (W P.sharedBase) (shl (W e) 1) = W (wrAddr P e) := by
  have hs := shared_lt hpre
  have h1 : shl (W e) 1 = W (e * 2 ^ 1) := shl_W (k := 1) (by decide) (by omega)
  rw [h1, add32_W (by omega)]
  unfold wrAddr
  congr 1
  omega

/-- The shared base as a 64-bit word (`cvt.u64.u32`). -/
theorem zext_W {a : Nat} (ha : a < 2 ^ 32) : zext (W a) = W a := by
  show truncBits 64 (r32 (W a)) = W a
  rw [r32_W ha, Rules.truncBits_64]

/-! ### The loop variables and tests -/

theorem pairIx_step (g u k : Nat) : pairIx g u + 6 * k = pairIx g (u + k) := by
  unfold pairIx
  omega

/-- The pair index of the next pairs (`add.s32 …, %r1795, 6 k`). -/
theorem pairIx_words {u : Nat} (hu : u < pairs g) :
    addi (W (pairIx g u)) 6 = W (pairIx g (u + 1)) ∧
    addi (W (pairIx g u)) 12 = W (pairIx g (u + 2)) ∧
    addi (W (pairIx g u)) 18 = W (pairIx g (u + 3)) ∧
    addi (W (pairIx g u)) 24 = W (pairIx g (u + 4)) := by
  have h := pairIx_lt hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← pairIx_step g u 1]; exact addi_W (n := 6) (by decide) (by omega)
  · rw [← pairIx_step g u 2]; exact addi_W (n := 12) (by decide) (by omega)
  · rw [← pairIx_step g u 3]; exact addi_W (n := 18) (by decide) (by omega)
  · rw [← pairIx_step g u 4]; exact addi_W (n := 24) (by decide) (by omega)

theorem cnt_word {u : Nat} (hu : u < 3) : addi (W u) 1 = W (u + 1) :=
  addi_W (n := 1) (by decide) (by omega)

theorem first_test_all : ∀ r < 2, ∀ u < 3,
    scmpi .ne .b (xor32 (W (u + 1)) (W r)) 2 = decide (u + 1 ≠ r + 2) := by decide +kernel

/-- **The exit test of the first loop** (`xor.b32` with the remainder word, `setp.ne.b32 …,
2`): the loop continues until its round counter is `head g`. -/
theorem first_test {u : Nat} (hu : u < head g) :
    scmpi .ne .b (xor32 (W (u + 1)) (W (rem4 g))) 2 = decide (u + 1 ≠ head g) := by
  have h := first_test_all _ (rem4_lt g) u (by have := head_le g; omega)
  rw [h, head_eq]

/-- **The exit test of the second loop** (`setp.lt.u32 %p29, %r1795, 232`). -/
theorem second_test {u : Nat} (hu : u < pairs g) :
    scmpi .lt .u (W (pairIx g u)) 232 = decide (pairIx g u < 232) := by
  have := pairIx_lt hu
  rw [scmpi_lt_u_W (by omega) (by decide) (by decide)]
  rfl

/-- The second loop continues exactly in its first nine rounds. -/
theorem second_iff {u m : Nat} (hm : m < 10) (hu : u = head g + 4 * m) :
    pairIx g u < 232 ↔ m < 9 := by
  have := warp_lt g
  subst hu
  unfold pairIx head
  split_ifs <;> omega

/-- `setp.gt.u32 %p30, %r1, 127` (instruction 619): the thread is no compute thread. -/
theorem tid_gt127 (g : Nat) : scmpi .gt .u (W (tid g)) 127 = decide (127 < tid g) := by
  have := tid_lt g
  rw [scmpi_gt_u_W (by omega) (by decide) (by decide)]
  rfl

/-! ### The base of the carry loads -/

theorem carry_word_all : ∀ t < 192,
    or32 (or32 (andi (shl (W t) 4) 48) (W (t % 32 / 4))) (shl (W (t / 32)) 8) =
      W (256 * (t / 32) + 16 * (t % 32 % 4) + t % 32 / 4) := by decide +kernel

/-- The index `%r358` of a compute thread's block of carries (instructions 622 to 626). -/
theorem carry_word (g : Nat) :
    or32 (or32 (andi (shl (W (tid g)) 4) 48) (W (lane g / 4))) (shl (W (warp g)) 8) =
      W (256 * warp g + 16 * (lane g % 4) + lane g / 4) :=
  carry_word_all (tid g) (tid_lt g)

theorem carry_quad (g : Nat) :
    mulWide .u (W (256 * warp g + 16 * (lane g % 4) + lane g / 4)) 4 =
      W (1024 * warp g + 64 * (lane g % 4) + 4 * (lane g / 4)) := by
  have := warp_lt g
  have := lane_lt g
  rw [quad_word (by omega)]
  congr 1
  omega

/-! ### Addresses -/

/-- The address the pointer code leaves is the swizzled address of the element. -/
theorem rd_norm (P : Params) (e : Nat) : swzN (P.sharedBase + 4 * e + 32768) = rdAddr P e := by
  unfold rdAddr
  congr 1
  omega

/-- **The read of an element is four bytes of the FP32 buffer** (offsets 32768 to 98304 of
the window), at a multiple of four. -/
theorem rdAddr_frame (hpre : Pre P L mem0) {e : Nat} (he : e < 16384) :
    P.sharedBase + 32768 ≤ rdAddr P e ∧ rdAddr P e + 4 ≤ P.sharedBase + 98304 ∧
      rdAddr P e % 4 = 0 ∧ rdAddr P e < 2 ^ 32 := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  have h1 : P.sharedBase + 32768 ≤ rdAddr P e := swzN_lo (by omega) (by omega)
  have h2 : rdAddr P e + 4 ≤ P.sharedBase + 98304 := swzN_hi (by omega) (by omega) (by omega)
  have h3 : rdAddr P e % 4 = 0 := swzN_mod4 (by omega)
  exact ⟨h1, h2, h3, by omega⟩

/-- **The write of an element is two bytes of `state_acc`** (the first 32768 bytes of the
window), at an even address. -/
theorem wrAddr_frame (hpre : Pre P L mem0) {e : Nat} (he : e < 16384) :
    P.sharedBase ≤ wrAddr P e ∧ wrAddr P e + 2 ≤ P.sharedBase + 32768 ∧
      wrAddr P e % 2 = 0 ∧ wrAddr P e < 2 ^ 32 := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  unfold wrAddr
  omega

/-! ### Which thread converts which element -/

/-- **The thread (its index in the block) that converts element `e`**: the pair index is
`16 (e / 64 % 16) + e / 1024`, its remainder modulo 6 the warp, and the lane is
`e % 64 / 2`. -/
def convOwner (e : Nat) : Nat := 32 * ((16 * (e / 64 % 16) + e / 1024) % 6) + e % 64 / 2

/-- The ordinal, among the elements of its thread, of element `e`. -/
def convOrd (e : Nat) : Nat := 2 * ((16 * (e / 64 % 16) + e / 1024) / 6) + e % 2

/-- An element of a thread determines the thread and the element's ordinal. -/
theorem slotOf_owner {i : Nat} (hi : i < 2 * pairs g) :
    slotOf g i < 16384 ∧ convOwner (slotOf g i) = tid g ∧ convOrd (slotOf g i) = i := by
  have hp := pairIx_lt (g := g) (u := i / 2) (by omega)
  have hl := lane_lt g
  have ht := tid_eq g
  have hw := warp_lt g
  have hq' : pairIx g (i / 2) = warp g + 6 * (i / 2) := rfl
  generalize pairIx g (i / 2) = q at hp hq'
  have e0 : slotOf g i = 1024 * (q % 16) + 64 * (q / 16) + 2 * lane g + i % 2 := by
    unfold slotOf slot0 pairIx
    rw [← hq']
  have e1 : (1024 * (q % 16) + 64 * (q / 16) + 2 * lane g + i % 2) / 1024 = q % 16 := by omega
  have e2 : (1024 * (q % 16) + 64 * (q / 16) + 2 * lane g + i % 2) / 64 % 16 = q / 16 := by
    omega
  have e3 : (1024 * (q % 16) + 64 * (q / 16) + 2 * lane g + i % 2) % 64 / 2 = lane g := by
    omega
  have e4 : (1024 * (q % 16) + 64 * (q / 16) + 2 * lane g + i % 2) % 2 = i % 2 := by omega
  have e5 : 16 * (q / 16) + q % 16 = q := by omega
  rw [e0]
  unfold convOwner convOrd
  rw [e1, e2, e3, e4, e5]
  omega

/-- **Every element of a block is converted**: element `e` is element `convOrd e` of the
thread with index `convOwner e`. -/
theorem slot_cover {e : Nat} (he : e < 16384) (hg : tid g = convOwner e) :
    convOrd e < 2 * pairs g ∧ slotOf g (convOrd e) = e := by
  have hl := lane_lt g
  have ht := tid_eq g
  have hw := warp_lt g
  unfold convOwner at hg
  unfold convOrd
  obtain ⟨q, hq⟩ : ∃ q, q = 16 * (e / 64 % 16) + e / 1024 := ⟨_, rfl⟩
  rw [← hq] at hg ⊢
  have hq2 : q < 256 := by omega
  have hwq : warp g = q % 6 := by omega
  have hlq : lane g = e % 64 / 2 := by omega
  have e1 : (2 * (q / 6) + e % 2) / 2 = q / 6 := by omega
  have e2 : (2 * (q / 6) + e % 2) % 2 = e % 2 := by omega
  have e3 : pairIx g (q / 6) = q := by unfold pairIx; omega
  constructor
  · unfold pairs head
    split_ifs <;> omega
  · have e4 : q % 16 = e / 1024 := by omega
    have e5 : q / 16 = e / 64 % 16 := by omega
    simp only [slotOf, slot0, e1, e2, e3, e4, e5, hlq]
    omega

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
