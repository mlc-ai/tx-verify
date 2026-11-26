-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Swizzle
public import Lemmas.Flow.Arith32WordW
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads

@[expose] public section

/-! # Warpgroup 0's shared address words as workspace offsets

The address words of the shape table's shared accesses (`Ev.lean`) name, for a thread of the
warpgroup (`tidOf L g < 128`; `t` its index, `w = t / 32` its warp, `t % 32` its lane), the
workspace bytes (`wsLoc`) at these offsets:

* `r13_loc`: the row-maximum and row-sum store, `221184 + 4 t`;
* `r14_loc`: the other warp pair's row, `221184 + (4 t ^^^ 256)`;
* `r17_loc`: the peer read `k`, `204800 + 4096 w + 16 (t % 32) + 512 k`;
* `pst_loc`: the peer store `k`, `204800 + 4096 (w ^^^ 2) + 16 (t % 32) + 512 k`;
* `r16_loc`: the P store `k`, `204800 + 4096 (w / 2) + 512 (w % 2) + 16 (t % 32) + 1024 k`;
* `vm_loc`: the valid-mask word of slot `v`, `221696 + 8 v + 4 (w / 2)`;
* `otma_loc`: output chunk `c`'s TMA source, `65536 + 16384 w + wg0OutOff c`.

The shared base is below `2 ^ 32 - 222952` (`sharedBase_lt`), so no sum wraps. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem lor512 {x : Nat} (hx : x < 512) : x ||| 512 = x + 512 := by
  rw [Nat.or_comm, lor_eq_add 9 (by decide) hx, Nat.add_comm]

theorem lor4096 {x : Nat} (hx : x < 4096) : 4096 ||| x = 4096 + x :=
  lor_eq_add 12 (by decide) hx

/-- The warp of a thread of the warpgroup, by cases. -/
theorem warp_cases {t : Nat} (ht : t < 128) :
    t / 32 = 0 ∨ t / 32 = 1 ∨ t / 32 = 2 ∨ t / 32 = 3 := by
  omega

theorem r13_loc (hp : Pre P L m) (ht : tidOf L g < 128) :
    smLoc L g (r13W L g) 221184 = wsLoc L (g / L.block) (221184 + 4 * tidOf L g) := by
  have hS := sharedBase_lt hp
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  simp only [r13W, r5W, tw, sbw, add32, shl, andi, r32, i32, truncBits]
  nf_simp [land127]
  omega

theorem r14_loc (hp : Pre P L m) (ht : tidOf L g < 128) :
    smLoc L g (r14W L g) 221184 = wsLoc L (g / L.block) (221184 + (4 * tidOf L g ^^^ 256)) := by
  have hS := sharedBase_lt hp
  have hx : 4 * tidOf L g ^^^ 256 < 512 := Nat.xor_lt_two_pow (n := 9) (by omega) (by omega)
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  simp only [r14W, r5W, tw, sbw, add32, xor32, shl, andi, r32, i32, truncBits]
  nf_simp [land127, nf_xor]
  have e : tidOf L g % 4294967296 % 128 % 4294967296 * 4 % 4294967296 = 4 * tidOf L g := by
    omega
  rw [e]
  omega

theorem r17_loc (hp : Pre P L m) (ht : tidOf L g < 128) {k : Nat} (hk : k < 8) :
    smLoc L g (r17W L g (warpW L g)) (204800 + 512 * (k : Int)) = wsLoc L (g / L.block)
      (204800 + 4096 * (tidOf L g / 32) + 16 * (tidOf L g % 32) + 512 * k) := by
  have hS := sharedBase_lt hp
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  simp only [r17W, r8W, warpW, warpOf, tw, sbw, add32, shl, andi, r32, i32, truncBits]
  nf_simp [land31]
  omega

theorem pst_loc (hp : Pre P L m) (ht : tidOf L g < 128) (k : Fin 8) :
    smLoc L g (pstW L g (warpW L g) k) 0 = wsLoc L (g / L.block)
      (204800 + 4096 * (tidOf L g / 32 ^^^ 2) + 16 * (tidOf L g % 32) + 512 * k.val) := by
  have hS := sharedBase_lt hp
  have hk := k.isLt
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  simp only [pstW, r507W, r8W, warpW, warpOf, tw, sbw, addi, add32, xor32, shl, andi, r32,
    i32, truncBits]
  nf_simp [land31, nf_xor]
  rcases warp_cases ht with h | h | h | h <;>
  simp only [h, Nat.reduceMod, Nat.reduceMul, Nat.reduceXor] <;> omega

theorem r16_loc (hp : Pre P L m) (ht : tidOf L g < 128) {k : Nat} (hk : k < 4) :
    smLoc L g (r16W L g (warpW L g)) (204800 + 1024 * (k : Int)) = wsLoc L (g / L.block)
      (204800 + 4096 * (tidOf L g / 32 / 2) + 512 * (tidOf L g / 32 % 2) +
        16 * (tidOf L g % 32) + 1024 * k) := by
  have hS := sharedBase_lt hp
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  simp only [r16W, r8W, warpW, warpOf, tw, sbw, add32, or32, shl, shru, andi, r32, i32,
    truncBits]
  nf_simp [land31]
  have hl : tidOf L g % 4294967296 % 32 % 4294967296 * 16 % 4294967296 =
      16 * (tidOf L g % 32) := by omega
  rw [hl]
  have hl2 : 16 * (tidOf L g % 32) % 4294967296 = 16 * (tidOf L g % 32) := by omega
  have h5 : 16 * (tidOf L g % 32) < 512 := by omega
  rcases warp_cases ht with h | h | h | h <;>
  simp only [h, Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceAnd,
    Nat.or_zero, Nat.zero_or, hl2, lor512 h5] <;>
  (try simp (disch := omega) only [lor4096]) <;> omega

/-- The pair test of `%r18` for each warp. -/
theorem pair_test : scmpi .gt .s (BitVec.ofNat 64 0) 1 = false ∧
    scmpi .gt .s (BitVec.ofNat 64 1) 1 = false ∧ scmpi .gt .s (BitVec.ofNat 64 2) 1 = true ∧
    scmpi .gt .s (BitVec.ofNat 64 3) 1 = true := by
  decide +kernel

theorem vm_loc (hp : Pre P L m) (ht : tidOf L g < 128) {d : D} {v : Nat} (hv : d.vs = W v)
    (hv4 : v < 4) :
    smLoc L g (add32 (r19W L d) (r18W (warpW L g))) 221696 =
      wsLoc L (g / L.block) (221696 + 8 * v + 4 * (tidOf L g / 32 / 2)) := by
  have hS := sharedBase_lt hp
  obtain ⟨c0, c1, c2, c3⟩ := pair_test
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  simp only [r19W, r18W, hv, W, warpW, warpOf, sbw]
  rcases warp_cases ht with h | h | h | h <;>
  simp only [h, c0, c1, c2, c3, sel, Bool.false_eq_true, ↓reduceIte, add32, shl, r32, i32,
    truncBits] <;> nf_simp <;> omega

/-- Output chunk `c`'s TMA source: `65536 + 16384 w` plus the chunk's offset. -/
theorem otma_loc (hp : Pre P L m) (ht : tidOf L g < 128) (c : Fin 4) :
    smLoc L g (otmaW L (warpW L g) c) 0 =
      wsLoc L (g / L.block) (65536 + 16384 * (tidOf L g / 32) + MemRow.wg0OutOff c.val) := by
  have hS := sharedBase_lt hp
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  fin_cases c <;>
  simp only [otmaW, otmaOff, MemRow.wg0OutOff, r25W, warpW, warpOf, sbw, addi, add32, shl, r32,
    i32, truncBits, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;>
  nf_simp <;> omega

/-- The staging row's byte offset of a thread of the warpgroup: its quadrant and its row. -/
theorem stQuad_eq (ht : tidOf L g < 128) :
    (stQuad L g).toNat = 16384 * (tidOf L g / 64) + 128 * (tidOf L g % 64) := by
  have key : ∀ t < 128, (mulWide .u (or32 (andi (shl (BitVec.ofNat 64 t) 6) 4032)
      (andi (shl (BitVec.ofNat 64 t) 7) 8192)) 2).toNat = 16384 * (t / 64) + 128 * (t % 64) := by
    decide +kernel
  exact key _ ht

theorem land112 (x : Nat) : x &&& 112 = 16 * (x % 128 / 16 % 8) := by
  have h1 : x &&& 112 = x % 128 &&& 112 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_mod_two_pow _ 7]
    by_cases hi : i < 7
    · simp [hi]
    · have : (112 : Nat).testBit i = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (by decide : 112 < 2 ^ 7) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  have key : ∀ y < 128, y &&& 112 = 16 * (y / 16 % 8) := by decide
  rw [h1, key _ (Nat.mod_lt _ (by decide))]

/-- **The staging pointer's byte**: chunk `k` of the thread's staging row at its swizzled place,
the row's three low bits xored into the chunk index (SW128). -/
theorem stW_eq (hp : Pre P L m) (ht : tidOf L g < 128) {k : Nat} (hk : k < 8) :
    stW L g k = L.sharedBase + (65536 + 16384 * (tidOf L g / 64) + 128 * (tidOf L g % 64) +
      16 * (k ^^^ tidOf L g % 8)) := by
  have hS : L.sharedBase % 1024 = 0 := by rw [hp.sharedBase]; exact hp.sharedAlignment
  have hk16 : 16 * k < 2 ^ 7 := by omega
  unfold stW Control.stM stP
  rw [stQuad_eq ht, land112]
  generalize tidOf L g = t at ht ⊢
  have hm : (L.sharedBase + (16384 * (t / 64) + 128 * (t % 64)) + (65536 + 16 * k)) / 8 % 128 /
      16 % 8 = t % 8 := by omega
  rw [hm]
  have hB : (L.sharedBase + 65536 + 16384 * (t / 64) + 128 * (t % 64)) % 2 ^ 7 = 0 := by omega
  have hx : 16 * (t % 8) ^^^ 16 * k = 16 * (k ^^^ t % 8) := by
    have key : ∀ a < 8, ∀ b < 8, 16 * a ^^^ 16 * b = 16 * (b ^^^ a) := by decide
    exact key _ (Nat.mod_lt _ (by decide)) _ hk
  have hlt : 16 * (t % 8) ^^^ 16 * k < 2 ^ 7 :=
    Nat.xor_lt_two_pow (by omega) hk16
  rw [show L.sharedBase + (16384 * (t / 64) + 128 * (t % 64)) + (65536 + 16 * k) =
    (L.sharedBase + 65536 + 16384 * (t / 64) + 128 * (t % 64)) ^^^ 16 * k by
      rw [xor_eq_add 7 hB hk16]; omega]
  rw [← Nat.xor_assoc, Nat.xor_comm (16 * (t % 8)), Nat.xor_assoc, xor_eq_add 7 hB hlt, hx]
  omega

/-- **The LSE address** (`%rd585`): row `64 (s_q ctaid.y + ctaid.x) + t` of the LSE output, as a
64-bit word. -/
theorem lseAddr_eq (hp : Pre P L m) :
    lseAddr P L g = W (P.lseBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) * 64 +
      tidOf L g % 128)) := by
  have hs := hp.strideRange
  have hr := hp.tensorRange.2.2
  have h1 := hp.sqPos
  have h2 := hp.bPos
  obtain ⟨hx, hy⟩ := ctaid_lt hp g
  have hb := hp.bLt
  have ht := tidOf_lt hp g
  have hl : P.lseBase < 2 ^ 64 := by
    have : 0 < lseBytes P := by unfold lseBytes; positivity
    omega
  have e1 : pw (P.s_q * 64) = W (P.s_q * 64) := by
    simp only [pw, leNat_eq, pow_zero, Nat.div_one]; congr 1; omega
  have e2 : pw 64 = W 64 := by simp only [pw, leNat_eq, pow_zero, Nat.div_one]; rfl
  have e3 : pw8 P.lseBase = W P.lseBase := by
    simp only [pw8, leNat_eq, pow_zero, Nat.div_one]; congr 1; omega
  have e4 : r5W L g = W (tidOf L g % 128) := andi_W_low (k := 7) ht (by decide)
  have e5 : r64 (W P.lseBase) = W P.lseBase := by
    apply BitVec.eq_of_toNat_eq; simp only [r64, truncBits, W, BitVec.toNat_ofNat]; omega
  have e6 : zext (W (tidOf L g % 128)) = W (tidOf L g % 128) := by
    apply BitVec.eq_of_toNat_eq; simp only [zext, r32, truncBits, W, BitVec.toNat_ofNat]; omega
  unfold lseAddr lseIdx lseRow lseBlk
  rw [e1, e2, e3, e4, e5, e6, show r2W L g = W (ctaidY L g) from rfl,
    show BitVec.ofNat 64 (ctaidX L g) = W (ctaidX L g) from rfl,
    mulWideR_s_W (by omega) (by omega), mulWideR_s_W (by omega) (by omega), add64_W, add64_W,
    shl64_2_W, add64_W]
  congr 1
  ring

/-- A memory event is no undefined behaviour. -/
theorem memEvent_noUb {e : Event} (hm : MemRow.MemEvent e) (f : Fault) : e.kind ≠ .ub f := by
  intro hf
  rcases hm with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [hf] at h <;> cases h

theorem wsLoc_at (c o j : Nat) : (wsLoc L c o).at j = wsLoc L c (o + j) := by
  simp only [wsLoc, Loc.at, Nat.add_assoc]

/-- **A read of the table at a word naming a workspace offset** is the read of its element. -/
theorem rdAt_ws {x : BitVec 64} {off : Int} {n j c o : Nat} {e : Event}
    (hm : MemRow.MemEvent e) (h : RdAt L g x off n j e) (hx : smLoc L g x off = wsLoc L c o) :
    ∃ a bs, e.kind = .rd a bs ∧ MemRow.WsAcc L c (o + n * j) n a := by
  rcases h with ⟨a, bs, hk, hl, hs⟩ | ⟨f, hf⟩
  · exact ⟨a, bs, hk, by rw [hl, hx, wsLoc_at], hs⟩
  · exact absurd hf (memEvent_noUb hm f)

/-- **A write of the table at a word naming a workspace offset** is the write of its element. -/
theorem wrAt_ws {x : BitVec 64} {off : Int} {n j c o : Nat} {e : Event}
    (hm : MemRow.MemEvent e) (h : WrAt L g x off n j e) (hx : smLoc L g x off = wsLoc L c o) :
    ∃ a bs, e.kind = .wr a bs ∧ MemRow.WsAcc L c (o + n * j) n a := by
  rcases h with ⟨a, bs, hk, hl, hs⟩ | ⟨f, hf⟩
  · exact ⟨a, bs, hk, by rw [hl, hx, wsLoc_at], hs⟩
  · exact absurd hf (memEvent_noUb hm f)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
