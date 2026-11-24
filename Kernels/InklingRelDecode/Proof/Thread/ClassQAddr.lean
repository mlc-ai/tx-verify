-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ClassBtAddr
public import Kernels.InklingRelDecode.Proof.Thread.ProBSpec

@[expose] public section

/-!
# The addresses of the prologue's query loads

The prologue's 64 `ld.global.b16` (`ldqSite k`, in four groups of 16 for the tile rows
`m = (tid / 8) % 16 + 16 G`, `G = k / 16`) read the elements of `Q` at
`q_base + 2 ((cu0 + m / 6) * stride_q + (6 kv_head + m % 6) * 128 + col)`, with the column
`col = 8 (tid % 8) + 64 ((k % 16) / 8) + k % 8`: the token of a row is `m / 6` and its head within
the group is `m % 6`, which the code computes with 16-bit `mul.hi` and add chains
(`r183_val` and its siblings, decided for the 128 thread indices), and the address registers are a
64-bit `mad.wide` of the 32-bit row offset and the base (`qbase_gen`, `rd3_val` to `rd6_val`) plus
the constant offset of the load (`ldq_reg`).

* `ldq_addr`: the address of load `k` in closed form, modulo `2 ^ 64`, where the 32-bit
  arithmetic does not wrap;
* `ldq_guard_tok`: the guard of a load says the token of its row is below `q_len`;
* `ldq_reads`: so the two bytes of a load whose guard holds are in `Params.reads` (the first
  disjunct: a valid token, a head below 12, a column below 128).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

theorem wMulWideS32_ofNat (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    wMulWideS32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a * b) := by
  unfold wMulWideS32
  have e0 : ((some IType.s == some IType.s) = true) := by decide
  have ea : a % 2 ^ 32 = a := Nat.mod_eq_of_lt (by omega)
  have eb : b % 2 ^ 32 = b := Nat.mod_eq_of_lt (by omega)
  have ea' : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have eb' : b % 2 ^ 64 = b := Nat.mod_eq_of_lt (by omega)
  have e1 : a % 2 ^ 64 % 2 ^ 32 % 2 ^ 32 = a := by omega
  have e2 : b % 2 ^ 64 % 2 ^ 32 % 2 ^ 32 = b := by omega
  simp only [e0, ↓reduceIte, tos32, truncBits, BitVec.toNat_ofNat, e1, e2, ha, hb,
    show 2 * 32 = 64 by rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  rw [show ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) by push_cast; rfl]
  omega

theorem wMadWideU32_ofNat (a b c : Nat) :
    wMadWideU32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c) =
      BitVec.ofNat 64 ((a % 2 ^ 32) * (b % 2 ^ 32) + c) := by
  unfold wMadWideU32 intBits intOf
  simp only [truncBits_ofNat _ _ (by omega : 32 ≤ 64), truncBits_ofNat 64 _ (by omega : 64 ≤ 64),
    show 2 * 32 = 64 by rfl, show ¬ (IType.u = IType.s) by decide, ite_false, BitVec.toNat_ofNat]
  have e1 : a % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := by omega
  have e2 : b % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 = b % 2 ^ 32 := by omega
  have e3 : c % 2 ^ 64 % 2 ^ 64 % 2 ^ 64 = c % 2 ^ 64 := by omega
  simp only [e1, e2, e3]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  rw [show ((a % 2 ^ 32 : Nat) : Int) * ((b % 2 ^ 32 : Nat) : Int) =
    ((a % 2 ^ 32 * (b % 2 ^ 32) : Nat) : Int) by push_cast; rfl]
  generalize a % 2 ^ 32 * (b % 2 ^ 32) = p
  omega

theorem ofInt_two : BitVec.ofInt 64 2 = BitVec.ofNat 64 2 := nfI 2

/-- Finite facts of the thread index: the 16-bit token and head chains of the query loads. -/
theorem r183_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r183 L g dt = BitVec.ofNat 64 ((tidOf L g / 8 % 16) / 6) := by
  simp only [v_r183, v_rs8, v_rs1, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem r182_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r182 L g dt = BitVec.ofNat 64 ((tidOf L g / 8 % 16 + 16) / 6) := by
  simp only [v_r182, v_rs7, v_rs2, v_rs1, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem r181_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r181 L g dt = BitVec.ofNat 64 ((tidOf L g / 8 % 16 + 32) / 6) := by
  simp only [v_r181, v_rs6, v_rs3, v_rs1, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem r180_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r180 L g dt = BitVec.ofNat 64 ((tidOf L g / 8 % 16 + 48) / 6) := by
  simp only [v_r180, v_rs5, v_rs4, v_r178, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem r189_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r189 L g dt = BitVec.ofNat 64 ((tidOf L g / 8 % 16) % 6) := by
  simp only [v_r189, v_r188, v_rs16, v_rs15, v_rs8, v_rs1, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem r191_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r191 L g dt = BitVec.ofNat 64 ((tidOf L g / 8 % 16 + 16) % 6) := by
  simp only [v_r191, v_r190, v_rs14, v_rs13, v_rs7, v_rs2, v_rs1, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem r193_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r193 L g dt = BitVec.ofNat 64 ((tidOf L g / 8 % 16 + 32) % 6) := by
  simp only [v_r193, v_r192, v_rs12, v_rs11, v_rs6, v_rs3, v_rs1, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem r195_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r195 L g dt = BitVec.ofNat 64 ((tidOf L g / 8 % 16 + 48) % 6) := by
  simp only [v_r195, v_r194, v_rs10, v_rs9, v_rs5, v_rs4, v_r178, v_r177, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem r28_val (L : Launch) (g : Nat) (dt : Dat) (h : tidOf L g < 128) :
    v_r28 L g dt = BitVec.ofNat 64 (8 * (tidOf L g % 8)) := by
  simp only [v_r28, v_r179, v_r1]
  generalize tidOf L g = t at *
  revert t
  decide +kernel

theorem wShl64_one (a : Nat) :
    wShl64 (BitVec.ofNat 64 a) (BitVec.ofInt 64 1) = BitVec.ofNat 64 (a * 2) := by
  have l : BitVec.ofInt 64 1 = BitVec.ofNat 64 1 := nfI 1
  have h1 : (truncBits 32 (BitVec.ofNat 64 1)).toNat = 1 := by decide
  unfold wShl64
  rw [l, h1]
  simp only [show ¬ (1 ≥ 64) by omega, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have h2 : a % 2 ^ 64 % 2 ^ 64 % 2 ^ 64 = a % 2 ^ 64 := by omega
  rw [h2]
  omega

/-- The base address of a group of query loads. -/
theorem qbase_gen (x0 x16 : BitVec 64) (cu0 T H y6 : Nat) (hc : cu0 + T < 2 ^ 31)
    (hs : x16.toNat < 2 ^ 31) (hy : y6 + H < 2 ^ 24) :
    wMadWideU32 (wShl32 (wAdd32 (BitVec.ofNat 64 y6) (BitVec.ofNat 64 H)) (BitVec.ofInt 64 7))
      (BitVec.ofInt 64 2)
      (wAdd64 (truncBits 64 x0) (wShl64 (wMulWideS32 (truncBits 32 x16)
        (wAdd32 (BitVec.ofNat 64 cu0) (BitVec.ofNat 64 T))) (BitVec.ofInt 64 1))) =
    BitVec.ofNat 64 (x0.toNat + 2 * (x16.toNat * (cu0 + T)) + 2 * ((y6 + H) * 128)) := by
  have e1 : x16.toNat % 2 ^ 32 = x16.toNat := Nat.mod_eq_of_lt (by omega)
  have e2 : (cu0 + T) % 2 ^ 32 = cu0 + T := Nat.mod_eq_of_lt (by omega)
  have h16 : truncBits 32 x16 = BitVec.ofNat 64 x16.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat]
    have : x16.toNat < 2 ^ 64 := by omega
    omega
  rw [wAdd32_ofNat, wAdd32_ofNat, e2, h16, wMulWideS32_ofNat _ _ (by omega) (by omega),
    wShl64_one, truncBits64_eq, ofInt_two, wAdd64_ofNat, ofInt_seven,
    wShl32_ofNat _ 7 (by norm_num), wMadWideU32_ofNat]
  have e3 : (y6 + H) % 2 ^ 32 = y6 + H := Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, e3]
  have e4 : (y6 + H) * 2 ^ 7 % 2 ^ 32 = (y6 + H) * 128 := Nat.mod_eq_of_lt (by omega)
  have e5 : (y6 + H) * 128 % 2 ^ 32 = (y6 + H) * 128 := Nat.mod_eq_of_lt (by omega)
  have e6 : (2 : Nat) % 2 ^ 32 = 2 := by norm_num
  have e7 : (y6 + H) * 2 ^ 7 % 2 ^ 32 % 2 ^ 32 = (y6 + H) * 128 := by omega
  rw [e7, e6]
  generalize x16.toNat * (cu0 + T) = p
  generalize (y6 + H) * 128 = q
  omega

theorem r29_val (L : Launch) (g : Nat) (dt : Dat) (hy : cta L g .y < 2 ^ 24) :
    v_r29 L g dt = BitVec.ofNat 64 (cta L g .y * 6) := by
  have l : BitVec.ofInt 64 6 = BitVec.ofNat 64 6 := nfI 6
  have h1 : cta L g .y % 2 ^ 32 = cta L g .y := Nat.mod_eq_of_lt (by omega)
  simp only [v_r29, v_r18, wCta_eq, l, wMulLo32_ofNat, h1]
  congr 1
  omega

theorem rd3_val (L : Launch) (g : Nat) (dt : Dat) (ht : tidOf L g < 128) (hy : cta L g .y ≤ 1)
    (hc : dt.cu0 + (tidOf L g / 8 % 16) / 6 < 2 ^ 31) (hs : dt.pro.x16.toNat < 2 ^ 31) :
    v_rd3 L g dt = BitVec.ofNat 64 (dt.pro.x0.toNat + 2 * (dt.pro.x16.toNat *
      (dt.cu0 + (tidOf L g / 8 % 16) / 6)) +
      2 * ((cta L g .y * 6 + (tidOf L g / 8 % 16) % 6) * 128)) := by
  simp only [v_rd3, v_r200, v_r196, v_rd116, v_rd115, v_rd114, v_r184, v_r65, v_rd70, v_r149,
    r183_val L g dt ht, r189_val L g dt ht, r29_val L g dt (by omega)]
  exact qbase_gen _ _ _ _ _ _ hc hs (by omega)

theorem rd4_val (L : Launch) (g : Nat) (dt : Dat) (ht : tidOf L g < 128) (hy : cta L g .y ≤ 1)
    (hc : dt.cu0 + (tidOf L g / 8 % 16 + 16) / 6 < 2 ^ 31) (hs : dt.pro.x16.toNat < 2 ^ 31) :
    v_rd4 L g dt = BitVec.ofNat 64 (dt.pro.x0.toNat + 2 * (dt.pro.x16.toNat *
      (dt.cu0 + (tidOf L g / 8 % 16 + 16) / 6)) +
      2 * ((cta L g .y * 6 + (tidOf L g / 8 % 16 + 16) % 6) * 128)) := by
  simp only [v_rd4, v_r201, v_r197, v_rd118, v_rd117, v_rd113, v_r185, v_r65, v_rd70, v_r149,
    r182_val L g dt ht, r191_val L g dt ht, r29_val L g dt (by omega)]
  exact qbase_gen _ _ _ _ _ _ hc hs (by omega)

theorem rd5_val (L : Launch) (g : Nat) (dt : Dat) (ht : tidOf L g < 128) (hy : cta L g .y ≤ 1)
    (hc : dt.cu0 + (tidOf L g / 8 % 16 + 32) / 6 < 2 ^ 31) (hs : dt.pro.x16.toNat < 2 ^ 31) :
    v_rd5 L g dt = BitVec.ofNat 64 (dt.pro.x0.toNat + 2 * (dt.pro.x16.toNat *
      (dt.cu0 + (tidOf L g / 8 % 16 + 32) / 6)) +
      2 * ((cta L g .y * 6 + (tidOf L g / 8 % 16 + 32) % 6) * 128)) := by
  simp only [v_rd5, v_r202, v_r198, v_rd120, v_rd119, v_rd112, v_r186, v_r65, v_rd70, v_r149,
    r181_val L g dt ht, r193_val L g dt ht, r29_val L g dt (by omega)]
  exact qbase_gen _ _ _ _ _ _ hc hs (by omega)

theorem rd6_val (L : Launch) (g : Nat) (dt : Dat) (ht : tidOf L g < 128) (hy : cta L g .y ≤ 1)
    (hc : dt.cu0 + (tidOf L g / 8 % 16 + 48) / 6 < 2 ^ 31) (hs : dt.pro.x16.toNat < 2 ^ 31) :
    v_rd6 L g dt = BitVec.ofNat 64 (dt.pro.x0.toNat + 2 * (dt.pro.x16.toNat *
      (dt.cu0 + (tidOf L g / 8 % 16 + 48) / 6)) +
      2 * ((cta L g .y * 6 + (tidOf L g / 8 % 16 + 48) % 6) * 128)) := by
  simp only [v_rd6, v_r203, v_r199, v_rd122, v_rd121, v_rd111, v_r187, v_r65, v_rd70, v_r149,
    r180_val L g dt ht, r195_val L g dt ht, r29_val L g dt (by omega)]
  exact qbase_gen _ _ _ _ _ _ hc hs (by omega)

theorem rd257_val (L : Launch) (g : Nat) (dt : Dat) (ht : tidOf L g < 128) :
    v_rd257 L g dt = BitVec.ofNat 64 (8 * (tidOf L g % 8) * 2) := by
  have l : BitVec.ofInt 64 2 = BitVec.ofNat 64 2 := nfI 2
  rw [v_rd257, r28_val L g dt ht, l, wMulWideU32_ofNat]
  congr 1
  omega

theorem wAdd64_toNat (a b : BitVec 64) : (wAdd64 a b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := by
  simp only [wAdd64, truncBits, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The offset of the `j`-th load of a group of query loads. -/
def qOff (j : Nat) : Nat := if j < 8 then 2 * j else 128 + 2 * (j - 8)

theorem ldq_reg0 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ j < 16, ∃ x : BitVec 64, valueOf L g dt (gloadBase (ldqSite (0 + j)).pc) = .bits 64 x ∧
      x.toNat = ((v_rd3 L g dt).toNat + (v_rd257 L g dt).toNat + qOff j) % 2 ^ 64 := by
  intro j hj
  interval_cases j
  all_goals
    refine ⟨_, rfl, ?_⟩
    simp only [v_rd129, v_rd130, v_rd131, v_rd132, v_rd133, v_rd134, v_rd135, v_rd136, v_rd137,
      v_rd138, v_rd139, v_rd140, v_rd141, v_rd142, v_rd143, v_rd144,
      wAdd64_toNat, qOff, BitVec.toNat_ofInt]
    norm_num

theorem ldq_reg1 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ j < 16, ∃ x : BitVec 64, valueOf L g dt (gloadBase (ldqSite (16 + j)).pc) = .bits 64 x ∧
      x.toNat = ((v_rd4 L g dt).toNat + (v_rd257 L g dt).toNat + qOff j) % 2 ^ 64 := by
  intro j hj
  interval_cases j
  all_goals
    refine ⟨_, rfl, ?_⟩
    simp only [v_rd145, v_rd146, v_rd147, v_rd148, v_rd149, v_rd150, v_rd151, v_rd152, v_rd153,
      v_rd154, v_rd155, v_rd156, v_rd157, v_rd158, v_rd159, v_rd160,
      wAdd64_toNat, qOff, BitVec.toNat_ofInt]
    norm_num

theorem ldq_reg2 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ j < 16, ∃ x : BitVec 64, valueOf L g dt (gloadBase (ldqSite (32 + j)).pc) = .bits 64 x ∧
      x.toNat = ((v_rd5 L g dt).toNat + (v_rd257 L g dt).toNat + qOff j) % 2 ^ 64 := by
  intro j hj
  interval_cases j
  all_goals
    refine ⟨_, rfl, ?_⟩
    simp only [v_rd161, v_rd162, v_rd163, v_rd164, v_rd165, v_rd166, v_rd167, v_rd168, v_rd169,
      v_rd170, v_rd171, v_rd172, v_rd173, v_rd174, v_rd175, v_rd176,
      wAdd64_toNat, qOff, BitVec.toNat_ofInt]
    norm_num

theorem ldq_reg3 (L : Launch) (g : Nat) (dt : Dat) :
    ∀ j < 16, ∃ x : BitVec 64, valueOf L g dt (gloadBase (ldqSite (48 + j)).pc) = .bits 64 x ∧
      x.toNat = ((v_rd6 L g dt).toNat + (v_rd257 L g dt).toNat + qOff j) % 2 ^ 64 := by
  intro j hj
  interval_cases j
  all_goals
    refine ⟨_, rfl, ?_⟩
    simp only [v_rd177, v_rd178, v_rd179, v_rd180, v_rd181, v_rd182, v_rd183, v_rd184, v_rd185,
      v_rd186, v_rd187, v_rd188, v_rd189, v_rd190, v_rd191, v_rd192,
      wAdd64_toNat, qOff, BitVec.toNat_ofInt]
    norm_num


/-- The base register of group `G` of the query loads, as a number. -/
def qReg (L : Launch) (g : Nat) (dt : Dat) : Nat → Nat
  | 0 => (v_rd3 L g dt).toNat
  | 1 => (v_rd4 L g dt).toNat
  | 2 => (v_rd5 L g dt).toNat
  | _ => (v_rd6 L g dt).toNat

theorem ldq_reg (L : Launch) (g : Nat) (dt : Dat) {k : Nat} (hk : k < 64) :
    ∃ x : BitVec 64, valueOf L g dt (gloadBase (ldqSite k).pc) = .bits 64 x ∧
      x.toNat = (qReg L g dt (k / 16) + (v_rd257 L g dt).toNat + qOff (k % 16)) % 2 ^ 64 := by
  have hj : k % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hG : k / 16 = 0 ∨ k / 16 = 1 ∨ k / 16 = 2 ∨ k / 16 = 3 := by omega
  rcases hG with h | h | h | h
  · have e : 16 * 0 + k % 16 = k := by omega
    have := ldq_reg0 L g dt (k % 16) hj
    rw [e] at this
    rw [h]
    exact this
  · have e : 16 * 1 + k % 16 = k := by omega
    have := ldq_reg1 L g dt (k % 16) hj
    rw [e] at this
    rw [h]
    exact this
  · have e : 16 * 2 + k % 16 = k := by omega
    have := ldq_reg2 L g dt (k % 16) hj
    rw [e] at this
    rw [h]
    exact this
  · have e : 16 * 3 + k % 16 = k := by omega
    have := ldq_reg3 L g dt (k % 16) hj
    rw [e] at this
    rw [h]
    exact this

theorem qReg0 (L : Launch) (g : Nat) (dt : Dat) : qReg L g dt 0 = (v_rd3 L g dt).toNat := rfl
theorem qReg1 (L : Launch) (g : Nat) (dt : Dat) : qReg L g dt 1 = (v_rd4 L g dt).toNat := rfl
theorem qReg2 (L : Launch) (g : Nat) (dt : Dat) : qReg L g dt 2 = (v_rd5 L g dt).toNat := rfl
theorem qReg3 (L : Launch) (g : Nat) (dt : Dat) : qReg L g dt 3 = (v_rd6 L g dt).toNat := rfl

theorem qOff_eq (j : Nat) (hj : j < 16) : qOff j = 2 * (j % 8) + 128 * (j / 8) := by
  unfold qOff
  split <;> omega

/-- **The address of query load `k`**: element `(token, head, col)` of `Q`,
`q_base + 2 * ((cu0 + token) * stride_q + head * 128 + col)` modulo `2 ^ 64`, for the row
`m = (tid / 8) % 16 + 16 * (k / 16)` of the tile (`token = m / 6`, `head = 6 kv_head + m % 6`) and
column `col = 8 (tid % 8) + 64 ((k % 16) / 8) + k % 8`. -/
theorem ldq_addr (L : Launch) (g : Nat) (dt : Dat) {k : Nat} (hk : k < 64) (ht : tidOf L g < 128)
    (hy : cta L g .y ≤ 1)
    (hc : dt.cu0 + (tidOf L g / 8 % 16 + 16 * (k / 16)) / 6 < 2 ^ 31)
    (hs : dt.pro.x16.toNat < 2 ^ 31) :
    loadAddr L g dt (ldqSite k) = (dt.pro.x0.toNat + 2 * (dt.pro.x16.toNat *
      (dt.cu0 + (tidOf L g / 8 % 16 + 16 * (k / 16)) / 6) +
      (cta L g .y * 6 + (tidOf L g / 8 % 16 + 16 * (k / 16)) % 6) * 128 +
      (8 * (tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8))) % 2 ^ 64 := by
  obtain ⟨x, hx, hxn⟩ := ldq_reg L g dt hk
  have hl : loadAddr L g dt (ldqSite k) = x.toNat := by
    unfold loadAddr
    rw [hx]
  rw [hl, hxn, qOff_eq _ (Nat.mod_lt _ (by norm_num)), rd257_val L g dt ht, BitVec.toNat_ofNat]
  have hG : k / 16 = 0 ∨ k / 16 = 1 ∨ k / 16 = 2 ∨ k / 16 = 3 := by omega
  rcases hG with h | h | h | h
  · have hc' : dt.cu0 + tidOf L g / 8 % 16 / 6 < 2 ^ 31 := by rw [h] at hc; simpa using hc
    have e := rd3_val L g dt ht hy hc' hs
    rw [h, qReg0, e, BitVec.toNat_ofNat]
    generalize dt.pro.x16.toNat * (dt.cu0 + tidOf L g / 8 % 16 / 6) = p
    omega
  · have hc' : dt.cu0 + (tidOf L g / 8 % 16 + 16) / 6 < 2 ^ 31 := by rw [h] at hc; simpa using hc
    have e := rd4_val L g dt ht hy hc' hs
    rw [h, qReg1, e, BitVec.toNat_ofNat]
    generalize dt.pro.x16.toNat * (dt.cu0 + (tidOf L g / 8 % 16 + 16) / 6) = p
    omega
  · have hc' : dt.cu0 + (tidOf L g / 8 % 16 + 32) / 6 < 2 ^ 31 := by rw [h] at hc; simpa using hc
    have e := rd5_val L g dt ht hy hc' hs
    rw [h, qReg2, e, BitVec.toNat_ofNat]
    generalize dt.pro.x16.toNat * (dt.cu0 + (tidOf L g / 8 % 16 + 32) / 6) = p
    omega
  · have hc' : dt.cu0 + (tidOf L g / 8 % 16 + 48) / 6 < 2 ^ 31 := by rw [h] at hc; simpa using hc
    have e := rd6_val L g dt ht hy hc' hs
    rw [h, qReg3, e, BitVec.toNat_ofNat]
    generalize dt.pro.x16.toNat * (dt.cu0 + (tidOf L g / 8 % 16 + 48) / 6) = p
    omega

theorem pGt_ofNat (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    pGtS32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b < a) := by
  simp only [pGtS32, PTX.compare, truncBits_ofNat _ _ (by omega : 32 ≤ 64), Option.getD_some,
    tos32]
  have h1 : a % 2 ^ 32 = a := Nat.mod_eq_of_lt (by omega)
  have h2 : b % 2 ^ 32 = b := Nat.mod_eq_of_lt (by omega)
  simp only [h1, h2, ha, hb, ↓reduceIte]
  rw [decide_eq_decide]
  omega

theorem guardVal_ldq (L : Launch) (g : Nat) (dt : Dat) :
    ∀ k < 64, guardVal L g dt (ldqSite k) =
      (if k / 16 = 0 then v_p81 L g dt else if k / 16 = 1 then v_p82 L g dt
        else if k / 16 = 2 then v_p83 L g dt else v_p84 L g dt) := by
  intro k hk
  interval_cases k <;> rfl

/-- **The guard of a query load says its row's token is a token of the request.** -/
theorem ldq_guard_tok (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) (ht : tidOf L g < 128)
    {k : Nat} (hk : k < 64) (hG : guardVal L g dt (ldqSite k) = true) :
    (tidOf L g / 8 % 16 + 16 * (k / 16)) / 6 < dt.cu1 - dt.cu0 := by
  rw [guardVal_ldq L g dt k hk] at hG
  have hq : dt.cu1 - dt.cu0 < 2 ^ 31 := by obtain ⟨-, h2, -⟩ := hb; omega
  have hG4 : k / 16 = 0 ∨ k / 16 = 1 ∨ k / 16 = 2 ∨ k / 16 = 3 := by omega
  rcases hG4 with h | h | h | h
  · simp only [h, ↓reduceIte] at hG
    simp only [v_p81, r20_val L g dt hb, r183_val L g dt ht,
      pGt_ofNat (dt.cu1 - dt.cu0) (tidOf L g / 8 % 16 / 6) hq (by omega),
      decide_eq_true_eq] at hG
    simpa [h] using hG
  · simp only [h, ↓reduceIte, show ¬ (1 = 0) by omega] at hG
    simp only [v_p82, r20_val L g dt hb, r182_val L g dt ht,
      pGt_ofNat (dt.cu1 - dt.cu0) ((tidOf L g / 8 % 16 + 16) / 6) hq (by omega),
      decide_eq_true_eq] at hG
    simpa [h] using hG
  · simp only [h, ↓reduceIte, show ¬ (2 = 0) by omega, show ¬ (2 = 1) by omega] at hG
    simp only [v_p83, r20_val L g dt hb, r181_val L g dt ht,
      pGt_ofNat (dt.cu1 - dt.cu0) ((tidOf L g / 8 % 16 + 32) / 6) hq (by omega),
      decide_eq_true_eq] at hG
    simpa [h] using hG
  · simp only [h, ↓reduceIte, show ¬ (3 = 0) by omega, show ¬ (3 = 1) by omega,
      show ¬ (3 = 2) by omega] at hG
    simp only [v_p84, v_p39, Bool.and_eq_true, r20_val L g dt hb, r180_val L g dt ht,
      pGt_ofNat (dt.cu1 - dt.cu0) ((tidOf L g / 8 % 16 + 48) / 6) hq (by omega),
      decide_eq_true_eq] at hG
    simpa [h] using hG.2

variable {P : Params} {mem0 : Mem0}

/-- **The address of a query load whose guard holds, in `Spec`'s terms**: the byte address of
element `(token, head, col)` of the request's `Q`, for a valid token, a head below 12 and a column
below 128 (`Params.reads`'s first disjunct, `Pre.qInput`). -/
theorem ldq_spec {L : Launch} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads) {dt : Dat}
    (ha : ArgsOk L g dt.pro) (hm : WordsMatch P (cta L g .z) dt) {k : Nat} (hk : k < 64)
    (hG : guardVal L g dt (ldqSite k) = true) :
    loadAddr L g dt (ldqSite k) = P.qBase + 2 * ((P.qStart (cta L g .z) +
        (tidOf L g / 8 % 16 + 16 * (k / 16)) / 6) * P.strideQ +
      (cta L g .y * 6 + (tidOf L g / 8 % 16 + 16 * (k / 16)) % 6) * headDim +
      (8 * (tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8)) ∧
    (tidOf L g / 8 % 16 + 16 * (k / 16)) / 6 < P.qLen (cta L g .z) ∧
    cta L g .y * 6 + (tidOf L g / 8 % 16 + 16 * (k / 16)) % 6 < heads ∧
    8 * (tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8 < headDim := by
  obtain ⟨hx, hy, hz⟩ := cta_lt hpre hg
  have hBnd := bnd_of_pre hpre hz hm
  have ht := ha.tid
  have htok := ldq_guard_tok L g dt hBnd ht hk hG
  have hq : dt.cu1 - dt.cu0 = P.qLen (cta L g .z) := by simp [Params.qLen, hm.cu0, hm.cu1]
  rw [hq] at htok
  have hqs := hpre.qLenLe _ hz
  have hend := hpre.cuEnd
  have hmono := qStart_mono hpre (r := cta L g .z + 1) (r' := P.b) (by omega) (Nat.le_refl _)
  have hnt := hpre.nTokRange
  have hsc := hpre.scalarsRange
  have hy1 : cta L g .y ≤ 1 := by unfold kvHeads at hy; omega
  have hx0 : dt.pro.x0 = BitVec.ofNat 64 P.qBase :=
    Option.some.inj (ha.p0.symm.trans hpre.paramQ)
  have hx16 : dt.pro.x16 = BitVec.ofNat 64 P.strideQ :=
    Option.some.inj (ha.p16.symm.trans hpre.paramStrideQ)
  have e16 : dt.pro.x16.toNat = P.strideQ := by
    rw [hx16, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have e0 : dt.pro.x0.toNat = P.qBase % 2 ^ 64 := by rw [hx0, BitVec.toNat_ofNat]
  have hqs1 : P.qStart (cta L g .z + 1) = P.qStart (cta L g .z) + P.qLen (cta L g .z) := by
    simp only [Params.qLen]
    have := hpre.cuMono _ hz
    omega
  have hcu : dt.cu0 = P.qStart (cta L g .z) := hm.cu0
  set m := tidOf L g / 8 % 16 + 16 * (k / 16) with hmdef
  have hm60 : m / 6 < P.qLen (cta L g .z) := htok
  have hc : dt.cu0 + m / 6 < 2 ^ 31 := by omega
  have haddr := ldq_addr L g dt hk ht hy1 hc (by omega)
  rw [e16, e0, hcu, ← hmdef] at haddr
  set A := P.qBase + 2 * ((P.qStart (cta L g .z) + m / 6) * P.strideQ +
    (cta L g .y * 6 + m % 6) * headDim +
    (8 * (tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8)) with hA
  have hread : P.reads A :=
    Or.inl ⟨cta L g .z, hz, m / 6, hm60, cta L g .y * 6 + m % 6, by unfold heads; omega,
      8 * (tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8, by unfold headDim; omega, 0, by omega,
      by rw [hA, Nat.add_zero]⟩
  have hrr := hpre.readsRange _ hread
  refine ⟨?_, hm60, by unfold heads; omega, by unfold headDim; omega⟩
  rw [haddr]
  simp only [hA, headDim] at hrr ⊢
  have hmul : P.strideQ * (P.qStart (cta L g .z) + m / 6) =
      (P.qStart (cta L g .z) + m / 6) * P.strideQ := Nat.mul_comm _ _
  rw [hmul]
  omega

/-- **A query load whose guard holds reads input bytes**: the two bytes at the address of load `k`
are bytes of `Q` of a valid token (`Params.reads`), for a state whose words are the request's. -/
theorem ldq_reads {L : Launch} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads) {dt : Dat}
    (ha : ArgsOk L g dt.pro) (hm : WordsMatch P (cta L g .z) dt) {k : Nat} (hk : k < 64)
    (hG : guardVal L g dt (ldqSite k) = true) :
    ∀ b < 2, P.reads (loadAddr L g dt (ldqSite k) + b) := by
  intro b hb
  obtain ⟨hA, htok, hhead, hcol⟩ := ldq_spec hpre hg ha hm hk hG
  obtain ⟨hx, hy, hz⟩ := cta_lt hpre hg
  rw [hA]
  refine Or.inl ⟨cta L g .z, hz, _, htok, _, hhead, _, hcol, b, hb, ?_⟩
  ring

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
