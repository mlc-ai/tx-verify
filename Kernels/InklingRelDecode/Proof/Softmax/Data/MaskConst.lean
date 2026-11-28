-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskFin
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Canon
import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants

@[expose] public section

/-! # The constants the mask reads, from the entry

At the wait of the score load the registers the mask runs read are the column offset
(`t / 16 % 2 * 64` for thread `t`, register 1956 and its 32-bit copy 1901), the block's first key
(register 1912, `128 * (split + i * splits)`) and the 32 pairs of constants (registers 1961 to
1992) the setup code derives from the words past the first token (`P0`, register 482) and the
thread's token (register 496): `P = P0 + token`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem en496 {V : Nat → Value} {t : Nat} (ht : t < 256) (h : V 462 = b32 t) :
    Gen.en_v583 V = b32 (token t) := by
  have : ∀ t < 256, Gen.en_v583 (fun r => if r = 462 then b32 t else b32 0) = b32 (token t) := by
    decide +kernel
  rw [← this t ht]
  simp only [Gen.en_v583, Gen.en_v582, Gen.en_v581, Gen.en_v580, Gen.en_v579, Gen.en_v578,
    Gen.en_v577, Gen.en_v576, h, ↓reduceIte]

theorem en798 {V : Nat → Value} {t : Nat} (ht : t < 256) (h : V 462 = b32 t) :
    Gen.en_v588 V = b32 (t / 16 % 2 * 64) := by
  have : ∀ t < 256, Gen.en_v588 (fun r => if r = 462 then b32 t else b32 0) =
      b32 (t / 16 % 2 * 64) := by decide +kernel
  rw [← this t ht]
  simp only [Gen.en_v588, Gen.en_v587, h, ↓reduceIte]

theorem add_imm_w {d a : Nat} (k x : ℤ) (v : Value) :
    okVal v (coreF (.int ⟨.add, .int .s 32, false, [some d], [.reg a, .imm k]⟩) [a] [w32 x]) =
      w32 (x + k) := by
  have h : lk [a] [w32 x] a = w32 x := by simp [lk]
  have e : coreF (.int ⟨.add, .int .s 32, false, [some d], [.reg a, .imm k]⟩) [a] [w32 x] =
      .ok (w32 (x + k)) := by
    simp only [coreF, coreW, addW, oVal, oBits, h, pure, Except.pure, bind, Except.bind,
      DType.width]
    simp only [w32, trunc_idem, trunc_add]
  rw [okVal_ok e]

/-- The pair of two words of integers. -/
def JW (v : Value) (x y : ℤ) : Prop := v = joinValue (w32 x) (w32 y)

theorem jw_join {a b : Value} {x y : ℤ} (ha : IW a x) (hb : IW b y) : JW (joinValue a b) x y := by
  rw [ha, hb]; rfl

theorem add_imm_iw {d a : Nat} {x : Value} {p : ℤ} (k : ℤ) (hx : IW x p) (v : Value) :
    IW (okVal v (coreF (.int ⟨.add, .int .s 32, false, [some d], [.reg a, .imm k]⟩) [a] [x]))
      (p + k) := by
  rw [hx]; exact add_imm_w k p v

theorem io_cst {V : Nat → Value} {cO P : ℤ} (h810 : IW (V 810) P) (h811 : IW (V 811) (cO - P)) :
    ∀ p ∈ Gen.io_facts3 V, 1961 ≤ p.1 → p.1 < 1993 →
      JW p.2 (P - 2 * ((p.1 : ℤ) - 1961))
        (if p.1 = 1961 then cO - P else P - 2 * ((p.1 : ℤ) - 1961) - 1) := by
  intro p hp
  simp only [Gen.io_facts3, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals first
    | (intro h1 h2; dsimp only at h1 h2; exfalso; omega)
    | (intro _ _
       dsimp only
       apply jw_join
       all_goals first
         | (refine iw_of h810 ?_; omega)
         | (refine iw_of h811 ?_; split_ifs <;> omega)
         | (refine iw_of (add_imm_iw _ h810 _) ?_; omega))


theorem g4_496 (ht : g % L.block < 256) : lookupD (G4 e L g) 496 = b32 (token (g % L.block)) := by
  have : lookupD (G4 e L g) 496 = Gen.en_v583 (lookupD (G0 e L g)) := by
    simp [G4, G3, G2, G1, lookupD, Gen.ng_facts1, Gen.e8_facts1, Gen.dv_facts1, Gen.en_facts1,
      List.lookup]
  rw [this]
  exact en496 ht (by simp [G0, lookupD])

theorem g4_798 (ht : g % L.block < 256) :
    lookupD (G4 e L g) 798 = b32 (g % L.block / 16 % 2 * 64) := by
  have : lookupD (G4 e L g) 798 = Gen.en_v588 (lookupD (G0 e L g)) := by
    simp [G4, G3, G2, G1, lookupD, Gen.ng_facts1, Gen.e8_facts1, Gen.dv_facts1, Gen.en_facts1,
      List.lookup]
  rw [this]
  exact en798 ht (by simp [G0, lookupD])

theorem g4_482 : lookupD (G4 e L g) 482 = e.prior := by
  simp [G4, G3, G2, G1, G0, lookupD, Gen.ng_facts1, Gen.e8_facts1, Gen.dv_facts1, Gen.en_facts1,
    List.lookup]


theorem b32_iw {n : Nat} (h : n < 2 ^ 32) : IW (b32 n) n := by
  unfold IW w32 b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_w]
  simp only [BitVec.toNat_ofNat]
  have h1 : ((n : ℤ) % 2 ^ 32).toNat = n := by omega
  rw [h1]
  omega

theorem g5_810 {P0 : ℤ} (hp : e.prior = w32 P0) (ht : g % L.block < 256) :
    IW (lookupD (G5 e L g) 810) (P0 + (token (g % L.block) : Nat)) := by
  have : lookupD (G5 e L g) 810 = Gen.ie_v814 (lookupD (G4 e L g)) := by
    simp [G5, lookupD, Gen.ie_facts1]
  rw [this]
  apply add_iw (by decide)
  · rw [g4_482]; exact hp
  · rw [g4_496 ht]; exact b32_iw (by unfold token row; omega)

theorem g5_811 {P0 : ℤ} (hp : e.prior = w32 P0) (ht : g % L.block < 256) :
    IW (lookupD (G5 e L g) 811)
      ((g % L.block / 16 % 2 * 64 : Nat) - (P0 + (token (g % L.block) : Nat))) := by
  have : lookupD (G5 e L g) 811 = Gen.ie_v815 (lookupD (G4 e L g)) := by
    simp [G5, lookupD, Gen.ie_facts1, List.lookup]
  rw [this]
  apply sub_iw (by decide)
  · rw [g4_798 ht]; exact b32_iw (by omega)
  · apply add_iw (by decide)
    · rw [g4_482]; exact hp
    · rw [g4_496 ht]; exact b32_iw (by unfold token row; omega)

theorem derV_cst {P0 : ℤ} (hp : e.prior = w32 P0) (ht : g % L.block < 256) {r : Nat}
    (h1 : 1961 ≤ r) (h2 : r < 1993) :
    JW (derV e L g r) (P0 + (token (g % L.block) : Nat) - 2 * ((r : ℤ) - 1961))
      (if r = 1961 then ((g % L.block / 16 % 2 * 64 : Nat) : ℤ) - (P0 + (token (g % L.block) : Nat))
        else P0 + (token (g % L.block) : Nat) - 2 * ((r : ℤ) - 1961) - 1) := by
  have hk : r ∈ (Gen.io_facts3 (lookupD (G5 e L g))).map Prod.fst := by
    simp only [Gen.io_facts3, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    omega
  obtain ⟨v, hv⟩ := lookup_some hk
  have e6 : derV e L g r = v := by
    simp [derV, G6, lookupD, lookup_app_left hv]
  have := io_cst (g5_810 hp ht) (g5_811 hp ht) (r, v) (mem_of_lookupK hv) h1 h2
  rw [e6]
  exact this


theorem w1V_1912 {d : D} (hs : d.c.site = .waitLd) :
    w1V e L g d 1912 = u32 ((e.split + d.c.i * e.splits) * 128) := by
  rw [w1V_eq hs (by decide +kernel)]
  unfold lookupD baseF
  simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
  have h : 1912 ∈ ctlLive Site.waitLd.pc := by decide +kernel
  simp [h]
  simp [valueOf, scalarValue]

theorem w1V_1956 {d : D} (hs : d.c.site = .waitLd) :
    w1V e L g d 1956 = b64 (g % L.block / 16 % 2 * 64) := by
  rw [w1V_eq hs (by decide +kernel)]
  unfold lookupD baseF
  simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
  have h : 1956 ∈ ctlLive Site.waitLd.pc := by decide +kernel
  simp [h]
  simp [valueOf, scalarValue]

theorem w1V_cst {d : D} (hs : d.c.site = .waitLd) {r : Nat} (h1 : 1961 ≤ r) (h2 : r < 1993) :
    w1V e L g d r = derV e L g r := by
  rw [w1V_eq hs (by simp only [kW1, List.mem_append, List.mem_range'_1]; omega)]
  unfold lookupD baseF
  simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
  have h : r ∉ ctlLive Site.waitLd.pc := by
    have : ∀ r, 1961 ≤ r → r < 1993 → r ∉ ctlLive Site.waitLd.pc := by decide +kernel
    exact this r h1 h2
  have h' : r ∈ keysC := by
    simp only [keysC, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨r - 1960, by omega, by omega⟩
  simp [dF, dFS, startF, pF, wF, wFS, hs, inRound, derF, lookup_factsFrom, h, h']
  simp only [List.lookup, beq_false_of_ne (show r ≠ 498 by omega),
    beq_false_of_ne (show r ≠ 1914 by omega), beq_false_of_ne (show r ≠ 482 by omega),
    beq_false_of_ne (show r ≠ 484 by omega), beq_false_of_ne (show r ≠ 483 by omega),
    beq_false_of_ne (show r ≠ 199 by omega), Option.getD_none]
theorem cvt_1901 (x : Nat) (v : Value) :
    IW (okVal v (coreF Gen.w1a_op1465 [1956] [b64 x])) x := by
  have e : coreF Gen.w1a_op1465 [1956] [b64 x] =
      .ok (.bits 32 (truncBits 32 (BitVec.ofNat 64 x))) := by
    simp [coreF, coreW, cvtW, oVal, oBits, Gen.w1a_op1465, lk, b64, pure, Except.pure, bind,
      Except.bind]
    have h64 : truncBits 64 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
      apply BitVec.eq_of_toNat_eq
      simp [truncBits, BitVec.toNat_ofNat]
    rw [h64]
  rw [okVal_ok e]
  unfold IW w32
  congr 1

/-- **The mask's inputs at the wait of the score load.** -/
theorem maskIn_w1 {d : D} (hs : d.c.site = .waitLd) {P0 : ℤ} (hp : e.prior = w32 P0)
    (ht : g % L.block < 256) (hb : (e.split + d.c.i * e.splits) * 128 < 2 ^ 32) :
    MaskIn (vA (w1V e L g d)) ((g % L.block / 16 % 2 * 64 : Nat) : ℤ)
      (((e.split + d.c.i * e.splits) * 128 : Nat) : ℤ)
      (P0 + (token (g % L.block) : Nat)) := by
  have p1956 : vP (w1V e L g d) 1956 = b64 (g % L.block / 16 % 2 * 64) := by
    rw [vP, V'_notin runP runP_ok _ (by decide +kernel), w1V_1956 hs]
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · refine V'_out runA runA_ok
      (P := fun r v => r = 1901 → IW v ((g % L.block / 16 % 2 * 64 : Nat) : ℤ))
      (fun q hq => ?_) (show 1901 ∈ runA.outs by decide +kernel) rfl
    change q ∈ Gen.w1a_facts6 (vP (w1V e L g d)) at hq
    simp only [Gen.w1a_facts6, List.mem_cons, List.not_mem_nil, or_false] at hq
    repeat' (rcases hq with rfl | hq)
    all_goals first
      | (intro h; dsimp only at h; omega)
      | (intro _
         show IW (okVal (.bits 32 0) (coreF Gen.w1a_op1465 [1956] [vP (w1V e L g d) 1956])) _
         rw [p1956]
         exact cvt_1901 _ _)
  · rw [vA, V'_notin runA runA_ok _ (by decide +kernel), vP,
      V'_notin runP runP_ok _ (by decide +kernel), w1V_1912 hs]
    unfold u32
    rw [Nat.mod_eq_of_lt hb]
    exact b32_iw hb
  · have h1 : 1961 + u < 1993 := by omega
    rw [vA, V'_notin runA runA_ok _ (by
      have : ∀ r, 1961 ≤ r → r < 1993 → r ∉ runA.outs := by decide +kernel
      exact this _ (by omega) h1), vP, V'_notin runP runP_ok _ (by
      have : ∀ r, 1961 ≤ r → r < 1993 → r ∉ runP.outs := by decide +kernel
      exact this _ (by omega) h1), w1V_cst hs (by omega) h1]
    have := derV_cst (e := e) (L := L) (g := g) hp ht (r := 1961 + u) (by omega) h1
    unfold JW at this
    rw [this]
    congr 2 <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
