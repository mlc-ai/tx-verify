-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumChain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumP
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Trace

@[expose] public section

/-! # The words of a valid block as extended reals

`W0Ok` (the words a block read are valid rows) turned into the hypotheses of the numeric stages:
the masked word of column `c` reads as `w0A w c` (the high word's number, or `-inf`), the
peer pairs read as `w0PeerF`, the peer maximum as `w0FE`, and `w0A + peer = w0Score`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof

noncomputable section

set_option linter.unusedSimpArgs false

theorem w0F_of_valFloat {v : Value} {r : ℝ} (h : valFloat .f32 v = .ok r) : w0F v = r := by
  simp [w0F, h, Except.toOption]

/-- The masked high word of column `c` as an extended real. -/
def w0A (w : W0Words) (c : Nat) : EReal :=
  if w0Bit w.mw c then ((w0F (w.hi.getD c (.pred false)) : ℝ) : EReal) else ⊥

theorem w0A_lane (w : W0Words) (c : Nat) : SK.ni.Lane (w0A w c) := by
  unfold w0A
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr rfl

theorem w0A_add (w : W0Words) (c : Nat) :
    w0A w c + ((w0PeerF w c : ℝ) : EReal) = w0Score w c := by
  unfold w0A w0Score
  split
  · rw [← EReal.coe_add]
  · rw [EReal.bot_add]

theorem w0Score_lane (w : W0Words) (c : Nat) : SK.ni.Lane (w0Score w c) := by
  rw [← w0A_add]; exact w0s_lane (w0A_lane w c)

theorem w0Bit_eq {w : W0Words} {n : Nat} (hn : n < 2 ^ 32)
    (h : w.mw = .bits 32 (BitVec.ofNat 64 n)) (c : Nat) : w0Bit w.mw c = n.testBit c := by
  rw [h]
  simp only [w0Bit, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

theorem w0_rd_mask {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {n : Nat} (hn : n < 2 ^ 32)
    (h : w.mw = .bits 32 (BitVec.ofNat 64 n)) {c : Nat} (hc : c < 32) :
    Rd (if n.testBit c = true then w.hi.getD c (.pred false) else w0NegInf) (w0A w c) := by
  unfold w0A
  rw [w0Bit_eq hn h c]
  split
  · obtain ⟨hcl, r, hr⟩ := hw.hi c hc
    rw [w0F_of_valFloat hr]
    exact rd_of_valFloat hcl hr
  · exact rd_negInf

theorem w0_rd_pm {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) : Rd w.pm (w0FE w.pm) := by
  obtain ⟨hc, hf⟩ := hw.pm
  unfold w0FE
  split
  · rename_i h; rw [h]; exact rd_negInf
  · rcases hf with ⟨r, hr⟩ | h
    · rw [w0F_of_valFloat hr]; exact rd_of_valFloat hc hr
    · exact absurd h (by assumption)

theorem w0_pair_is {v : Value} (h1 : W0Fin (splitValue 64 v).1) (h2 : W0Fin (splitValue 64 v).2) :
    W0PairIs v (w0F (splitValue 64 v).1) (w0F (splitValue 64 v).2) := by
  obtain ⟨r, hr⟩ := h1
  obtain ⟨s, hs⟩ := h2
  rw [w0F_of_valFloat hr, w0F_of_valFloat hs]
  exact pairRead_of_reads (readEReal_of_valFloat hr) (readEReal_of_valFloat hs)

theorem w0PeerF_a {w : W0Words} (k : Nat) :
    w0PeerF w (4 * k) = w0F (splitValue 64 (w.pw k).1).1 := by
  simp only [w0PeerF]
  rw [show 4 * k / 4 = k by omega, show 4 * k / 2 % 2 = 0 by omega, show 4 * k % 2 = 0 by omega]
  simp

theorem w0PeerF_b {w : W0Words} (k : Nat) :
    w0PeerF w (4 * k + 1) = w0F (splitValue 64 (w.pw k).1).2 := by
  simp only [w0PeerF]
  rw [show (4 * k + 1) / 4 = k by omega, show (4 * k + 1) / 2 % 2 = 0 by omega,
    show (4 * k + 1) % 2 = 1 by omega]
  simp

theorem w0PeerF_c {w : W0Words} (k : Nat) :
    w0PeerF w (4 * k + 2) = w0F (splitValue 64 (w.pw k).2).1 := by
  simp only [w0PeerF]
  rw [show (4 * k + 2) / 4 = k by omega, show (4 * k + 2) / 2 % 2 = 1 by omega,
    show (4 * k + 2) % 2 = 0 by omega]
  simp

theorem w0PeerF_d {w : W0Words} (k : Nat) :
    w0PeerF w (4 * k + 3) = w0F (splitValue 64 (w.pw k).2).2 := by
  simp only [w0PeerF]
  rw [show (4 * k + 3) / 4 = k by omega, show (4 * k + 3) / 2 % 2 = 1 by omega,
    show (4 * k + 3) % 2 = 1 by omega]
  simp

open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen in
theorem w0c_car_467 (x : BitVec 64) (m l mx sk : Value) :
    lookupD (f_car x m l mx sk) 467 = .bits 32 x := by
  simp [f_car, lookupD, List.lookup]

open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen in
theorem w0c_car_3243 (x : BitVec 64) (m l mx sk : Value) :
    lookupD (f_car x m l mx sk) 3243 = scPair x := by
  simp [f_car, lookupD, List.lookup]

open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen in
theorem w0c_car_2950 (x : BitVec 64) (m l mx sk : Value) :
    lookupD (f_car x m l mx sk) 2950 = m := by
  simp [f_car, lookupD, List.lookup]

open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen in
theorem w0c_car_2955 (x : BitVec 64) (m l mx sk : Value) :
    lookupD (f_car x m l mx sk) 2955 = l := by
  simp [f_car, lookupD, List.lookup]

open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen in
theorem w0c_car_2885 (x : BitVec 64) (m l mx sk : Value) :
    lookupD (f_car x m l mx sk) 2885 = mx := by
  simp [f_car, lookupD, List.lookup]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
