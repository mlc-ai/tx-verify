-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumMask
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StrictLib

@[expose] public section

/-! # Conditions of the valid-mask chain

Each column of the mask chain (`and`, `setp`, `selp`, or `setp`, `selp` for the sign bits) is no
fault on the 32-bit mask word `n` and a word of four bytes: the equations `w0m_colA` to
`w0m_colD` prove, with the same steps, that every outcome is `.ok`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

theorem c_colA {d1 d2 d3 a1 a2 a p n : Nat} {src v : Value} (hn : n < 2 ^ 32) {k : Nat}
    (hs : src = .bits 32 (BitVec.ofNat 64 (n / 2 ^ k))) (hap : a ≠ p) (hv : v.bytes = 4) :
    (∃ x, coreF (.int ⟨.and, .int .b 32, false, [some d1], [.reg a1, .imm 1]⟩) [a1] [src] =
        .ok x) ∧
      (∃ x, coreF (.int ⟨.setp .ne none, .int .b 32, false, [some d2], [.reg a2, .imm 0]⟩) [a2]
        [okVal (.bits 32 0) (coreF (.int ⟨.and, .int .b 32, false, [some d1],
          [.reg a1, .imm 1]⟩) [a1] [src])] = .ok x) ∧
      (∃ x, coreF (.int ⟨.selp, .int .b 32, false, [some d3], [.reg a, .imm (-8388608), .reg p]⟩)
        [a, p] [v, okVal (.bits 32 0) (coreF (.int ⟨.setp .ne none, .int .b 32, false, [some d2],
          [.reg a2, .imm 0]⟩) [a2] [okVal (.bits 32 0) (coreF (.int ⟨.and, .int .b 32, false,
          [some d1], [.reg a1, .imm 1]⟩) [a1] [src])])] = .ok x) := by
  have hy : n / 2 ^ k < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  subst hs
  have e1 := w0m_and_imm (dd := d1) (a := a1) (k := 1) (kn := 1) rfl (by simp) hy (by norm_num)
  refine ⟨⟨_, e1⟩, ?_⟩
  rw [e1]
  simp only [w0m_okVal]
  have e2 := w0m_setp_ne0 (dd := d2) (a := a2) (y := n / 2 ^ k &&& 1)
    (lt_of_le_of_lt Nat.and_le_right (by norm_num))
  refine ⟨⟨_, e2⟩, ?_⟩
  rw [e2]
  simp only [w0m_okVal]
  exact ⟨_, w0m_selp_hi hap v hv _⟩

theorem c_colB {d1 d2 d3 a1 a2 a p n : Nat} {src v : Value} {k b : Nat}
    {km : Int} (hkm : km = ((2 ^ b : Nat) : Int)) (hb : b < 16)
    (hs : src = .bits 16 (BitVec.ofNat 64 (n / 2 ^ k % 65536))) (hap : a ≠ p)
    (hv : v.bytes = 4) :
    (∃ x, coreF (.int ⟨.and, .int .b 16, false, [some d1], [.reg a1, .imm km]⟩) [a1] [src] =
        .ok x) ∧
      (∃ x, coreF (.int ⟨.setp .eq none, .int .b 16, false, [some d2], [.reg a2, .imm 0]⟩) [a2]
        [okVal (.bits 32 0) (coreF (.int ⟨.and, .int .b 16, false, [some d1],
          [.reg a1, .imm km]⟩) [a1] [src])] = .ok x) ∧
      (∃ x, coreF (.int ⟨.selp, .int .b 32, false, [some d3], [.imm (-8388608), .reg a, .reg p]⟩)
        [a, p] [v, okVal (.bits 32 0) (coreF (.int ⟨.setp .eq none, .int .b 16, false, [some d2],
          [.reg a2, .imm 0]⟩) [a2] [okVal (.bits 32 0) (coreF (.int ⟨.and, .int .b 16, false,
          [some d1], [.reg a1, .imm km]⟩) [a1] [src])])] = .ok x) := by
  have hy : n / 2 ^ k % 65536 < 2 ^ 16 := by omega
  subst hs
  have e1 := w0m_and_imm (dd := d1) (a := a1) hkm (by simp) hy
    (Nat.pow_lt_pow_right (by norm_num) hb)
  refine ⟨⟨_, e1⟩, ?_⟩
  rw [e1]
  simp only [w0m_okVal]
  have e2 := w0m_setp_eq0 (dd := d2) (a := a2) (y := n / 2 ^ k % 65536 &&& 2 ^ b)
    (by simp) (lt_of_le_of_lt Nat.and_le_left hy)
  refine ⟨⟨_, e2⟩, ?_⟩
  rw [e2]
  simp only [w0m_okVal]
  exact ⟨_, w0m_selp_lo hap v hv _⟩

theorem c_colC {d2 d3 a2 a p n : Nat} {src v : Value} {k : Nat}
    (hs : src = .bits 16 (BitVec.ofNat 64 (w0mSx (n / 2 ^ k % 256)))) (hap : a ≠ p)
    (hv : v.bytes = 4) :
    (∃ x, coreF (.int ⟨.setp .gt none, .int .s 16, false, [some d2], [.reg a2, .imm (-1)]⟩) [a2]
        [src] = .ok x) ∧
      (∃ x, coreF (.int ⟨.selp, .int .b 32, false, [some d3], [.imm (-8388608), .reg a, .reg p]⟩)
        [a, p] [v, okVal (.bits 32 0) (coreF (.int ⟨.setp .gt none, .int .s 16, false, [some d2],
          [.reg a2, .imm (-1)]⟩) [a2] [src])] = .ok x) := by
  subst hs
  have e2 := w0m_setp_gt16 (dd := d2) (a := a2) (y := w0mSx (n / 2 ^ k % 256))
    (by unfold w0mSx; split_ifs <;> omega)
  refine ⟨⟨_, e2⟩, ?_⟩
  rw [e2]
  simp only [w0m_okVal]
  exact ⟨_, w0m_selp_lo hap v hv _⟩

theorem c_colD {d2 d3 a2 a p n : Nat} {src v : Value} (hn : n < 2 ^ 32)
    (hs : src = .bits 32 (BitVec.ofNat 64 n)) (hap : a ≠ p) (hv : v.bytes = 4) :
    (∃ x, coreF (.int ⟨.setp .gt none, .int .s 32, false, [some d2], [.reg a2, .imm (-1)]⟩) [a2]
        [src] = .ok x) ∧
      (∃ x, coreF (.int ⟨.selp, .int .b 32, false, [some d3], [.imm (-8388608), .reg a, .reg p]⟩)
        [a, p] [v, okVal (.bits 32 0) (coreF (.int ⟨.setp .gt none, .int .s 32, false, [some d2],
          [.reg a2, .imm (-1)]⟩) [a2] [src])] = .ok x) := by
  subst hs
  have e2 := w0m_setp_gt32 (dd := d2) (a := a2) hn
  refine ⟨⟨_, e2⟩, ?_⟩
  rw [e2]
  simp only [w0m_okVal]
  exact ⟨_, w0m_selp_lo hap v hv _⟩

theorem c_shr {dd a y kn : Nat} {k : Int} {x : Value} (hkn : k = (kn : Int)) (hy : y < 2 ^ 32)
    (hk : kn < 32) (hx : x = .bits 32 (BitVec.ofNat 64 y)) :
    ∃ v, coreF (.int ⟨.shr, .int .u 32, false, [some dd], [.reg a, .imm k]⟩) [a] [x] = .ok v := by
  subst hx
  exact ⟨_, w0m_shr hkn hy hk⟩

theorem c_bfe {a y p : Nat} {x : Value} (hy : y < 2 ^ 32) (hp : p + 8 ≤ 32)
    (hx : x = .bits 32 (BitVec.ofNat 64 y)) :
    ∃ v, bfeW .s 32 (.reg a) (.imm (p : Int)) (.imm 8) (lk [a] [x]) = .ok v := by
  subst hx
  exact ⟨_, w0m_bfe hy hp⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
