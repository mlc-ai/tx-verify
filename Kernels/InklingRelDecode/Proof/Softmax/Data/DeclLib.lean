-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Decline

@[expose] public section

/-! # The scalar arithmetic on registers of a kind is not declined

A scalar `sub` or `mul` whose registers hold values of the kinds below reads both operands as
extended reals whose difference or product is defined (`Decline.lean`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

/-- A register that holds a value of a kind up to `ni` reads as an extended real of that kind. -/
theorem rd_sk {t : TState} {r : Nat} {v : Value} {k : SK} (hk : k.le .ni = true)
    (h : t.regs r = some v) (hv : k.Has v) :
    ∃ x, readERealOpnd t .f32 (.reg r) = some (.ok x) ∧ k.Lane x := by
  obtain ⟨x, hx, lx⟩ := SK.lane_of hk hv
  exact ⟨x, by rw [readERealOpnd_reg h, hx], lx⟩

/-- **A difference of a number or `-inf` and a number is not declined.** -/
theorem decl_sub {L : Launch} {g : Nat} {t : TState} {fz : Bool} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hva : SK.ni.Has va)
    (hvb : SK.fl.Has vb) :
    execIdealFloat L g t (.float { subI fz with dsts := [some d], srcs := [.reg a, .reg b] })
      ≠ none := by
  obtain ⟨x, hx, lx⟩ := rd_sk (k := .ni) rfl ha hva
  obtain ⟨y, hy, ly⟩ := rd_sk (k := .fl) rfl hb hvb
  obtain ⟨s, rfl⟩ := ly
  refine ideal_sub1 (by simp [arith2]) hx hy ?_
  rcases lx with ⟨r, rfl⟩ | rfl
  · rw [← EReal.coe_neg]
    simp [addEReal]
  · rw [← EReal.coe_neg]
    simp [addEReal]

/-- **A product of a positive number and a number or `-inf` is not declined.** -/
theorem decl_mul_pw {L : Launch} {g : Nat} {t : TState} {fz : Bool} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hva : SK.pw.Has va)
    (hvb : SK.ni.Has vb) :
    execIdealFloat L g t (.float { mulI fz with dsts := [some d], srcs := [.reg a, .reg b] })
      ≠ none := by
  obtain ⟨x, hx, ⟨r, hr, rfl⟩⟩ := rd_sk (k := .pw) rfl ha hva
  obtain ⟨y, hy, ly⟩ := rd_sk (k := .ni) rfl hb hvb
  refine ideal_mul1 (by simp [arith2]) hx hy ?_
  rcases ly with ⟨s, rfl⟩ | rfl
  · exact mulEReal_real r s
  · simp [mulEReal, hr.ne', EReal.coe_ne_top, EReal.coe_ne_bot, EReal.coe_eq_zero]

/-- **A product of two numbers is not declined.** -/
theorem decl_mul_fl {L : Launch} {g : Nat} {t : TState} {fz : Bool} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hva : SK.fl.Has va)
    (hvb : SK.fl.Has vb) :
    execIdealFloat L g t (.float { mulI fz with dsts := [some d], srcs := [.reg a, .reg b] })
      ≠ none := by
  obtain ⟨x, hx, ⟨r, rfl⟩⟩ := rd_sk (k := .fl) rfl ha hva
  obtain ⟨y, hy, ⟨s, rfl⟩⟩ := rd_sk (k := .fl) rfl hb hvb
  exact ideal_mul1 (by simp [arith2]) hx hy (mulEReal_real r s)

/-- The values after a run of two lists are the values after the second on those after the first. -/
theorem xFinal_append : ∀ (a b : List XItem) (V : Nat → Value),
    xFinal V (a ++ b) = xFinal (xFinal V a) b
  | [], _, _ => rfl
  | _ :: a, b, _ => xFinal_append a b _

/-- The requirement of a run of two lists. -/
theorem xReq_append : ∀ (a b : List XItem) (V : Nat → Value),
    xReq V (a ++ b) = (xReq V a && xReq (xFinal V a) b)
  | [], _, _ => by simp [xReq, xFinal]
  | _ :: a, b, _ => by
    simp only [List.cons_append, xReq, xFinal, Bool.and_assoc]
    rw [xReq_append a b]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
