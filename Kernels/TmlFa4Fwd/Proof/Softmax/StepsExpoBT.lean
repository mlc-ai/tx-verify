-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoBT
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The bias round's exponents: the tail's single unpack

The tail (pcs 6308 to 6507) runs, per path, two generated runs around pc 6380, `mov.b64
{%r3845, _}`, which unpacks only the low half (`seg6380<P>`). The low half is the path's own
register (`%r3607` on the hardware path, `%r3650` on the software path), which the runs carry, so
its kind is that register's. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exec_unpackLo {L : Launch} {g : Nat} {t : TState} {lo a : Nat} {v : Value}
    (hS : SegFreePc Assumptions.all t.pc) (h : t.regs a = some v) (hu : UnpackOk v) :
    execLocalA Assumptions.all L g t (.move ⟨.unpack, .int .b 64, [some lo, none], [.reg a]⟩) =
      .ok (PTX.next (setReg t lo (splitValue 64 v).1)) := by
  rw [(hS.at rfl).exec, execLocalRule_of_none (Gen.moveNone t _)]
  obtain ⟨h1, h2, h3⟩ := hu
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, h,
    h1, h2, h3, bind, Except.bind, pure, Except.pure, setDst]

/-- The end and start keys of the tail's runs (path A). -/
abbrev tAKeys0 : List Nat := (Gen.expoBTA0_facts3 fun _ => .pred false).map Prod.fst
abbrev tAKeys1 : List Nat := (Gen.expoBTA1_facts0 fun _ => .pred false).map Prod.fst

theorem expoBTA0_facts0_eq (V : Nat → Value) :
    Gen.expoBTA0_facts0 V =
      factsFrom ((Gen.expoBTA0_facts0 fun _ => .pred false).map Prod.fst) V := by
  kernel_rfl

theorem expoBTA0_end_eq (V : Nat → Value) :
    Gen.expoBTA0_facts3 V = factsFrom tAKeys0 (lookupD (Gen.expoBTA0_facts3 V)) := by
  kernel_rfl

theorem expoBTA1_facts0_eq (V : Nat → Value) :
    Gen.expoBTA1_facts0 V = factsFrom tAKeys1 V := by
  kernel_rfl

/-- **The unpack at pc 6380** (path A). -/
theorem seg6380A {L : Launch} {g : Nat} (U : Nat → Value)
    (hu : UnpackOk (lookupD (Gen.expoBTA0_facts3 U) 9556)) :
    ∃ n, Seg kernel Assumptions.all L g n 6380 (Gen.expoBTA0_facts3 U) 6381
      (Gen.expoBTA1_facts0 (nextTA U)) := by
  rw [expoBTA0_end_eq, expoBTA1_facts0_eq]
  have hn : (4905 : Nat) ∉ tAKeys0 := by decide +kernel
  obtain ⟨n, h⟩ := Seg.rule1 (K := kernel) (A := Assumptions.all) (L := L) (g := g)
    (pc := 6380) (d := 4905) (F := factsFrom tAKeys0 (lookupD (Gen.expoBTA0_facts3 U)))
    (v := (splitValue 64 (lookupD (Gen.expoBTA0_facts3 U) 9556)).1) Flow.code_6380 rfl
    (fun R cf hR => exec_unpackLo (Gen.segFree 6380 rfl)
      (holds_mem hR (mem_factsFrom (by decide +kernel))) hu)
    (not_mem_factsFrom hn)
  refine ⟨n, h.weaken_end fun R hR => holds_of_pointwise fun r hr => ?_⟩
  have hk : tAKeys1.all (fun r => r == 4905 || tAKeys0.contains r) = true := by
    decide +kernel
  have := List.all_eq_true.mp hk r hr
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
  rcases this with rfl | hm
  · simp only [nextTA]
    rw [Function.update_self]; exact hR.1
  · have hne : r ≠ 4905 := by rintro rfl; exact hn hm
    simp only [nextTA]
    rw [Function.update_of_ne hne]
    exact holds_mem hR.2 (mem_factsFrom hm)

/-- The end and start keys of the tail's runs (path B). -/
abbrev tBKeys0 : List Nat := (Gen.expoBTB0_facts3 fun _ => .pred false).map Prod.fst
abbrev tBKeys1 : List Nat := (Gen.expoBTB1_facts0 fun _ => .pred false).map Prod.fst

theorem expoBTB0_facts0_eq (V : Nat → Value) :
    Gen.expoBTB0_facts0 V =
      factsFrom ((Gen.expoBTB0_facts0 fun _ => .pred false).map Prod.fst) V := by
  kernel_rfl

theorem expoBTB0_end_eq (V : Nat → Value) :
    Gen.expoBTB0_facts3 V = factsFrom tBKeys0 (lookupD (Gen.expoBTB0_facts3 V)) := by
  kernel_rfl

theorem expoBTB1_facts0_eq (V : Nat → Value) :
    Gen.expoBTB1_facts0 V = factsFrom tBKeys1 V := by
  kernel_rfl

/-- **The unpack at pc 6380** (path B). -/
theorem seg6380B {L : Launch} {g : Nat} (U : Nat → Value)
    (hu : UnpackOk (lookupD (Gen.expoBTB0_facts3 U) 9556)) :
    ∃ n, Seg kernel Assumptions.all L g n 6380 (Gen.expoBTB0_facts3 U) 6381
      (Gen.expoBTB1_facts0 (nextTB U)) := by
  rw [expoBTB0_end_eq, expoBTB1_facts0_eq]
  have hn : (4905 : Nat) ∉ tBKeys0 := by decide +kernel
  obtain ⟨n, h⟩ := Seg.rule1 (K := kernel) (A := Assumptions.all) (L := L) (g := g)
    (pc := 6380) (d := 4905) (F := factsFrom tBKeys0 (lookupD (Gen.expoBTB0_facts3 U)))
    (v := (splitValue 64 (lookupD (Gen.expoBTB0_facts3 U) 9556)).1) Flow.code_6380 rfl
    (fun R cf hR => exec_unpackLo (Gen.segFree 6380 rfl)
      (holds_mem hR (mem_factsFrom (by decide +kernel))) hu)
    (not_mem_factsFrom hn)
  refine ⟨n, h.weaken_end fun R hR => holds_of_pointwise fun r hr => ?_⟩
  have hk : tBKeys1.all (fun r => r == 4905 || tBKeys0.contains r) = true := by
    decide +kernel
  have := List.all_eq_true.mp hk r hr
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
  rcases this with rfl | hm
  · simp only [nextTB]
    rw [Function.update_self]; exact hR.1
  · have hne : r ≠ 4905 := by rintro rfl; exact hn hm
    simp only [nextTB]
    rw [Function.update_of_ne hne]
    exact holds_mem hR.2 (mem_factsFrom hm)

/-- A pair kind. -/
def isPr : Kd → Bool
  | .pr _ => true
  | _ => false

theorem unpack_of_isPr {k : Kd} {v : Value} (h : k.Has v) (hk : isPr k = true) : UnpackOk v := by
  cases k with
  | pr _ => exact h.1
  | _ => simp [isPr] at hk

/-- A scalar kind. -/
def isS : Kd → Bool
  | .s _ => true
  | _ => false

theorem clean_of_isS {k : Kd} {v : Value} (h : k.Has v) (hk : isS k = true) : Clean v := by
  cases k with
  | s s => exact SK.clean h
  | _ => simp [isS] at hk

/-- The low half of a pair whose low value is clean, whatever the high value. -/
theorem split_join_lo {a b : Value} (ha : Clean a) : (splitValue 64 (joinValue a b)).1 = a := by
  obtain ⟨ha4, has, hab⟩ := ha
  cases a with
  | slice w o n => exact absurd rfl (has w o n)
  | bits w x =>
    have hx := hab w x rfl
    simp only [Value.bytes] at ha4
    cases b with
    | bits w' y =>
      unfold joinValue
      by_cases hw : w = w' ∧ 2 * w ≤ 64
      · obtain ⟨rfl, hw2⟩ := hw
        have h32 : w = 32 := by omega
        subst h32
        simp only [and_self, Nat.reduceMul, Nat.reduceLeDiff, ↓reduceIte, splitValue,
          Nat.reduceDiv, Value.bits.injEq, true_and]
        apply BitVec.eq_of_toNat_eq
        rw [truncBits32_toNat, toNat_or_shl32_lo, Nat.mod_eq_of_lt hx]
      · simp only [hw, ↓reduceIte, splitValue]
    | _ => rfl
  | _ =>
    cases b with
    | slice w o n => simp only [joinValue]; all_goals rfl
    | _ => rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
