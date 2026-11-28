-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpWindow

@[expose] public section

/-! # The probability pack gives pairs of `bf16` numbers

At the update of the next round (pc 949) the exponentials of the last round are in the registers
1994 to 2017 (pairs of numbers) and 508 to 523 (numbers). The pack of pcs 951 to 1007 turns them
into the 32 words the store of pc 1009 writes (registers 1677 to 1708), each a pair of `bf16`
numbers. The update of the running maximum and sum (pcs 949 and 950) is not part of the run. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- **What the pack reads**: the exponentials, the pairs and the singles. -/
structure PkIn (V : Nat → Value) : Prop where
  pr : ∀ r, 1994 ≤ r → r < 2018 → (Kd.pr .fl).Has (V r)
  sg : ∀ r, 508 ≤ r → r < 524 → (Kd.s .fl).Has (V r)

/-- **The first pack run's words** are pairs of `bf16` numbers. -/
theorem k1_has {V : Nat → Value} (h : PkIn V) : ∀ p ∈ Gen.pk1_facts2 V, BfNum p.2 := by
  intro p hp
  simp only [Gen.pk1_facts2, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' rcases hp with rfl | hp
  all_goals
    refine cvtBf_has ?_ ?_ <;>
    first
      | exact split1_has (h.pr _ (by decide) (by decide))
      | exact split2_has (h.pr _ (by decide) (by decide))

/-- **The second pack run's words** are pairs of `bf16` numbers. -/
theorem k2_has {V : Nat → Value} (h : PkIn V) : ∀ p ∈ Gen.pk2_facts1 V, BfNum p.2 := by
  intro p hp
  simp only [Gen.pk2_facts1, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' rcases hp with rfl | hp
  all_goals exact cvtBf_has (h.sg _ (by decide) (by decide)) (h.sg _ (by decide) (by decide))

/-! ### The runs on a register file -/

def vP1 (V : Nat → Value) : Nat → Value := runK1.V' V
def vP2 (V : Nat → Value) : Nat → Value := runK2.V' V

/-- **The pack before the barrier** (pcs 951 to 998), from any registers that hold its inputs. -/
theorem pk1_seg {K : List Nat} (hK : runK1.live.all (fun r => K.contains r) = true)
    (V : Nat → Value) :
    SegU kernel Assumptions.all L g 951 (factsFrom K V) 999 (factsFrom (runK1.K' K) (vP1 V)) :=
  runK1.adv (L := L) (g := g) (K := K) runK1_ok V hK

/-- **The pack after the barrier** (pcs 1000 to 1007). -/
theorem pk2_seg {K : List Nat} (hK : runK2.live.all (fun r => K.contains r) = true)
    (V : Nat → Value) :
    SegU kernel Assumptions.all L g 1000 (factsFrom K V) 1008 (factsFrom (runK2.K' K) (vP2 V)) :=
  runK2.adv (L := L) (g := g) (K := K) runK2_ok V hK

theorem pk1_typed {V : Nat → Value} (h : PkIn V) {r : Nat} (hr : r ∈ runK1.outs) :
    BfNum (vP1 V r) := V'_out runK1 runK1_ok (P := fun _ => BfNum) (k1_has h) hr

theorem pk2_typed {V : Nat → Value} (h : PkIn V) {r : Nat} (hr : r ∈ runK2.outs) :
    BfNum (vP2 V r) := V'_out runK2 runK2_ok (P := fun _ => BfNum) (k2_has h) hr

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
