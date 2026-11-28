-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.NumVal
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

theorem ev_fmaF {fz : Bool} {d : Value} {a b c : Nat} {x y z : Value} {u : EReal} {v w : ℝ}
    (hb : b ≠ a) (hc : c ≠ a) (hcb : c ≠ b) (hx : Ev x u) (hy : Ev y v) (hz : Ev z w)
    (hv : 0 < v) : Ev (okVal d ((fF (floatE (fmaI .rn fz)) [.reg a, .reg b, .reg c]) [x, y, z]))
      (u * v + w) := by
  rw [fF_reg3 hb hc hcb]
  exact ev_fma hx hy hz hv

/-- The score register each shifted score (register `1288 + 2 u`) is made of. -/
def srcTab (u : Nat) : Nat :=
  [1415, 1416, 1417, 1418, 1420, 1421, 1422, 1423, 1425, 1426, 1428, 1429, 1431, 1432,
   1433, 1434, 1436, 1437, 1438, 1439, 1441, 1442, 1443, 1444, 1446, 1447, 1449, 1450,
   1452, 1453, 1454, 1455, 1457, 1458, 1460, 1461, 1463, 1464, 1465, 1466, 1468, 1469,
   1471, 1472, 1474, 1475, 1476, 1477, 1479, 1480, 1481, 1482, 1484, 1485, 1486, 1487,
   1489, 1490, 1492, 1493, 1495, 1496, 1497, 1498].getD u 0

/-- **The shifted scores**: the register `r` of the facts holds `x * scale + c` of the masked score
`x` in register `srcTab ((r - 1288) / 2)`. -/
theorem e1_ev {V : Nat → Value} {xs : Nat → EReal} {sc c : ℝ}
    (hs : ∀ r ∈ scoreRegs, Ev (V r) (xs r)) (h498 : Ev (V 498) sc) (hsc : 0 < sc)
    (hc : Ev (Gen.ex1_v1848 V) c) :
    ∀ p ∈ Gen.ex1_facts3 V, Ev p.2 (xs (srcTab ((p.1 - 1288) / 2)) * sc + c) := by
  intro p hp
  simp only [Gen.ex1_facts3, List.mem_cons, List.not_mem_nil] at hp
  repeat' rcases hp with rfl | hp
  all_goals
    simp only [srcTab, Nat.reduceSub, Nat.reduceDiv, List.getD_cons_zero, List.getD_cons_succ]
    refine ev_fmaF ?_ ?_ ?_ (hs _ ?_) h498 hc hsc <;> decide

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
