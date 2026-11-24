-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueElect
public import Kernels.TmlFa4Fwd.Proof.PrologueInit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section

def initGroups : Vector (List (Fin 34)) 16 := #v[
  [0, 1], [2, 3], [4, 5, 6], [7, 8, 9], [10, 11], [12, 13], [14, 15], [16, 17],
  [18, 19], [20, 21], [22, 23], [24, 25], [26, 27], [28, 29], [30, 31], [32, 33]]

/-- The consecutive initialization sites controlled by an election. -/
def initGroup (j : Fin 16) : List (Fin 34) := initGroups[j]

def initEvent (l : Launch) (g : Nat) (i : Fin 34) : Event :=
  let s := initSite i
  ⟨s.pc, .mbInit ⟨.shared, g / l.block, l.sharedBase + s.baseOffset + s.displacement⟩ s.count⟩

theorem groupExit (j : Fin 16) :
    (electSite j).skipPc = (electSite j).pc + 4 + (initGroup j).length := by
  fin_cases j <;> rfl

theorem groupCode (j : Fin 16) (k : Nat) (i : Fin 34) (h : (initGroup j)[k]? = some i) :
    let s := initSite i
    let e := electSite j
    s.pc = e.pc + 4 + k ∧ s.countReg = e.countReg ∧ s.count = e.count ∧
      s.baseReg ≠ e.skipReg ∧ s.baseReg ≠ e.countReg := by
  have hk := (List.getElem?_eq_some_iff.mp h).choose
  have hlim : (initGroup j).length ≤ 3 := by fin_cases j <;> decide
  have hk3 : k < 3 := by omega
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;>
    fin_cases j <;> first | (cases h; decide) | cases h

/-- The other lanes take the branch and arrive at the same join in two local steps. -/
theorem followerInitGroupWith {A : List Assumption} [StartupAgreement A]
    {l : Launch} {g : Nat} {t : TState} (j : Fin 16)
    (hp : t.pc = (electSite j).pc + 1) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (he : t.regs (electSite j).chosenReg = some (.pred false)) :
    ∃ u, run kernel A l g 2 t = some u ∧ u.pc = (electSite j).skipPc ∧
      u.fault = none ∧ u.sub = 0 ∧ u.acc = [] ∧
      ∀ r ≠ (electSite j).skipReg, u.regs r = t.regs r := by
  let u := { next (setReg t (electSite j).skipReg (.pred true)) with pc := (electSite j).skipPc }
  refine ⟨u, electRouteWith (A := A) (g := g) j false hp hf hs ha he, rfl, hf, hs, ha, ?_⟩
  intro r hr
  simp [u, next, setReg, hr]

end
end PTX.Kernels.TmlFa4Fwd.Prologue
