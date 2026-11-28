-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ref

@[expose] public section

/-! # Warpgroup 0's counts: the steps

The counts after an event (`Code.bump`): an event that is neither an arrival nor a successful
poll (`isMb`) keeps the mbarrier classes (`bump_plain`), an arrival adds one to its object's
arrivals (`bump_arrive`), a successful poll one to its object's acquisitions (`bump_acq`). The
place's counts move by the same one at each mbarrier event of the order (`acq_wv`, `acq_wq`,
`arr_arrV`, `acq_next`, `arr_next`, `arr_last`, `acq_sv`); `RefAt.congr` carries the invariant to
counts that agree on the mbarrier classes. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {O : Objs} {n n' : Cnt → Nat} {e : Event}

/-- An arrival or a successful poll. -/
def isMb (k : Kind) : Bool :=
  match k with
  | .arrive .. => true
  | .wait _ _ true _ _ => true
  | _ => false

/-- **Counts that agree on the mbarrier classes** have the same place facts. -/
theorem RefAt.congr {k : Reg} {i : Nat} {w : Words}
    (h : ∀ l, n' (.acq l) = n (.acq l) ∧ n' (.arrive l) = n (.arrive l))
    (hJ : RefAt O k i w n) : RefAt O k i w n' := by
  have hc : ∀ {a r i sv}, Counts O n a r i sv → Counts O n' a r i sv :=
    fun ⟨ha, hr⟩ => ⟨fun l => (h l).1.trans (ha l), fun l => (h l).2.trans (hr l)⟩
  cases k with
  | setup => exact hc hJ
  | loop => obtain ⟨r, hl, hC⟩ := hJ; exact ⟨r, hl, hc hC⟩
  | epi | fin => exact ⟨hJ.1, hc hJ.2⟩

theorem bump_plain (h : isMb e.kind = false) (l : Loc) :
    Code.bump cls n e (.acq l) = n (.acq l) ∧ Code.bump cls n e (.arrive l) = n (.arrive l) := by
  obtain ⟨pc, k⟩ := e
  simp only [Code.bump, cls]
  cases k with
  | wait m q ok a sc => cases ok <;> simp_all [kindOf, isMb]
  | tc k => cases k <;> simp_all [kindOf, isMb]
  | _ => simp_all [kindOf, isMb]

theorem bump_arrive (hpc : inRole e = true) {m : Loc} {tx c : Nat} {r : Bool} {sc : MbarScope}
    (hk : e.kind = .arrive m tx c r sc) (l : Loc) :
    Code.bump cls n e (.acq l) = n (.acq l) ∧
      Code.bump cls n e (.arrive l) = n (.arrive l) + ind (l = m) := by
  simp [Code.bump, cls, kindOf, hk, hpc, eq_comm]

theorem bump_acq (hpc : inRole e = true) {m : Loc} {q : Nat} {a : Bool} {sc : MbarScope}
    (hk : e.kind = .wait m q true a sc) (l : Loc) :
    Code.bump cls n e (.acq l) = n (.acq l) + ind (l = m) ∧
      Code.bump cls n e (.arrive l) = n (.arrive l) := by
  simp [Code.bump, cls, kindOf, hk, hpc, eq_comm]

/-- The counts' unfolding: the objects' indicators stay atoms. -/
macro "w0_cnt " h:ident : tactic => `(tactic| (simp only [acqCnt, arrCnt, use, ind, $h:ident,
    Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero, and_true, and_false, ↓reduceIte,
    Nat.reduceLeDiff, Bool.false_eq_true, true_and, false_and, Nat.le_refl, Nat.reduceEqDiff,
    Nat.zero_add] <;> omega))

theorem acq_wv (r : Nat) (l : Loc) :
    acqCnt O r 1 none l = acqCnt O r 0 none l + ind (l = O.vReady (r % 4)) := by
  rcases (by omega : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3) with h | h | h | h <;>
    w0_cnt h

theorem acq_wq (r : Nat) (l : Loc) :
    acqCnt O r 2 none l = acqCnt O r 1 none l + ind (l = O.qk (r % 2)) := by
  rcases (by omega : r % 2 = 0 ∨ r % 2 = 1) with h | h <;> w0_cnt h

theorem arr_arrV (r : Nat) (l : Loc) :
    arrCnt O true r 3 l = arrCnt O true r 2 l + ind (l = O.vFree (r % 4)) := by
  rcases (by omega : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3) with h | h | h | h <;>
    w0_cnt h

/-- The ring uses after block `r`. -/
theorem use_next (S j r : Nat) (hj : j < S) {k : Nat} (hk : k ≤ 3) :
    use S j r 3 k = ringUses S j (r + 1) := by
  rw [ringUses_succ hj]
  simp only [use, ind, hk, and_true]

theorem acq_next (r : Nat) (l : Loc) : acqCnt O (r + 1) 0 none l = acqCnt O r 3 none l := by
  simp only [acqCnt, use_next 4 0 r (by omega) (by omega : 1 ≤ 3),
    use_next 4 1 r (by omega) (by omega : 1 ≤ 3), use_next 4 2 r (by omega) (by omega : 1 ≤ 3),
    use_next 4 3 r (by omega) (by omega : 1 ≤ 3), use_next 2 0 r (by omega) (by omega : 2 ≤ 3),
    use_next 2 1 r (by omega) (by omega : 2 ≤ 3)]
  simp only [use, ind, and_false, ↓reduceIte,
    Nat.add_zero, show ¬ (1 ≤ 0) by omega, show ¬ (2 ≤ 0) by omega]

theorem arr_next (r : Nat) (l : Loc) :
    arrCnt O true (r + 1) 0 l = arrCnt O true r 3 l + ind (l = O.so (r % 2)) := by
  simp only [arrCnt, use_next 4 0 r (by omega) (le_refl 3), use_next 4 1 r (by omega) (le_refl 3),
    use_next 4 2 r (by omega) (le_refl 3), use_next 4 3 r (by omega) (le_refl 3),
    ringUses_succ (show 0 < 2 by omega) r, ringUses_succ (show 1 < 2 by omega) r]
  rcases (by omega : r % 2 = 0 ∨ r % 2 = 1) with h | h <;> w0_cnt h

theorem arr_last (r i : Nat) (l : Loc) :
    arrCnt O true r i l = arrCnt O false r i l + ind (l = O.last) := by
  simp only [arrCnt, ↓reduceIte, Bool.false_eq_true]
  omega

theorem acq_sv (r j : Nat) (l : Loc) :
    acqCnt O r 0 (some j) l = acqCnt O r 0 none l + ind (l = O.sv j) := by
  simp only [acqCnt]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
