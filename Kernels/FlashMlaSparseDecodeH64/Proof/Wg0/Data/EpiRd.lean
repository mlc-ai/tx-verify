-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.NumEs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.EpiFacts
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumLk

@[expose] public section

/-! # The epilogue's words at the staging stores

The facts at the staging stores of output chunk `c` (`f_os`) from the carried statistics, the
peer's row-sum word, the sink word and the accumulator words the chunk's load returned: word `j`
of the chunk is the bf16 pair of the products of accumulator words `2 j` and `2 j + 1` with the
factor `w0Fac (w0ESum r l + p) sk m`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

/-- The first register of the scaled words of output chunk `c`. -/
def eStart (c : Fin 4) : Nat := [1810, 1981, 2151, 2320].getD c.val 0

/-- The first register of the loaded words of output chunk `c`. -/
def eLoad (c : Fin 4) : Nat := [1745, 1916, 2086, 2255].getD c.val 0

/-- A site at the pc of a staging store is that store's site. -/
theorem site_pc_ost2 {s : Site} {c : Fin 4} {k : Fin 8} (h : s.pc = ost2Base c + k.val) :
    s = .ost2 c k := by
  revert h
  cases s with
  | ost2 c' k' =>
    intro h
    have hk := k.isLt
    have hk' := k'.isLt
    simp only [Site.pc] at h
    have : c' = c := by
      fin_cases c <;> fin_cases c' <;> simp [ost2Base] at h ⊢ <;> omega
    subst this
    have : k' = k := Fin.ext (by omega)
    rw [this]
  | sld a' k' => intro h; exfalso; revert h; revert a' k'; fin_cases c <;> fin_cases k <;> decide
  | pst k' | pld k' => intro h; exfalso; revert h; revert k'; fin_cases c <;> fin_cases k <;> decide
  | ost c' | rld c' | rldw c' | rst c' | rstw c' | old c' | oldw c' | ofpx c' | obar c' | oel c'
    | otma c' => intro h; exfalso; revert h; revert c'; fin_cases c <;> fin_cases k <;> decide
  | _ => intro h; exfalso; revert h; fin_cases c <;> fin_cases k <;> decide

theorem site_pc_1178 {s : Site} (h : s.pc = 1178) : s = .lse := by
  cases s
  case lse => rfl
  all_goals exfalso
  all_goals simp only [Site.pc] at h
  all_goals try omega
  case sld arm k => cases arm <;> fin_cases k <;> simp at h
  case ost2 c k => fin_cases c <;> simp [ost2Base] at h <;> omega
  all_goals (rename_i c; fin_cases c <;> simp at h)

theorem site_pc_1155 {s : Site} (h : s.pc = 1155) : s = .est := by
  cases s
  all_goals first
    | rfl
    | (exfalso; revert h; simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc]; done))
    | (rename_i a k; fin_cases a <;> fin_cases k <;> (exfalso; revert h; simp [Site.pc, ost2Base]))

theorem site_pc_566 {s : Site} (h : s.pc = 566) : s = .mst := by
  cases s
  all_goals first
    | rfl
    | (exfalso; revert h; simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc]; done))
    | (rename_i a k; fin_cases a <;> fin_cases k <;> (exfalso; revert h; simp [Site.pc, ost2Base]))

theorem w0Carry_l_nonneg (sc : ℝ) (bs : List (List Event)) : 0 ≤ (w0Carry sc bs).2 := by
  induction bs using List.reverseRecOn with
  | nil => simp [w0Carry]
  | append_singleton bs seg ih =>
    rw [w0Carry_snoc]
    simp only [w0Next]
    refine add_nonneg (mul_nonneg ih (by positivity)) (Finset.sum_nonneg fun i _ => ?_)
    unfold w0Prob
    split_ifs <;> positivity

/-- The loaded words of chunk `c`, as registers of the facts after its load. -/
theorem ow_rd (c : Fin 4) (V : Nat → Value) (pe : Value) (o : List Value) (ho : o.length = 64)
    {O : Nat → ℝ} (hO : ∀ i < 64, Rd (o.getD i (.pred false)) (O i)) :
    ∀ i < 64, Rd (lookupD (f_ow c.val V pe o) (eLoad c + i)) (O i) := by
  intro i hi
  have hz : ∀ r ∈ eRegs c.val, r ∈ eRegs c.val := fun r h => h
  unfold f_ow
  have hmem : eLoad c + i ∈ eRegs c.val := by
    fin_cases c <;> (simp [eLoad, eRegs, List.mem_range'_1]; omega)
  rw [lk_frame (K := eRegs c.val) hz (by
    simp only [f_fac, Gen.e7_facts1, List.map_cons, List.map_nil]
    fin_cases c <;> decide) hmem]
  have hlook : lookupD ((eRegs c.val).zip o) (eLoad c + i) = o.getD i (.pred false) := by
    have h := lookup_range_zip (eLoad c) o i (by omega)
    have hr : eRegs c.val = List.range' (eLoad c) o.length := by
      rw [ho]; fin_cases c <;> rfl
    unfold lookupD
    rw [hr, h]
    simp [List.getElem?_eq_getElem (show i < o.length by omega)]
  rw [hlook]
  exact hO i hi

theorem es_out_key (c : Fin 4) (W : Nat → Value) {j : Nat} (hj : j < 32) :
    eStart c + 3 * j ∈ (es_out c.val W).map Prod.fst := by
  fin_cases c <;>
    (simp only [eStart, es_out, Gen.es0_facts4, Gen.es1_facts4, Gen.es2_facts4,
      Gen.es3_facts4, List.map_cons, List.map_nil, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
     revert hj; revert j; decide)

theorem w0e_es_out (c : Fin 4) (W : Nat → Value) (O : Nat → ℝ) {f : ℝ}
    (hO : ∀ i < 64, Rd (W (eLoad c + i)) (O i))
    (hc : pairRead (W 3577) = some (.ok ((f : EReal), (f : EReal)))) :
    ∀ j < 32, lookupD (es_out c.val W) (eStart c + 3 * j) =
      Assumptions.bf16Pair (O (2 * j) * f) (O (2 * j + 1) * f) := by
  fin_cases c
  · exact w0e_es0 W O hO hc
  · exact w0e_es1 W O hO hc
  · exact w0e_es2 W O hO hc
  · exact w0e_es3 W O hO hc

/-- **The staging words of chunk `c`** from the carried statistics (`r` the true maximum, `m`, `l`
the carried maximum and sum, `sk` the sink word), the peer's row-sum word `pe`, and the loaded
words `o`. -/
theorem w0e_os_word (c : Fin 4) (x : BitVec 64) (mV lV mxV skV pe : Value) (o : List Value)
    {r sk : EReal} {m l p : ℝ} {O : Nat → ℝ}
    (hm : Rd mV m) (hl : Rd lV l) (hr : Rd mxV r) (hk : Rd skV sk) (hp : Rd pe p)
    (hl0 : 0 ≤ l) (hp0 : 0 ≤ p) (hrp : r = ⊥ → p = 0) (ho : o.length = 64)
    (hO : ∀ i < 64, Rd (o.getD i (.pred false)) (O i)) :
    ∀ j < 32, lookupD (f_os c.val (lookupD (f_car x mV lV mxV skV)) pe o) (eStart c + 3 * j) =
      Assumptions.bf16Pair (O (2 * j) * w0Fac (w0ESum r l + p) sk m)
        (O (2 * j + 1) * w0Fac (w0ESum r l + p) sk m) := by
  intro j hj
  set V := lookupD (f_car x mV lV mxV skV) with hV
  have hfac := w0e_fac V pe (r := r) (m := m) (l := l) (p := p) (sk := sk)
    (by simpa [hV, lookupD, f_car, List.lookup] using hr)
    (by simpa [hV, lookupD, f_car, List.lookup] using hm)
    (by simpa [hV, lookupD, f_car, List.lookup] using hl)
    (by simpa [hV, lookupD, f_car, List.lookup] using hk) hp hl0 hp0 hrp
  have hkey := es_out_key c (lookupD (f_ow c.val V pe o)) hj
  unfold f_os
  rw [lk_head_mem hkey]
  refine w0e_es_out c _ O (fun i hi => ?_) ?_ j hj
  · exact ow_rd c V pe o ho hO i hi
  · unfold f_ow
    rw [lk_head_mem (by simp only [f_fac, Gen.e7_facts1, List.map_cons, List.map_nil]; decide)]
    exact hfac

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
