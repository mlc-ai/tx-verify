-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Interface
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # `tc_gemm`: the whole trace of a thread, by position

A thread's trace is a prefix of its whole trace `fullE P` for the values `P` its events returned
(`Par`: the column thread 0 stored, the address read and the column kept from it, the numbers of
failed polls, the loaded words), possibly followed by one undefined-behaviour event: after a read
whose bytes give no column, or at the store of a loaded word that is not four bytes (`Wit`, from
the thread facts: `wit`). `fullAt` gives the event at each position of `fullE` (`full_get`): the
head (`headE`) and the first barrier, the read at `hd g`, thread 0's polls of `bar0`, MMA and
commit, the polls of `bar1` from `tl g P`, the fence, the load at `ldIdx g P`, then the wait, the
stores, the fences, the second barrier, warp 0's deallocation and the exit (`postAt`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- What the open events of a thread returned, and how often it polled. -/
structure Par where
  /-- The column of the address thread 0 stores. -/
  col : Nat
  /-- The read of the address, and the column kept from it. -/
  rd : List (Option Byte)
  c : Nat
  /-- Failed polls of `bar0` (thread 0). -/
  n0 : Nat
  /-- Failed polls of `bar1`. -/
  n1 : Nat
  /-- The words loaded from Tensor Memory. -/
  vals : List Value

/-- The whole trace of thread `g`. -/
def fullE (A B D S g : Nat) (P : Par) : List Event :=
  preW1 A B S g P.col P.rd P.c P.n0 ++ List.replicate P.n1 (wait1E S false) ++
    lastE D S g P.c P.vals

/-- The position of the address read. -/
def hd (g : Nat) : Nat := if g = 0 then 9 else if g / 32 = 0 then 2 else 1
/-- The position of the first poll of `bar1`. -/
def tl (g : Nat) (P : Par) : Nat := hd g + 1 + if g = 0 then P.n0 + 3 else 0
/-- The position of the load from Tensor Memory. -/
def ldIdx (g : Nat) (P : Par) : Nat := tl g P + P.n1 + 2

/-- After the load: its wait, the stores, the fences and the barrier, warp 0's deallocation. -/
def postE (D g c : Nat) (vals : List Value) : List Event :=
  [wldE] ++ storesE D g vals 8 ++ [fbE, bar1E, fa2E] ++ (if g / 32 = 0 then [deallocE c] else [])

variable {A B D S g c : Nat} {vals : List Value}

theorem headE_length {col : Nat} :
    (headE A B S g col).length + 1 = hd g := by
  unfold headE hd; split_ifs <;> rfl

theorem lastE_eq : lastE D S g c vals =
    [wait1E S true, fa1E, ldE g c vals] ++ (postE D g c vals ++ [exitE]) := by
  simp [lastE, postE]

theorem storesE_length (j : Nat) : (storesE D g vals j).length = j := by simp [storesE]

theorem storesE_get {j k : Nat} :
    (storesE D g vals j)[k]? = if k < j then some (stE D g vals k) else none := by
  unfold storesE
  split_ifs with h
  · simp [h]
  · simp; omega

/-- `postE ++ [exitE]`, by position. -/
def postAt (D g c : Nat) (vals : List Value) (k : Nat) : Option Event :=
  if k = 0 then some wldE
  else if k < 9 then some (stE D g vals (k - 1))
  else if k = 9 then some fbE
  else if k = 10 then some bar1E
  else if k = 11 then some fa2E
  else if k = 12 then some (if g / 32 = 0 then deallocE c else exitE)
  else if k = 13 ∧ g / 32 = 0 then some exitE
  else none

theorem post_get (k : Nat) : (postE D g c vals ++ [exitE])[k]? = postAt D g c vals k := by
  have e : postE D g c vals ++ [exitE] = wldE :: (storesE D g vals 8 ++
      ([fbE, bar1E, fa2E] ++ if g / 32 = 0 then [deallocE c, exitE] else [exitE])) := by
    unfold postE; split_ifs <;> simp
  rw [e]
  rcases k with _ | k
  · simp [postAt]
  rw [List.getElem?_cons_succ]
  by_cases hk : k < 8
  · rw [List.getElem?_append_left (by rw [storesE_length]; omega), storesE_get, ite_eq_left hk]
    simp [postAt, show k + 1 < 9 by omega]
  rw [List.getElem?_append_right (by rw [storesE_length]; omega), storesE_length]
  obtain ⟨i, rfl⟩ : ∃ i, k = 8 + i := ⟨k - 8, by omega⟩
  rw [Nat.add_sub_cancel_left]
  by_cases hg : g / 32 = 0
  · rcases i with _ | _ | _ | _ | _ | i <;> simp [postAt, hg]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rcases i with _ | _ | _ | _ | i <;> simp [postAt, hg]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- The whole trace of thread `g`, by position. -/
def fullAt (A B D S g : Nat) (P : Par) (j : Nat) : Option Event :=
  if j < hd g then (headE A B S g P.col ++ [bar0E])[j]?
  else if j = hd g then some (rdE S P.rd)
  else if g = 0 ∧ j < hd g + 1 + P.n0 then some (wait0E S false)
  else if g = 0 ∧ j = hd g + 1 + P.n0 then some (wait0E S true)
  else if g = 0 ∧ j = hd g + 2 + P.n0 then some (mmaE S P.c)
  else if g = 0 ∧ j = hd g + 3 + P.n0 then some (commitE S)
  else if j < tl g P + P.n1 then some (wait1E S false)
  else if j = tl g P + P.n1 then some (wait1E S true)
  else if j = tl g P + P.n1 + 1 then some fa1E
  else if j = ldIdx g P then some (ldE g P.c P.vals)
  else postAt D g P.c P.vals (j - (ldIdx g P + 1))

/-- The trace from the first poll of `bar1`, by position. -/
theorem tail_get (P : Par) (k : Nat) :
    (List.replicate P.n1 (wait1E S false) ++ lastE D S g P.c P.vals)[k]? =
      if tl g P + k < tl g P + P.n1 then some (wait1E S false)
      else if tl g P + k = tl g P + P.n1 then some (wait1E S true)
      else if tl g P + k = tl g P + P.n1 + 1 then some fa1E
      else if tl g P + k = ldIdx g P then some (ldE g P.c P.vals)
      else postAt D g P.c P.vals (tl g P + k - (ldIdx g P + 1)) := by
  rw [lastE_eq]
  by_cases h4 : k < P.n1
  · rw [List.getElem?_append_left (by simpa using h4), List.getElem?_replicate, ite_eq_left h4,
      ite_eq_left (by omega)]
  rw [List.getElem?_append_right (by simp; omega), ite_eq_right (by omega)]
  simp only [List.length_replicate]
  obtain ⟨q, rfl⟩ : ∃ q, k = P.n1 + q := ⟨k - P.n1, by omega⟩
  rw [Nat.add_sub_cancel_left]
  rcases q with _ | _ | _ | q
  · simp
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by simp [ldIdx]; omega)]; rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by simp [ldIdx]; omega)]
    simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
    rw [post_get]
    congr 1
    simp [ldIdx]; omega

theorem full_get (P : Par) (j : Nat) : (fullE A B D S g P)[j]? = fullAt A B D S g P j := by
  have hh := headE_length (A := A) (B := B) (S := S) (g := g) (col := P.col)
  have hb : (headE A B S g P.col ++ [bar0E]).length = hd g := by simp; omega
  have hpre : fullE A B D S g P = (headE A B S g P.col ++ [bar0E]) ++ (rdE S P.rd ::
      ((if g = 0 then midE S P.c P.n0 else []) ++
        (List.replicate P.n1 (wait1E S false) ++ lastE D S g P.c P.vals))) := by
    simp [fullE, preW1]
  rw [hpre]
  unfold fullAt
  by_cases h1 : j < hd g
  · rw [List.getElem?_append_left (by omega), ite_eq_left h1]
  rw [List.getElem?_append_right (by omega), hb, ite_eq_right h1]
  by_cases h1' : j = hd g
  · subst h1'; simp
  rw [ite_eq_right h1']
  obtain ⟨i, rfl⟩ : ∃ i, j = hd g + (i + 1) := ⟨j - hd g - 1, by omega⟩
  rw [show hd g + (i + 1) - hd g = i + 1 by omega, List.getElem?_cons_succ]
  by_cases hg : g = 0
  · subst hg
    rw [ite_eq_left rfl]
    simp only [true_and]
    have hm : (midE S P.c P.n0).length = P.n0 + 3 := by simp [midE]
    by_cases h2 : i < P.n0 + 3
    · rw [List.getElem?_append_left (by omega)]
      unfold midE
      by_cases h3 : i < P.n0
      · rw [List.getElem?_append_left (by simpa using h3), List.getElem?_replicate, ite_eq_left h3,
          ite_eq_left (by omega)]
      · rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_replicate]
        obtain ⟨q, rfl⟩ : ∃ q, i = P.n0 + q := ⟨i - P.n0, by omega⟩
        have hq : q < 3 := by omega
        rw [Nat.add_sub_cancel_left]
        interval_cases q
        · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; rfl
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; rfl
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_left (by omega)]; rfl
    · rw [List.getElem?_append_right (by omega), hm, ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, i = P.n0 + 3 + k := ⟨i - (P.n0 + 3), by omega⟩
      rw [Nat.add_sub_cancel_left, show hd 0 + (P.n0 + 3 + k + 1) = tl 0 P + k by
        simp [tl]; omega]
      exact tail_get P k
  · simp only [List.nil_append, hg, false_and, ↓reduceIte]
    rw [show hd g + (i + 1) = tl g P + i by simp [tl, hg]; omega]
    exact tail_get P i

/-! ### The events, case by case -/

theorem head_cases {col j : Nat} {ev : Event}
    (h : (headE A B S g col ++ [bar0E])[j]? = some ev) :
    (g / 32 = 0 ∧ j = 0 ∧ ev = allocE S) ∨ (g = 0 ∧ j = 1 ∧ ev = tslotE S col) ∨
    (g = 0 ∧ j = 2 ∧ ev = init0E S) ∨ (g = 0 ∧ j = 3 ∧ ev = init1E S) ∨
    (g = 0 ∧ j = 4 ∧ ev = fenceE) ∨ (g = 0 ∧ j = 5 ∧ ev = arriveE S) ∨
    (g = 0 ∧ j = 6 ∧ ev = bulkAE A S) ∨ (g = 0 ∧ j = 7 ∧ ev = bulkBE B S) ∨
    (j + 1 = hd g ∧ ev = bar0E) := by
  unfold headE at h
  by_cases h0 : g = 0
  · subst h0
    have hj : j < 9 := by
      by_contra hj; rw [List.getElem?_eq_none (by simp; omega)] at h; cases h
    interval_cases j <;> simp at h <;> subst h <;> simp [hd]
  by_cases h32 : g / 32 = 0
  · rw [ite_eq_right h0, ite_eq_left h32] at h
    have hj : j < 2 := by
      by_contra hj; rw [List.getElem?_eq_none (by simp; omega)] at h; cases h
    interval_cases j <;> simp at h <;> subst h <;> simp [hd, h0, h32]
  · rw [ite_eq_right h0, ite_eq_right h32] at h
    have hj : j < 1 := by
      by_contra hj; rw [List.getElem?_eq_none (by simp; omega)] at h; cases h
    interval_cases j; simp at h; subst h; simp [hd, h0, h32]

theorem post_cases {k : Nat} {ev : Event} (h : postAt D g c vals k = some ev) :
    (k = 0 ∧ ev = wldE) ∨ (∃ j < 8, k = j + 1 ∧ ev = stE D g vals j) ∨ (k = 9 ∧ ev = fbE) ∨
    (k = 10 ∧ ev = bar1E) ∨ (k = 11 ∧ ev = fa2E) ∨ (g / 32 = 0 ∧ k = 12 ∧ ev = deallocE c) ∨
    (k = (if g / 32 = 0 then 13 else 12) ∧ ev = exitE) := by
  unfold postAt at h
  by_cases h1 : k = 0
  · rw [ite_eq_left h1] at h; cases h; exact .inl ⟨h1, rfl⟩
  rw [ite_eq_right h1] at h
  by_cases h2 : k < 9
  · rw [ite_eq_left h2] at h; cases h; exact .inr (.inl ⟨k - 1, by omega, by omega, rfl⟩)
  rw [ite_eq_right h2] at h
  by_cases h3 : k = 9
  · rw [ite_eq_left h3] at h; cases h; exact .inr (.inr (.inl ⟨h3, rfl⟩))
  rw [ite_eq_right h3] at h
  by_cases h4 : k = 10
  · rw [ite_eq_left h4] at h; cases h; exact .inr (.inr (.inr (.inl ⟨h4, rfl⟩)))
  rw [ite_eq_right h4] at h
  by_cases h5 : k = 11
  · rw [ite_eq_left h5] at h; cases h; exact .inr (.inr (.inr (.inr (.inl ⟨h5, rfl⟩))))
  rw [ite_eq_right h5] at h
  by_cases h6 : k = 12
  · rw [ite_eq_left h6] at h
    by_cases hg : g / 32 = 0
    · rw [ite_eq_left hg] at h; cases h
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨hg, h6, rfl⟩)))))
    · rw [ite_eq_right hg] at h; cases h
      exact .inr (.inr (.inr (.inr (.inr (.inr ⟨by simp [hg, h6], rfl⟩)))))
  rw [ite_eq_right h6] at h
  by_cases h7 : k = 13 ∧ g / 32 = 0
  · rw [ite_eq_left h7] at h; cases h
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨by simp [h7.2, h7.1], rfl⟩)))))
  · rw [ite_eq_right h7] at h; cases h

/-- Every event of the whole trace, by its position. -/
theorem full_cases {P : Par} {j : Nat} {ev : Event} (h : fullAt A B D S g P j = some ev) :
    (j < hd g ∧ (headE A B S g P.col ++ [bar0E])[j]? = some ev) ∨
    (j = hd g ∧ ev = rdE S P.rd) ∨
    (g = 0 ∧ hd g < j ∧ j < hd g + 1 + P.n0 ∧ ev = wait0E S false) ∨
    (g = 0 ∧ j = hd g + 1 + P.n0 ∧ ev = wait0E S true) ∨
    (g = 0 ∧ j = hd g + 2 + P.n0 ∧ ev = mmaE S P.c) ∨
    (g = 0 ∧ j = hd g + 3 + P.n0 ∧ ev = commitE S) ∨
    (tl g P ≤ j ∧ j < tl g P + P.n1 ∧ ev = wait1E S false) ∨
    (j = tl g P + P.n1 ∧ ev = wait1E S true) ∨
    (j = tl g P + P.n1 + 1 ∧ ev = fa1E) ∨
    (j = ldIdx g P ∧ ev = ldE g P.c P.vals) ∨
    (ldIdx g P < j ∧ postAt D g P.c P.vals (j - (ldIdx g P + 1)) = some ev) := by
  have htl : tl g P = hd g + 1 + if g = 0 then P.n0 + 3 else 0 := rfl
  have hld : ldIdx g P = tl g P + P.n1 + 2 := rfl
  unfold fullAt at h
  by_cases h1 : j < hd g
  · rw [ite_eq_left h1] at h; exact .inl ⟨h1, h⟩
  rw [ite_eq_right h1] at h
  by_cases h2 : j = hd g
  · rw [ite_eq_left h2] at h; cases h; exact .inr (.inl ⟨h2, rfl⟩)
  rw [ite_eq_right h2] at h
  by_cases h3 : g = 0 ∧ j < hd g + 1 + P.n0
  · rw [ite_eq_left h3] at h; cases h; exact .inr (.inr (.inl ⟨h3.1, by omega, h3.2, rfl⟩))
  rw [ite_eq_right h3] at h
  by_cases h4 : g = 0 ∧ j = hd g + 1 + P.n0
  · rw [ite_eq_left h4] at h; cases h; exact .inr (.inr (.inr (.inl ⟨h4.1, h4.2, rfl⟩)))
  rw [ite_eq_right h4] at h
  by_cases h5 : g = 0 ∧ j = hd g + 2 + P.n0
  · rw [ite_eq_left h5] at h; cases h; exact .inr (.inr (.inr (.inr (.inl ⟨h5.1, h5.2, rfl⟩))))
  rw [ite_eq_right h5] at h
  by_cases h6 : g = 0 ∧ j = hd g + 3 + P.n0
  · rw [ite_eq_left h6] at h; cases h
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨h6.1, h6.2, rfl⟩)))))
  rw [ite_eq_right h6] at h
  have hge : tl g P ≤ j := by
    rw [htl]; by_cases hg : g = 0
    · subst hg; rw [ite_eq_left rfl]; simp only [true_and] at h3 h4 h5 h6; omega
    · rw [ite_eq_right hg]; omega
  by_cases h7 : j < tl g P + P.n1
  · rw [ite_eq_left h7] at h; cases h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hge, h7, rfl⟩))))))
  rw [ite_eq_right h7] at h
  by_cases h8 : j = tl g P + P.n1
  · rw [ite_eq_left h8] at h; cases h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h8, rfl⟩)))))))
  rw [ite_eq_right h8] at h
  by_cases h9 : j = tl g P + P.n1 + 1
  · rw [ite_eq_left h9] at h; cases h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h9, rfl⟩))))))))
  rw [ite_eq_right h9] at h
  by_cases h10 : j = ldIdx g P
  · rw [ite_eq_left h10] at h; cases h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h10, rfl⟩)))))))))
  rw [ite_eq_right h10] at h
  exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨by omega, h⟩)))))))))

/-! ### Lengths and counts -/

/-- `fullE` before the load from Tensor Memory. -/
def preLd (A B S g : Nat) (P : Par) : List Event :=
  preW1 A B S g P.col P.rd P.c P.n0 ++ List.replicate P.n1 (wait1E S false) ++ [wait1E S true, fa1E]

theorem fullE_preLd (P : Par) :
    fullE A B D S g P = preLd A B S g P ++ ldE g P.c P.vals :: (postE D g P.c P.vals ++ [exitE]) :=
      by
  simp [fullE, preLd, lastE_eq]

theorem preLd_length (P : Par) : (preLd A B S g P).length = ldIdx g P := by
  have hh := headE_length (A := A) (B := B) (S := S) (g := g) (col := P.col)
  simp only [preLd, preW1, ldIdx, tl, List.length_append, List.length_cons, List.length_replicate,
    List.length_nil]
  split_ifs <;> simp [midE] <;> omega

theorem post_length : (postE D g c vals ++ [exitE]).length = if g / 32 = 0 then 14 else 13 := by
  unfold postE; split_ifs <;> simp [storesE_length]

theorem fullE_length (P : Par) :
    (fullE A B D S g P).length = ldIdx g P + if g / 32 = 0 then 15 else 14 := by
  rw [fullE_preLd, List.length_append, preLd_length, List.length_cons, post_length]
  split_ifs <;> omega

/-- `fullE` up to a position after the load. -/
theorem take_post {r : Nat} (P : Par) :
    (fullE A B D S g P).take (ldIdx g P + 1 + r) =
      preLd A B S g P ++ ldE g P.c P.vals :: (postE D g P.c P.vals ++ [exitE]).take r := by
  rw [fullE_preLd, List.take_append, preLd_length,
    List.take_of_length_le (by rw [preLd_length]; omega),
    show ldIdx g P + 1 + r - ldIdx g P = r + 1 by omega, List.take_succ_cons]

theorem headE_bar {col : Nat} : (headE A B S g col).countP Execution.isBar = 0 := by
  unfold headE
  split_ifs <;> simp [Execution.isBar, allocE, tslotE, init0E, init1E, fenceE, arriveE, bulkAE,
    bulkBE]

theorem preLd_bar (P : Par) : (preLd A B S g P).countP Execution.isBar = 1 := by
  unfold preLd preW1 midE
  split_ifs <;> simp [List.countP_append, headE_bar, Execution.isBar, bar0E, rdE, wait0E, mmaE,
    commitE, wait1E, fa1E, List.countP_replicate, List.countP_cons]

theorem headE_tc {col : Nat} :
    (headE A B S g col).countP isTcColl = if g / 32 = 0 then 1 else 0 := by
  unfold headE
  split_ifs <;> first | omega | simp [isTcColl, allocE, tslotE, init0E, init1E, fenceE, arriveE,
    bulkAE, bulkBE, List.countP_cons]

theorem preLd_tc (P : Par) :
    (preLd A B S g P).countP isTcColl = if g / 32 = 0 then 1 else 0 := by
  unfold preLd preW1 midE
  simp only [List.countP_append, headE_tc]
  split_ifs <;> simp [isTcColl, bar0E, rdE, wait0E, mmaE, commitE, wait1E, fa1E,
    List.countP_replicate]

theorem post_take12 :
    (postE D g c vals ++ [exitE]).take 12 = wldE :: (storesE D g vals 8 ++ [fbE, bar1E, fa2E]) := by
  have hs := storesE_length (D := D) (g := g) (vals := vals) 8
  have e : postE D g c vals ++ [exitE] = (wldE :: (storesE D g vals 8 ++ [fbE, bar1E, fa2E])) ++
      ((if g / 32 = 0 then [deallocE c] else []) ++ [exitE]) := by simp [postE]
  rw [e, List.take_append_of_le_length (by simp [hs]), List.take_of_length_le (by simp [hs])]

theorem storesE_count (p : Event → Bool) (hp : ∀ j, p (stE D g vals j) = false) :
    (storesE D g vals 8).countP p = 0 := by
  rw [List.countP_eq_zero]
  intro x hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  rw [storesE_get] at hj
  split_ifs at hj
  · cases hj; simp [hp]

theorem fullE_tc (P : Par) :
    (fullE A B D S g P).countP isTcColl = if g / 32 = 0 then 4 else 2 := by
  rw [fullE_preLd, List.countP_append, preLd_tc, List.countP_cons]
  unfold postE
  have := storesE_count (D := D) (g := g) (vals := P.vals) isTcColl
    (fun j => by simp [stE, isTcColl])
  have hld : isTcColl (ldE g P.c P.vals) = true := rfl
  simp only [hld, ↓reduceIte]
  split_ifs <;> simp [List.countP_append, this, isTcColl, wldE, fbE, bar1E, fa2E, deallocE,
    exitE, List.countP_cons]

/-! ### Specific positions -/

section
variable (P : Par)

theorem tl_ge : hd g + 1 ≤ tl g P := by unfold tl; split_ifs <;> omega
theorem ldIdx_eq : ldIdx g P = tl g P + P.n1 + 2 := rfl
theorem hd_pos : 1 ≤ hd g := by unfold hd; split_ifs <;> omega
theorem hd_le : hd g ≤ 9 := by unfold hd; split_ifs <;> omega
theorem tl_zero : tl 0 P = hd 0 + 4 + P.n0 := by simp [tl]; omega
theorem tl_ne {g : Nat} (hg : g ≠ 0) : tl g P = hd g + 1 := by simp [tl, hg]

theorem fullAt_head {j : Nat} (hj : j < hd g) :
    fullAt A B D S g P j = (headE A B S g P.col ++ [bar0E])[j]? := by
  unfold fullAt; rw [ite_eq_left hj]

theorem fullAt_rd : fullAt A B D S g P (hd g) = some (rdE S P.rd) := by
  unfold fullAt; rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem fullAt_tail {j : Nat} (hj : tl g P ≤ j) :
    fullAt A B D S g P j =
      if j < tl g P + P.n1 then some (wait1E S false)
      else if j = tl g P + P.n1 then some (wait1E S true)
      else if j = tl g P + P.n1 + 1 then some fa1E
      else if j = ldIdx g P then some (ldE g P.c P.vals)
      else postAt D g P.c P.vals (j - (ldIdx g P + 1)) := by
  have h1 := tl_ge (g := g) P
  unfold fullAt
  by_cases hg : g = 0
  · subst hg
    have := tl_zero P
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [hg, false_and, ↓reduceIte]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem fullAt_w1t : fullAt A B D S g P (tl g P + P.n1) = some (wait1E S true) := by
  rw [fullAt_tail P (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem fullAt_fa1 : fullAt A B D S g P (tl g P + P.n1 + 1) = some fa1E := by
  rw [fullAt_tail P (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem fullAt_ld : fullAt A B D S g P (ldIdx g P) = some (ldE g P.c P.vals) := by
  rw [fullAt_tail P (by rw [ldIdx_eq]; omega), ite_eq_right (by rw [ldIdx_eq]; omega),
    ite_eq_right (by rw [ldIdx_eq]; omega), ite_eq_right (by rw [ldIdx_eq]; omega),
    ite_eq_left rfl]

theorem fullAt_post (r : Nat) :
    fullAt A B D S g P (ldIdx g P + 1 + r) = postAt D g P.c P.vals r := by
  rw [fullAt_tail P (by rw [ldIdx_eq]; omega), ite_eq_right (by rw [ldIdx_eq]; omega),
    ite_eq_right (by rw [ldIdx_eq]; omega), ite_eq_right (by rw [ldIdx_eq]; omega),
    ite_eq_right (by omega), Nat.add_sub_cancel_left]

theorem fullAt_w0t : fullAt A B D S 0 P (hd 0 + 1 + P.n0) = some (wait0E S true) := by
  unfold fullAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left ⟨rfl, rfl⟩]

theorem fullAt_mma : fullAt A B D S 0 P (hd 0 + 2 + P.n0) = some (mmaE S P.c) := by
  unfold fullAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left ⟨rfl, rfl⟩]

theorem fullAt_commit : fullAt A B D S 0 P (hd 0 + 3 + P.n0) = some (commitE S) := by
  unfold fullAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨rfl, rfl⟩]

theorem fullAt_bar0 : fullAt A B D S g P (hd g - 1) = some bar0E := by
  have := hd_pos (g := g)
  rw [fullAt_head P (by omega)]
  have hh := headE_length (A := A) (B := B) (S := S) (g := g) (col := P.col)
  rw [List.getElem?_append_right (by omega), show hd g - 1 - (headE A B S g P.col).length = 0 by
    omega]
  rfl

theorem fullAt_w0f {j : Nat} (h1 : hd 0 < j) (h2 : j < hd 0 + 1 + P.n0) :
    fullAt A B D S 0 P j = some (wait0E S false) := by
  unfold fullAt; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨rfl, h2⟩]

theorem fullAt_w1f {j : Nat} (h1 : tl g P ≤ j) (h2 : j < tl g P + P.n1) :
    fullAt A B D S g P j = some (wait1E S false) := by
  rw [fullAt_tail P h1, ite_eq_left h2]

end

theorem bar01 : bar0 S ≠ bar1 S := by simp [bar0, bar1]

end

end PTX.Kernels.TcGemm.Proof
