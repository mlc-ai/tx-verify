-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTotB
public import Kernels.InklingRelDecode.Proof.Thread.SmFlt

@[expose] public section

/-! # The first half of the score stage read back on `f32` numbers

Where the S words are `f32` numbers and the bias words `bf16` numbers or zero (`BfOk`), the
values of `SmTot` are the numbers of `SmFin`: the scores' `fma` has the exact outcome
(`scE_real`), the words at the shuffle are the words of `D.fin` (`finT_eq`, so the machine's
successor at the wait is `D.afterWait`: `afterWaitT_eq`), no instruction of the stage's first half
faults (`s1Ok_real`), and the thread's maximum is the value of the extended-real maximum of the
words (`ownV_eq`, for any score words). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### The tree on score words -/

/-- The columns that a register of the tree holds as a single unpacked word. -/
def RI.updS : RI → List (Nat × Option Nat) → List (Nat × Option Nat)
  | .unp a b q, st => (b, some (2 * q + 1)) :: (a, some (2 * q)) :: st
  | .mx2 d _ _, st => (d, none) :: st
  | .mx3 d _ _ _, st => (d, none) :: st

/-- The register-word list after the first `c` instructions. -/
def rsSt (c : Nat) : List (Nat × Option Nat) := (rmCode.take c).foldl (fun st i => i.updS st) []

theorem rsSt_succ {c : Nat} {i : RI} (h : rmCode[c]? = some i) :
    rsSt (c + 1) = i.updS (rsSt c) := by
  unfold rsSt
  rw [List.take_succ, h]
  simp [List.foldl_append]

/-- The unpacked word of the column `j` is in its register at the end of the tree. -/
theorem rs_word : ∀ j < 64, (rsSt 74).lookup (colReg j) = some (some j) := by decide +kernel

/-- A register of the tree that holds the word of a column holds the word `w` of that column. -/
theorem rv_word (w : Nat → Value) : ∀ c r k, (rsSt c).lookup r = some (some k) →
    (rvSt w c).lookup r = some (w k) := by
  intro c
  induction c with
  | zero => intro r k h; simp [rsSt] at h
  | succ c ih =>
    intro r k h
    rcases hi : rmCode[c]? with _ | i
    · have hl : rmCode.length ≤ c := List.getElem?_eq_none_iff.mp hi
      have e1 : rmCode.take (c + 1) = rmCode.take c := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp only [rsSt, e1] at h
      simp only [rvSt, e1]
      exact ih r k h
    · rw [rsSt_succ hi] at h
      rw [rvSt_succ hi]
      cases i with
      | unp a b q =>
        simp only [RI.updS, RI.updV, List.lookup] at h ⊢
        by_cases hb : r = b
        · subst hb
          simp only [beq_self_eq_true, Option.some.injEq] at h ⊢
          rw [← h]
        · simp only [beq_false_of_ne hb] at h ⊢
          by_cases ha : r = a
          · subst ha
            simp only [beq_self_eq_true, Option.some.injEq] at h ⊢
            rw [← h]
          · simp only [beq_false_of_ne ha] at h ⊢
            exact ih r k h
      | mx2 d a b =>
        simp only [RI.updS, RI.updV, List.lookup] at h ⊢
        by_cases hd : r = d
        · subst hd; simp at h
        · simp only [beq_false_of_ne hd] at h ⊢
          exact ih r k h
      | mx3 d a b e =>
        simp only [RI.updS, RI.updV, List.lookup] at h ⊢
        by_cases hd : r = d
        · subst hd; simp at h
        · simp only [beq_false_of_ne hd] at h ⊢
          exact ih r k h

/-- The pair of an unpack of the tree is below 32. -/
def RI.qOk : RI → Bool
  | .unp _ _ q => decide (q < 32)
  | _ => true

theorem rmCode_qOk : rmCode.all RI.qOk = true := by decide +kernel

theorem rmCode_unp_lt {c a b q : Nat} (h : rmCode[c]? = some (.unp a b q)) : q < 32 := by
  have := List.all_eq_true.mp rmCode_qOk _ (List.mem_of_getElem? h)
  simpa [RI.qOk] using this

theorem rvSt_congr {w w' : Nat → Value} (h : ∀ k < 64, w k = w' k) :
    ∀ c, c ≤ 74 → rvSt w c = rvSt w' c := by
  intro c
  induction c with
  | zero => intro; rfl
  | succ c ih =>
    intro hc
    have hi : rmCode[c]? = some rmCode[c] :=
      List.getElem?_eq_getElem (by rw [rmCode_length]; omega)
    rw [rvSt_succ hi, rvSt_succ hi, ih (by omega)]
    generalize hI : rmCode[c] = i at hi
    cases i with
    | unp a b q =>
      have hq := rmCode_unp_lt hi
      simp only [RI.updV, h (2 * q) (by omega), h (2 * q + 1) (by omega)]
    | mx2 => rfl
    | mx3 => rfl

theorem ownV_congr {w w' : Nat → Value} (h : ∀ k < 64, w k = w' k) : ownV w = ownV w' := by
  unfold ownV
  rw [rvSt_congr h 74 (le_refl _)]

theorem cmaxW_or (w : Nat → Value) (a b : Nat) :
    cmaxW w (a ||| b) = max (cmaxW w a) (cmaxW w b) := by
  unfold cmaxW
  have : (Finset.range 64).filter (fun k => (a ||| b).testBit k) =
      (Finset.range 64).filter (fun k => a.testBit k) ∪
        (Finset.range 64).filter (fun k => b.testBit k) := by
    ext k
    simp [Nat.testBit_or, and_or_left]
  rw [this, Finset.sup_union]

theorem cmaxW_pow (w : Nat → Value) {k : Nat} (hk : k < 64) : cmaxW w (2 ^ k) = eOf (w k) := by
  unfold cmaxW
  have : (Finset.range 64).filter (fun j => (2 ^ k).testBit j) = {k} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.testBit_two_pow]
    constructor
    · rintro ⟨-, h⟩
      exact (of_decide_eq_true h).symm
    · rintro rfl
      exact ⟨hk, by simp⟩
  rw [this, Finset.sup_singleton]

/-- **On score words the tree's registers hold the values of the extended-real maxima of their
columns.** -/
theorem rv_vals {w : Nat → Value} (hw : ∀ k < 64, ScoreWord (w k)) :
    ∀ c, c ≤ 74 → ∀ r m, (rmSt c).lookup r = some m →
      (rvSt w c).lookup r = some (erealValue .f32 (cmaxW w m)) := by
  intro c
  induction c with
  | zero => intro _ r m h; simp [rmSt] at h
  | succ c ih =>
    intro hc r m h
    have hi : rmCode[c]? = some rmCode[c] :=
      List.getElem?_eq_getElem (by rw [rmCode_length]; omega)
    have hck := rm_chk c (by omega)
    unfold rmChk at hck
    rw [hi] at hck
    rw [rmSt_succ hi] at h
    rw [rvSt_succ hi]
    generalize rmCode[c] = i at hi hck h
    cases i with
    | unp a b q =>
      have hq := rmCode_unp_lt hi
      simp only [RI.upd, RI.updV, List.lookup] at h ⊢
      by_cases hb : r = b
      · subst hb
        simp only [beq_self_eq_true, Option.some.injEq] at h ⊢
        rw [← h, cmaxW_pow w (by omega), (hw _ (by omega)).eval]
      · simp only [beq_false_of_ne hb] at h ⊢
        by_cases ha : r = a
        · subst ha
          simp only [beq_self_eq_true, Option.some.injEq] at h ⊢
          rw [← h, cmaxW_pow w (by omega), (hw _ (by omega)).eval]
        · simp only [beq_false_of_ne ha] at h ⊢
          exact ih (by omega) r m h
    | mx2 d a b =>
      simp only [RI.chk, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hck
      obtain ⟨⟨⟨⟨⟨⟨hm, hsa⟩, hsb⟩, hla⟩, hlb⟩, hsub⟩, hemu⟩ := hck
      obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.mp hsa
      obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.mp hsb
      have va := ih (by omega) a ma hma
      have vb := ih (by omega) b mb hmb
      simp only [RI.upd, RI.updV, List.lookup] at h ⊢
      by_cases hd : r = d
      · subst hd
        simp only [beq_self_eq_true, Option.some.injEq] at h ⊢
        rw [← h]
        simp only [lk, hma, hmb, Option.getD_some, lkV, va, vb]
        rw [maxE_ereal2 (cmaxW_lt_top hw ma).ne (cmaxW_lt_top hw mb).ne, cmaxW_or]
        rfl
      · simp only [beq_false_of_ne hd] at h ⊢
        exact ih (by omega) r m h
    | mx3 d a b e =>
      simp only [RI.chk, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hck
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hm, hsa⟩, hsb⟩, hse⟩, hla⟩, hlb⟩, hle⟩, hsub⟩, hemu⟩ := hck
      obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.mp hsa
      obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.mp hsb
      obtain ⟨me, hme⟩ := Option.isSome_iff_exists.mp hse
      have va := ih (by omega) a ma hma
      have vb := ih (by omega) b mb hmb
      have ve := ih (by omega) e me hme
      simp only [RI.upd, RI.updV, List.lookup] at h ⊢
      by_cases hd : r = d
      · subst hd
        simp only [beq_self_eq_true, Option.some.injEq] at h ⊢
        rw [← h]
        simp only [lk, hma, hmb, hme, Option.getD_some, lkV, va, vb, ve]
        rw [maxE_ereal3 (cmaxW_lt_top hw ma).ne (cmaxW_lt_top hw mb).ne (cmaxW_lt_top hw me).ne,
          cmaxW_or, cmaxW_or]
        rfl
      · simp only [beq_false_of_ne hd] at h ⊢
        exact ih (by omega) r m h

/-- **On score words the tree has outcomes**, where every pair register is the pack of its two
words. -/
theorem rv_ok {w P : Nat → Value} (hw : ∀ k < 64, ScoreWord (w k))
    (hP : ∀ q < 32, P q = joinValue (w (2 * q)) (w (2 * q + 1))) : RvOk P w := by
  intro c hc i hi
  have hck := rm_chk c hc
  unfold rmChk at hck
  rw [hi] at hck
  cases i with
  | unp a b q =>
    have hq := rmCode_unp_lt hi
    have h0 := hw (2 * q) (by omega)
    have h1 := hw (2 * q + 1) (by omega)
    simp only [RI.okV, hP q hq]
    simp [unpackE, bytes_join h0 h1, split64_join h0 h1, h0.bytes, h1.bytes, Except.toBool]
  | mx2 d a b =>
    simp only [RI.chk, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hck
    obtain ⟨⟨⟨⟨⟨⟨hm, hsa⟩, hsb⟩, hla⟩, hlb⟩, hsub⟩, hemu⟩ := hck
    obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.mp hsa
    obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.mp hsb
    simp only [RI.okV, lkV, rv_vals hw c (by omega) a ma hma, rv_vals hw c (by omega) b mb hmb,
      Option.getD_some]
    rw [maxE_ereal2 (cmaxW_lt_top hw ma).ne (cmaxW_lt_top hw mb).ne]
    rfl
  | mx3 d a b e =>
    simp only [RI.chk, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hm, hsa⟩, hsb⟩, hse⟩, hla⟩, hlb⟩, hle⟩, hsub⟩, hemu⟩ := hck
    obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.mp hsa
    obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.mp hsb
    obtain ⟨me, hme⟩ := Option.isSome_iff_exists.mp hse
    simp only [RI.okV, lkV, rv_vals hw c (by omega) a ma hma, rv_vals hw c (by omega) b mb hmb,
      rv_vals hw c (by omega) e me hme, Option.getD_some]
    rw [maxE_ereal3 (cmaxW_lt_top hw ma).ne (cmaxW_lt_top hw mb).ne (cmaxW_lt_top hw me).ne]
    rfl

theorem rm_root_lookup : (rmSt 74).lookup (R 1059) = some (2 ^ 64 - 1) := by decide +kernel

/-- **The thread's maximum on score words** is the value of their extended-real maximum. -/
theorem ownV_eq {w : Nat → Value} (hw : ∀ k < 64, ScoreWord (w k)) :
    ownV w = erealValue .f32 (cmaxW w fullMask) := by
  unfold ownV lkV
  rw [rv_vals hw 74 (le_refl _) _ _ rm_root_lookup]
  rfl

/-! ### The stage's first half on numbers -/

/-- The score words after the stage's first half are score words. -/
theorem fin_ScOk {d : D} (hs : ∀ k < 64, ∃ x, (d.sv k).1 = .float .f32 x) :
    (D.fin L g d).ScOk := by
  intro k hk
  unfold D.fin
  split_ifs with h96 h97
  · obtain ⟨x, hx⟩ := hs k hk
    exact Or.inl ⟨x, hx⟩
  · show ScoreWord (scSv d 32 k).1
    simp only [scSv, show k / 2 < 32 by omega, ↓reduceIte]
    exact Or.inl ⟨_, rfl⟩
  · show ScoreWord (mSv L g d 32 k).1
    simp only [mSv, msk, show ¬ (32 = 1) by omega, show k / 2 < 32 by omega, decide_true,
      ↓reduceIte, mw]
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr rfl

variable {d : D}

theorem joinValue_float (x y : ℝ) :
    joinValue (.float .f32 x) (.float .f32 y) = .pair (.float .f32 x) (.float .f32 y) := rfl

theorem vf0 (a b : Value) {x : ℝ} (h : valFloat .f32 a = .ok x) :
    valFloat .f32 (splitValue 64 (.pair a b)).1 = .ok x := h

theorem vf1 (a b : Value) {x : ℝ} (h : valFloat .f32 b = .ok x) :
    valFloat .f32 (splitValue 64 (.pair a b)).2 = .ok x := h

/-- **The score's `fma` on numbers** is the pair of the exact scores. -/
theorem scE_real (hs : ∀ k < 64, ∃ x, (d.sv k).1 = .float .f32 x) {q : Nat} (hq : q < 32) :
    d.scE q = .ok (.pair (.float .f32 (d.scd (2 * q))) (.float .f32 (d.scd (2 * q + 1)))) := by
  obtain ⟨x0, hx0⟩ := hs (2 * q) (by omega)
  obtain ⟨x1, hx1⟩ := hs (2 * q + 1) (by omega)
  have hsp : d.sP q = .pair (.float .f32 x0) (.float .f32 x1) := by
    rw [D.sP, hx0, hx1]; rfl
  unfold D.scE
  rw [hsp, D.bP, invP, joinValue_float, joinValue_float,
    fma2E_fin (vf0 (.float .f32 (d.bR (2 * q))) (.float .f32 (d.bR (2 * q + 1))) (valFloat_float _))
      (vf1 (.float .f32 (d.bR (2 * q))) (.float .f32 (d.bR (2 * q + 1))) (valFloat_float _))
      (vf0 (.float .f32 (1 / d.e.sc)) (.float .f32 (1 / d.e.sc)) (valFloat_float _))
      (vf1 (.float .f32 (1 / d.e.sc)) (.float .f32 (1 / d.e.sc)) (valFloat_float _))
      (vf0 (.float .f32 x0) (.float .f32 x1) (valFloat_float _))
      (vf1 (.float .f32 x0) (.float .f32 x1) (valFloat_float _))]
  simp [D.scd, hx0, hx1, bfR]

theorem scP_real (hs : ∀ k < 64, ∃ x, (d.sv k).1 = .float .f32 x) {q : Nat} (hq : q < 32) :
    d.scP q = .pair (.float .f32 (d.scd (2 * q))) (.float .f32 (d.scd (2 * q + 1))) := by
  rw [D.scP, scE_real hs hq]
  rfl

theorem hW_pair2 (a b : Value) {k : Nat} :
    hW (.pair a b) k = if k % 2 = 0 then a else b := by
  simp [hW, splitValue]

theorem mwT_real (hs : ∀ k < 64, ∃ x, (d.sv k).1 = .float .f32 x) {k : Nat} (hk : k < 64) :
    mwT L g d k = mw d.e (g % L.block) d.n d.scd k := by
  unfold mwT mw selV
  rw [scP_real hs (by omega), hW_pair2]
  have : (if k % 2 = 0 then Value.float .f32 (d.scd (2 * (k / 2)))
      else .float .f32 (d.scd (2 * (k / 2) + 1))) = .float .f32 (d.scd k) := by
    split_ifs with h
    · rw [show 2 * (k / 2) = k by omega]
    · rw [show 2 * (k / 2) + 1 = k by omega]
  rw [this]

theorem mw_score (e : Ent) (T n : Nat) (sc : Nat → ℝ) (k : Nat) : ScoreWord (mw e T n sc k) := by
  unfold mw
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr rfl

theorem scoredT_sP (d : D) {m q : Nat} (hq : q < m) : (d.scoredT m).sP q = d.scP q := by
  show joinValue (scSvT d m (2 * q)).1 (scSvT d m (2 * q + 1)).1 = d.scP q
  unfold scSvT
  rw [if_pos (by omega : 2 * q / 2 < m), if_pos (by omega : (2 * q + 1) / 2 < m),
    show 2 * q / 2 = q by omega, show (2 * q + 1) / 2 = q by omega]
  have e0 : slW (d.scP q) (2 * q) = slW (d.scP q) 0 := by simp [slW]
  have e1 : slW (d.scP q) (2 * q + 1) = slW (d.scP q) 1 := by simp [slW]
  rw [e0, e1]
  exact joinValue_slices (scP_bytes d q)

theorem maskedT_sP (d : D) {q : Nat} (hq : q < 32) :
    (D.maskedT L g d 32).sP q = joinValue (mwT L g d (2 * q)) (mwT L g d (2 * q + 1)) := by
  show joinValue (mSvT L g d 32 (2 * q)).1 (mSvT L g d 32 (2 * q + 1)).1 = _
  have hm : ∀ j, j / 2 < 32 → msk 32 (j / 2) = true := fun j hj => by simp [msk, hj]
  unfold mSvT
  rw [if_pos (hm _ (by omega)), if_pos (hm _ (by omega))]

theorem colW_of_sP {d : D} {k : Nat} {a b : Value}
    (h : d.sP (k / 2) = joinValue a b) (ha : ScoreWord a) (hb : ScoreWord b) :
    colW d k = if k % 2 = 0 then a else b := by
  unfold colW hW
  rw [h, split64_join ha hb]

/-- **The words at the shuffle are the words of `D.fin`** where the S words are numbers. -/
theorem colW_s1 (hs : ∀ k < 64, ∃ x, (d.sv k).1 = .float .f32 x) {k : Nat} (hk : k < 64) :
    colW (D.s1 L g d) k = ((D.fin L g d).sv k).1 := by
  have hk2 : (if k % 2 = 0 then 2 * (k / 2) else 2 * (k / 2) + 1) = k := by
    split_ifs <;> omega
  unfold D.s1 D.fin
  by_cases h96 : pr96 d.e d.n = true
  · simp only [h96, ↓reduceIte]
    obtain ⟨x0, hx0⟩ := hs (2 * (k / 2)) (by omega)
    obtain ⟨x1, hx1⟩ := hs (2 * (k / 2) + 1) (by omega)
    rw [colW_of_sP (a := (d.sv (2 * (k / 2))).1) (b := (d.sv (2 * (k / 2) + 1)).1) rfl
      (by rw [hx0]; exact Or.inl ⟨_, rfl⟩) (by rw [hx1]; exact Or.inl ⟨_, rfl⟩)]
    split_ifs with h
    · rw [show 2 * (k / 2) = k by omega]
    · rw [show 2 * (k / 2) + 1 = k by omega]
  simp only [h96, Bool.false_eq_true, ↓reduceIte]
  by_cases h97 : pr97 d.e d.n = true
  · simp only [h97, ↓reduceIte]
    rw [colW_of_sP (a := .float .f32 (d.scd (2 * (k / 2))))
      (b := .float .f32 (d.scd (2 * (k / 2) + 1)))
      (by rw [scoredT_sP d (by omega), scP_real hs (by omega)]; rfl)
      (Or.inl ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩)]
    show _ = (scSv d 32 k).1
    simp only [scSv, show k / 2 < 32 by omega, ↓reduceIte]
    split_ifs with h
    · rw [show 2 * (k / 2) = k by omega]
    · rw [show 2 * (k / 2) + 1 = k by omega]
  · simp only [h97, Bool.false_eq_true, ↓reduceIte]
    rw [colW_of_sP (a := mw d.e (g % L.block) d.n d.scd (2 * (k / 2)))
      (b := mw d.e (g % L.block) d.n d.scd (2 * (k / 2) + 1))
      (by rw [maskedT_sP d (by omega), mwT_real hs (by omega), mwT_real hs (by omega)])
      (mw_score _ _ _ _ _) (mw_score _ _ _ _ _)]
    show _ = (mSv L g d 32 k).1
    have hm : msk 32 (k / 2) = true := by simp [msk, show k / 2 < 32 by omega]
    simp only [mSv, hm, ↓reduceIte]
    split_ifs with h
    · rw [show 2 * (k / 2) = k by omega]
    · rw [show 2 * (k / 2) + 1 = k by omega]

/-- The words of `D.fin` at the columns from 64 on are the S words. -/
theorem fin_sv_high (d : D) {k : Nat} (hk : 64 ≤ k) : (D.fin L g d).sv k = d.sv k := by
  unfold D.fin
  split_ifs
  · rfl
  · simp [D.scored, scSv, show ¬ (k / 2 < 32) by omega]
  · simp [D.masked, mSv, msk, scSv, show ¬ (k / 2 < 32) by omega]

/-- **The machine's words at the shuffle are those of `D.fin`** where the S words are numbers. -/
theorem finT_eq (hs : ∀ k < 64, ∃ x, (d.sv k).1 = .float .f32 x) :
    D.finT L g d = (D.fin L g d).sv := by
  funext k
  unfold D.finT
  by_cases hk : k < 64
  · simp only [hk, ↓reduceIte]
    have e := colW_s1 (L := L) (g := g) hs hk
    rw [dif_pos (by rw [e]; exact ((D.fin L g d).sv k).2)]
    exact Subtype.ext e
  · simp only [hk, ↓reduceIte]
    exact (fin_sv_high d (by omega)).symm

/-- **No instruction of the stage's first half faults** where the S words are numbers. -/
theorem s1Ok_real (hs : ∀ k < 64, ∃ x, (d.sv k).1 = .float .f32 x) : D.s1Ok L g d := by
  have hsc := fin_ScOk (L := L) (g := g) hs
  have hw : ∀ k < 64, ScoreWord (colW (D.s1 L g d) k) := fun k hk => by
    rw [colW_s1 hs hk]; exact hsc k hk
  refine ⟨fun _ q hq => by rw [scE_real hs hq]; rfl, rv_ok hw fun q hq => ?_⟩
  rw [colW_s1 hs (by omega), colW_s1 hs (by omega)]
  unfold D.s1 D.fin
  by_cases h96 : pr96 d.e d.n = true
  · simp only [h96, ↓reduceIte]
    rfl
  simp only [h96, Bool.false_eq_true, ↓reduceIte]
  by_cases h97 : pr97 d.e d.n = true
  · simp only [h97, ↓reduceIte]
    rw [scoredT_sP d hq, scP_real hs hq]
    show _ = joinValue (scSv d 32 (2 * q)).1 (scSv d 32 (2 * q + 1)).1
    simp only [scSv, show 2 * q / 2 < 32 by omega, show (2 * q + 1) / 2 < 32 by omega,
      ↓reduceIte]
    rfl
  · simp only [h97, Bool.false_eq_true, ↓reduceIte]
    rw [maskedT_sP d hq, mwT_real hs (by omega), mwT_real hs (by omega)]
    show _ = joinValue (mSv L g d 32 (2 * q)).1 (mSv L g d 32 (2 * q + 1)).1
    have hm : ∀ j, j / 2 < 32 → msk 32 (j / 2) = true := fun j hj => by simp [msk, hj]
    simp only [mSv, hm (2 * q) (by omega), hm (2 * q + 1) (by omega), ↓reduceIte]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
