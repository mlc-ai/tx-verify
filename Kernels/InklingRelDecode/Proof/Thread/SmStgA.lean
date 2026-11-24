-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmFlt
public import Kernels.InklingRelDecode.Proof.Thread.SmStg
public import Kernels.InklingRelDecode.Proof.Thread.SmTotC

@[expose] public section

/-! # The new maximum, the decision and `alpha` in the registers (pcs 1839-1848)

After the shuffle of the row maximum (pc 1838, `%r1060` receives the maximum of the lane
`^ 16`), ten instructions compute `m_new`, `m_safe`, `alpha_log2`, the lazy-rescale decision,
`alpha`, `m_use` and `m_use * (-scale_log2)`. The facts after each are the live registers valued
by an overlay of the registers written so far in front of the table of the state at the shuffle
(`valueEx`, `Seg.set1`); the values are those `D.afterMax` records:

| pc | register | value |
| --- | --- | --- |
| 1839 | `%r1061` | `m_new` (`D.mnE`) |
| 1840 | `%p167` | `m_new = -inf` |
| 1841 | `%r1062` | `m_safe` (the pattern `0` for `-inf`) |
| 1842 | `%r1063` | `m - m_safe` |
| 1843 | `%r809` | `alpha_log2` (`D.aE`) |
| 1844 | `%p168` | `alpha_log2 >= -8` (`D.keepB`) |
| 1845 | `%r808` | `2 ^ alpha_log2` |
| 1846 | `%r46` | `alpha` (`D.alV`) |
| 1847 | `%r1064` | `m_use` |
| 1848 | `%r1065` | `m_use * (-scale_log2)` | -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Softmax
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### The table's registers of the stage -/

theorem valueOf_r1061 (d : D) : valueOf L g d 1520 = ownV fun k => (d.stg.fsv k).1 := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

/-- On score words the thread's maximum is the value of its extended-real maximum. -/
theorem valueOf_r1061E {d : D} (hw : ∀ k < 64, ScoreWord (d.stg.fsv k).1) :
    valueOf L g d 1520 = erealValue .f32 d.ownE := by
  rw [valueOf_r1061, ownV_eq hw]
  rfl

theorem valueOf_r37 (d : D) : valueOf L g d 498 = .float .f32 (slOf d.e) := by
  sm_vals
  rfl

theorem valueOf_r38 (d : D) : valueOf L g d 499 = .float .f32 (-(slOf d.e)) := by
  sm_vals
  rfl

theorem sl_pos {d : D} (hok : d.e.Ok) : 0 < slOf d.e := by
  have h1 := hok.scalePos
  have h2 : 0 < log2eF32 := by unfold log2eF32; norm_num
  exact mul_pos h1 h2

/-! ### The numbers -/

/-- `m_safe` as an extended real (`0` for `m_new = -inf`). -/
def mSE (E : EReal) : EReal := if E = ⊥ then 0 else E

/-- `%r1062`: the pattern `0` for `m_new = -inf`, else `m_new`. -/
def m1064V (E : EReal) : Value := if E = ⊥ then b32 0 else erealValue .f32 E

/-- `m - m_safe` as the register computes it. -/
def D.dE (d : D) (rE : EReal) : EReal := d.mE + -(mSE (d.mnE rE))

/-- `alpha_log2 = scale_log2 * (m - m_safe)` as the register computes it (`%r809`). -/
def D.aE (d : D) (rE : EReal) : EReal := (slOf d.e : EReal) * d.dE rE

/-- `%r1064`: `m` where the rescale is lazy, else `%r1062`. -/
def D.uV (d : D) (rE : EReal) : Value :=
  if Softmax.Keep (d.aE rE) then d.m else m1064V (d.mnE rE)

theorem readEReal_m1064 {E : EReal} (h : E ≠ ⊤) :
    readEReal .f32 (m1064V E) = some (.ok (mSE E)) := by
  unfold m1064V mSE
  split_ifs with hb
  · rfl
  · exact readEReal_erealValue h

theorem mSE_ne_bot {E : EReal} : mSE E ≠ ⊥ := by
  unfold mSE; split_ifs with h
  · simp
  · exact h

theorem mSE_eq_cast {E : EReal} (h : E ≠ ⊤) : mSE E = ((Softmax.mSafe E : ℝ) : EReal) := by
  unfold mSE Softmax.mSafe
  split_ifs with hb
  · simp
  · exact (EReal.coe_toReal h hb).symm

/-- What the stage needs of the state at the shuffle: the running maximum, the received maximum
and the 64 score words are score words, and the entry numbers are in range. -/
structure StA (d : D) (recv : Value) : Prop where
  m : ScoreWord d.m
  r : ScoreWord recv
  w : ∀ k < 64, ScoreWord (d.stg.fsv k).1
  ok : d.e.Ok

theorem StA.E_ne_top {d : D} {recv : Value} (h : StA d recv) : d.mnE (eOf recv) ≠ ⊤ := by
  unfold D.mnE
  refine lt_top_iff_ne_top.mp (max_lt (max_lt (lt_top_iff_ne_top.mpr h.m.ne_top) ?_)
    (lt_top_iff_ne_top.mpr h.r.ne_top))
  exact cmaxW_lt_top h.w _

abbrev xa1 (d : D) (recv : Value) : List (Nat × Value) :=
  (1522, erealValue .f32 (d.mnE (eOf recv))) :: xa0 recv

theorem live_xa : ∀ k < 10, subX (Flow.live (1840 + k)) (Flow.live (1839 + k))
    [[1522, 167, 1523, 1524, 1270, 168, 1269, 507, 1525, 1526].getD k 0] = true := by
  decide +kernel

theorem emu_xa : ∀ k < 10, Assumptions.emuSites.contains (1839 + k) = false := by decide +kernel

theorem seg_a1 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1839
      (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) 1840
      (factsFrom (Flow.live 1840) (valueEx (valueOf L g d) (xa1 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1839 rfl (fun t h => ?_)
    (subX_sound (live_xa 0 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 0 (by omega)
  have F := h.2.2.2.2
  have ra : t.regs 1914 = some d.m := by
    have := holds_mem F (mem_factsFrom (val := valueEx (valueOf L g d) (xa0 recv))
      (show 1914 ∈ Flow.live 1839 by decide +kernel))
    simpa [valueEx, List.lookup, valueOf_m] using this
  have rb : t.regs 1520 = some (erealValue .f32 d.ownE) := by
    have := holds_mem F (mem_factsFrom (val := valueEx (valueOf L g d) (xa0 recv))
      (show 1520 ∈ Flow.live 1839 by decide +kernel))
    simpa [valueEx, List.lookup, valueOf_r1061E hA.w] using this
  have rc : t.regs 1521 = some recv := by
    have := holds_mem F (mem_factsFrom (val := valueEx (valueOf L g d) (xa0 recv))
      (show 1521 ∈ Flow.live 1839 by decide +kernel))
    simpa [valueEx, List.lookup] using this
  have hown : d.ownE ≠ ⊤ := lt_top_iff_ne_top.mp (cmaxW_lt_top hA.w _)
  have hp : t.pc = 1839 := h.1
  have hmax : maxE [d.m, erealValue .f32 d.ownE, recv] =
      .ok (erealValue .f32 (d.mnE (eOf recv))) := by
    have := maxE_ereal3 hA.m.ne_top hown hA.r.ne_top
    rw [hA.m.eval, hA.r.eval] at this
    exact this
  show execLocalA asms L g t (maxOp 1522 [1914, 1520, 1521]) = _
  rw [exec_maxE3 (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega)) ra rb rc, hmax]
  rfl

/-- A register of the overlay's facts holds its overlay value. -/
theorem reg_of {t : TState} {live : List Nat} {B : Nat → Value} {ex : List (Nat × Value)}
    (F : Holds t.regs (factsFrom live (valueEx B ex))) {r : Nat} (hr : r ∈ live) {v : Value}
    (hv : valueEx B ex r = v) : t.regs r = some v := by
  have := holds_mem F (mem_factsFrom (val := valueEx B ex) hr)
  rwa [hv] at this

theorem readEReal_m8 : readEReal .f32 (.bits 32 (BitVec.ofNat 64 3238002688)) =
    some (.ok (((-8 : ℝ)) : EReal)) := by
  have h : f32Value 3238002688 = some (-8 : ℚ) := by decide +kernel
  have := readEReal_of_valFloat (valFloat_b32 (b := 3238002688) (by norm_num) h)
  simpa [b32] using this

theorem readEReal_inf : readEReal .f32 (.bits 32 (BitVec.ofNat 64 4286578688)) =
    some (.ok ⊥) := by
  have := readEReal_erealValue (x := ⊥) bot_ne_top
  rwa [erealValue_bot'] at this

abbrev xa2 (d : D) (recv : Value) : List (Nat × Value) :=
  (167, Value.pred (decide (d.mnE (eOf recv) = ⊥))) :: xa1 d recv
abbrev xa3 (d : D) (recv : Value) : List (Nat × Value) :=
  (1523, m1064V (d.mnE (eOf recv))) :: xa2 d recv
abbrev xa4 (d : D) (recv : Value) : List (Nat × Value) :=
  (1524, erealValue .f32 (d.dE (eOf recv))) :: xa3 d recv
abbrev xa5 (d : D) (recv : Value) : List (Nat × Value) :=
  (1270, erealValue .f32 (d.aE (eOf recv))) :: xa4 d recv
abbrev xa6 (d : D) (recv : Value) : List (Nat × Value) :=
  (168, Value.pred (decide (Softmax.Keep (d.aE (eOf recv))))) :: xa5 d recv
abbrev xa7 (d : D) (recv : Value) : List (Nat × Value) :=
  (1269, Value.float .f32 (Softmax.pow2 (d.aE (eOf recv)))) :: xa6 d recv
abbrev xa8 (d : D) (recv : Value) : List (Nat × Value) :=
  (507, if Softmax.Keep (d.aE (eOf recv)) then b32 1065353216
    else Value.float .f32 (Softmax.pow2 (d.aE (eOf recv)))) :: xa7 d recv
abbrev xa9 (d : D) (recv : Value) : List (Nat × Value) :=
  (1525, d.uV (eOf recv)) :: xa8 d recv

theorem StA.dE_ne_top {d : D} {recv : Value} (h : StA d recv) : d.dE (eOf recv) ≠ ⊤ := by
  unfold D.dE
  refine lt_top_iff_ne_top.mp (EReal.add_lt_top h.m.ne_top ?_)
  intro hb
  exact mSE_ne_bot (EReal.neg_eq_top_iff.mp hb)

theorem StA.aE_ne_top {d : D} {recv : Value} (h : StA d recv) : d.aE (eOf recv) ≠ ⊤ := by
  unfold D.aE
  have hd := h.dE_ne_top
  have hs : (0 : ℝ) < slOf d.e := sl_pos h.ok
  induction hdE : d.dE (eOf recv) using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hs]; exact bot_ne_top
  | coe y => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd hdE hd

theorem StA.aE_eq {d : D} {recv : Value} (h : StA d recv) :
    d.aE (eOf recv) = d.aLog (eOf recv) := by
  unfold D.aE D.aLog Softmax.alphaLog2 D.dE
  rw [mSE_eq_cast h.E_ne_top, ← sub_eq_add_neg, mul_comm]

/-- The stage's registers in each state, as the instructions need them. -/
theorem seg_a2 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1840
      (factsFrom (Flow.live 1840) (valueEx (valueOf L g d) (xa1 d recv))) 1841
      (factsFrom (Flow.live 1841) (valueEx (valueOf L g d) (xa2 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1840 rfl (fun t h => ?_)
    (subX_sound (live_xa 1 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 1 (by omega)
  have hp : t.pc = 1840 := h.1
  have ra : t.regs 1522 = some (erealValue .f32 (d.mnE (eOf recv))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (setpOp .eq 167 1522 4286578688) = _
  rw [exec_setpEInf (idealAtSc (L := L) (g := g) (by decide) hE) ra
    (readEReal_erealValue hA.E_ne_top) readEReal_inf (by decide)]
  simp [erealCompare]

theorem seg_a3 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1841
      (factsFrom (Flow.live 1841) (valueEx (valueOf L g d) (xa2 d recv))) 1842
      (factsFrom (Flow.live 1842) (valueEx (valueOf L g d) (xa3 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1841 rfl (fun t h => ?_)
    (subX_sound (live_xa 2 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 2 (by omega)
  have hp : t.pc = 1841 := h.1
  have rp : t.regs 167 = some (.pred (decide (d.mnE (eOf recv) = ⊥))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  have rb : t.regs 1522 = some (erealValue .f32 (d.mnE (eOf recv))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (selpOp 1523 (.f32imm 0) (.reg 1522) 167) = _
  rw [exec_selp (segFree hE) rp readValue_imm (readValue_reg rb) rfl
    (erealValue_f32_bytes _)]
  simp only [m1064V, decide_eq_true_eq]
  split_ifs <;> rfl

theorem seg_a4 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1842
      (factsFrom (Flow.live 1842) (valueEx (valueOf L g d) (xa3 d recv))) 1843
      (factsFrom (Flow.live 1843) (valueEx (valueOf L g d) (xa4 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1842 rfl (fun t h => ?_)
    (subX_sound (live_xa 3 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 3 (by omega)
  have hp : t.pc = 1842 := h.1
  have ra : t.regs 1914 = some d.m :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_m])
  have rb : t.regs 1523 = some (m1064V (d.mnE (eOf recv))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (subOp 1524 1914 1523) = _
  have hadd : addEReal (eOf d.m) (-(mSE (d.mnE (eOf recv)))) =
      some (d.dE (eOf recv)) := by
    unfold addEReal
    rw [if_neg]
    · rfl
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact hA.m.ne_top h1
      · exact mSE_ne_bot (EReal.neg_eq_top_iff.mp h2)
  rw [exec_subE (idealAtSc (L := L) (g := g) (by decide) hE) ra rb (readEReal_sw hA.m)
    (readEReal_m1064 hA.E_ne_top) hadd]

theorem seg_a5 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1843
      (factsFrom (Flow.live 1843) (valueEx (valueOf L g d) (xa4 d recv))) 1844
      (factsFrom (Flow.live 1844) (valueEx (valueOf L g d) (xa5 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1843 rfl (fun t h => ?_)
    (subX_sound (live_xa 4 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 4 (by omega)
  have hp : t.pc = 1843 := h.1
  have ra : t.regs 498 = some (.float .f32 (slOf d.e)) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_r37])
  have rb : t.regs 1524 = some (erealValue .f32 (d.dE (eOf recv))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (mulOp 1270 498 1524) = _
  have hs : (0 : ℝ) < slOf d.e := sl_pos hA.ok
  have hmul : mulEReal (slOf d.e : EReal) (d.dE (eOf recv)) = some (d.aE (eOf recv)) := by
    unfold mulEReal
    rw [if_neg]
    · rfl
    · rintro (⟨h1, -⟩ | ⟨-, h2 | h2⟩)
      · exact absurd h1 (by exact_mod_cast hs.ne')
      · exact EReal.coe_ne_top _ h2
      · exact EReal.coe_ne_bot _ h2
  rw [exec_mulE (idealAtSc (L := L) (g := g) (by decide) hE) ra rb
    (readEReal_of_valFloat (valFloat_float _)) (readEReal_erealValue hA.dE_ne_top) hmul]

theorem seg_a6 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1844
      (factsFrom (Flow.live 1844) (valueEx (valueOf L g d) (xa5 d recv))) 1845
      (factsFrom (Flow.live 1845) (valueEx (valueOf L g d) (xa6 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1844 rfl (fun t h => ?_)
    (subX_sound (live_xa 5 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 5 (by omega)
  have hp : t.pc = 1844 := h.1
  have ra : t.regs 1270 = some (erealValue .f32 (d.aE (eOf recv))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (setpOp .ge 168 1270 3238002688) = _
  rw [exec_setpEI (idealAtSc (L := L) (g := g) (by decide) hE) ra
    (readEReal_erealValue hA.aE_ne_top) readEReal_m8 (by decide)]
  have : erealCompare .ge (d.aE (eOf recv)) (((-8 : ℝ)) : EReal) =
      decide (Softmax.Keep (d.aE (eOf recv))) := by
    unfold erealCompare Softmax.Keep
    exact decide_eq_decide.mpr Iff.rfl
  rw [this]

theorem seg_a7 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1845
      (factsFrom (Flow.live 1845) (valueEx (valueOf L g d) (xa6 d recv))) 1846
      (factsFrom (Flow.live 1846) (valueEx (valueOf L g d) (xa7 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1845 rfl (fun t h => ?_)
    (subX_sound (live_xa 6 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 6 (by omega)
  have hp : t.pc = 1845 := h.1
  have ra : t.regs 1270 = some (erealValue .f32 (d.aE (eOf recv))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (ex2Op 1269 1270) = _
  rw [exec_ex2V hA.aE_ne_top hE (by omega) (by omega) (by omega) ra]

theorem seg_a8 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1846
      (factsFrom (Flow.live 1846) (valueEx (valueOf L g d) (xa7 d recv))) 1847
      (factsFrom (Flow.live 1847) (valueEx (valueOf L g d) (xa8 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1846 rfl (fun t h => ?_)
    (subX_sound (live_xa 7 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 7 (by omega)
  have hp : t.pc = 1846 := h.1
  have rp : t.regs 168 = some (.pred (decide (Softmax.Keep (d.aE (eOf recv))))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  have rb : t.regs 1269 = some (.float .f32 (Softmax.pow2 (d.aE (eOf recv)))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (selpOp 507 (.f32imm 1065353216) (.reg 1269) 168) = _
  rw [exec_selp (segFree hE) rp readValue_imm (readValue_reg rb) rfl rfl]
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

theorem seg_a9 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1847
      (factsFrom (Flow.live 1847) (valueEx (valueOf L g d) (xa8 d recv))) 1848
      (factsFrom (Flow.live 1848) (valueEx (valueOf L g d) (xa9 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1847 rfl (fun t h => ?_)
    (subX_sound (live_xa 8 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 8 (by omega)
  have hp : t.pc = 1847 := h.1
  have rp : t.regs 168 = some (.pred (decide (Softmax.Keep (d.aE (eOf recv))))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  have ra : t.regs 1914 = some d.m :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_m])
  have rb : t.regs 1523 = some (m1064V (d.mnE (eOf recv))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (selpOp 1525 (.reg 1914) (.reg 1523) 168) = _
  have b1 : (m1064V (d.mnE (eOf recv))).bytes = 4 := by
    unfold m1064V; split_ifs
    · rfl
    · exact erealValue_f32_bytes _
  rw [exec_selp (segFree hE) rp (readValue_reg ra) (readValue_reg rb) hA.m.bytes b1]
  simp only [D.uV, decide_eq_true_eq]

abbrev xa10 (d : D) (recv : Value) : List (Nat × Value) :=
  (1526, Value.float .f32 (d.mUse (eOf recv) * -(slOf d.e))) :: xa9 d recv

/-- Where the rescale is lazy, the running maximum is a number. -/
theorem StA.keep_m_ne_bot {d : D} {recv : Value} (h : StA d recv)
    (hk : Softmax.Keep (d.aLog (eOf recv))) : d.mE ≠ ⊥ := by
  intro hb
  apply Softmax.not_keep_bot
  have : d.aLog (eOf recv) = ⊥ := by
    unfold D.aLog Softmax.alphaLog2
    rw [hb]
    have hs : (0 : ℝ) < slOf d.e := sl_pos h.ok
    rw [EReal.bot_sub, EReal.bot_mul_coe_of_pos hs]
  rwa [this] at hk

theorem StA.read_uV {d : D} {recv : Value} (h : StA d recv) :
    readEReal .f32 (d.uV (eOf recv)) = some (.ok ((d.mUse (eOf recv) : ℝ) : EReal)) := by
  unfold D.uV D.mUse
  rw [h.aE_eq]
  split_ifs with hk
  · rw [readEReal_sw h.m]
    have h1 := h.keep_m_ne_bot hk
    have h2 : d.mE ≠ ⊤ := h.m.ne_top
    simp only [D.mE] at h1 h2 ⊢
    rw [EReal.coe_toReal h2 h1]
  · rw [readEReal_m1064 h.E_ne_top, mSE_eq_cast h.E_ne_top]

theorem seg_a10 {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 1 1848
      (factsFrom (Flow.live 1848) (valueEx (valueOf L g d) (xa9 d recv))) 1849
      (factsFrom (Flow.live 1849) (valueEx (valueOf L g d) (xa10 d recv))) := by
  refine Seg.set1 (K := kernel) Flow.code_1848 rfl (fun t h => ?_)
    (subX_sound (live_xa 9 (by omega)))
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_xa 9 (by omega)
  have hp : t.pc = 1848 := h.1
  have ra : t.regs 1525 = some (d.uV (eOf recv)) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  have rb : t.regs 499 = some (.float .f32 (-(slOf d.e))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_r38])
  show execLocalA asms L g t (mulOp 1526 1525 499) = _
  rw [exec_mulE (idealAtSc (L := L) (g := g) (by decide) hE) ra rb hA.read_uV
    (readEReal_of_valFloat (valFloat_float _)) (mulEReal_coe _ _), erealValue_coe]

/-- **The ten instructions** (pcs 1839 to 1848). -/
theorem seg_a (hA : StA d recv) :
    Seg kernel asms L g 10 1839
      (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) 1849
      (factsFrom (Flow.live 1849) (valueEx (valueOf L g d) (xa10 d recv))) :=
  Seg.of_len ((((((((((seg_a1 hA).comp (seg_a2 hA)).comp (seg_a3 hA)).comp (seg_a4 hA)).comp
    (seg_a5 hA)).comp (seg_a6 hA)).comp (seg_a7 hA)).comp (seg_a8 hA)).comp (seg_a9 hA)).comp
    (seg_a10 hA)) rfl

/-! ### The 64 fused multiply-adds (pcs 1849 to 1912)

`%r(827 + 2 j) = fma(word j, scale_log2, m_use * (-scale_log2))`: the exponent of column `j`. -/

/-- The exponent of column `k`: `s * scale_log2 + m_use * (-scale_log2)` in the extended reals
(`-inf` for a masked column). -/
def D.xE (d : D) (rE : EReal) (k : Nat) : EReal :=
  eOf (d.stg.fsv k).1 * (slOf d.e : EReal) + ((d.mUse rE * -(slOf d.e) : ℝ) : EReal)

/-- The overlay after `j` fused multiply-adds. -/
def fx (d : D) (rE : EReal) : Nat → List (Nat × Value)
  | 0 => []
  | j + 1 => (1288 + 2 * j, erealValue .f32 (d.xE rE j)) :: fx d rE j

/-- The instruction at `pc` is `fma.rn.f32 d, a, b, c`. -/
def fmaAt (pc d a b c : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .float f⟩ =>
    f == { op := .fma, ty := ty1 .f32, rnd := some .rn, dsts := [some d],
           srcs := [.reg a, .reg b, .reg c] }
  | _ => false

theorem fmaAt_spec {pc d a b c : Nat} (h : fmaAt pc d a b c = true) :
    kernel.code[pc]? = some ⟨none, fmaOp d a b c⟩ := by
  unfold fmaAt at h
  split at h
  · rename_i f hc
    rw [hc, fmaOp, beq_iff_eq.mp h]
  · cases h

theorem fmaX_code : ∀ j < 64, fmaAt (1849 + j) (1288 + 2 * j) (colReg j) 498 1526 = true := by
  decide +kernel

theorem emu_fmaX : ∀ j < 64, Assumptions.emuSites.contains (1849 + j) = false := by
  decide +kernel

theorem live_fmaX : ∀ j < 64, colReg j ∈ Flow.live (1849 + j) ∧ 498 ∈ Flow.live (1849 + j) ∧
    1526 ∈ Flow.live (1849 + j) ∧
    subX (Flow.live (1849 + j + 1)) (Flow.live (1849 + j)) [1288 + 2 * j] = true := by
  decide +kernel

theorem valueEx_fx_off (d : D) (rE : EReal) (B : Nat → Value) (ex : List (Nat × Value)) {r : Nat}
    (j : Nat) (h : ∀ k < j, r ≠ 1288 + 2 * k) : valueEx B (fx d rE j ++ ex) r = valueEx B ex r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [fx, List.cons_append, valueEx_cons_ne _ _ (h j (by omega))]
    exact ih fun k hk => h k (by omega)

theorem valueEx_fx_in (d : D) (rE : EReal) (B : Nat → Value) (ex : List (Nat × Value))
    {j k : Nat} (hk : k < j) : valueEx B (fx d rE j ++ ex) (1288 + 2 * k) =
      erealValue .f32 (d.xE rE k) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [fx, List.cons_append]
    by_cases h : k = j
    · subst h; exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

theorem colReg_nodup : ((List.range 64).map colReg).Nodup := by decide +kernel

theorem lookup_Xt_off (d : D) {r : Nat} (hr : 1415 ≤ r ∧ r < 1499) :
    (valuesXt d).lookup r = none := by
  refine lookup_none_of_not_mem _ (fun hm => ?_)
  simp only [valuesXt, List.map_append, List.map_map, List.mem_append, List.mem_map,
    List.mem_range, Function.comp_apply] at hm
  omega

theorem valueOf_word (d : D) {j : Nat} (hj : j < 64) :
    valueOf L g d (colReg j) = (d.stg.fsv j).1 := by
  have hr := colReg_range j hj
  rw [valueOf_X d (by unfold XKey; omega)]
  have hxs : (valuesXs d.stg.fsv d.stg.ow d.stg.al).lookup (colReg j) =
      some (d.stg.fsv j).1 := by
    unfold valuesXs
    rw [lookup_append', lookup_map_get (f := colReg) (v := fun k => (d.stg.fsv k).1)
      (List.range 64) colReg_nodup (List.mem_range.mpr hj)]
    rfl
  have b : ∀ k, k ∈ [172, 506, 168, 507, 1522, 1531, 1544, 1520, 1529, 1536, 1538, 1540, 1534,
      1542] → (colReg j == k) = false := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp <;> omega
  simp only [valuesX, lookup_append', List.lookup, lookup_Xt_off d hr, hxs]
  rw [b 172 (by simp), b 506 (by simp), b 168 (by simp), b 507 (by simp), b 1522 (by simp),
    b 1531 (by simp), b 1544 (by simp), b 1520 (by simp), b 1529 (by simp), b 1536 (by simp),
    b 1538 (by simp), b 1540 (by simp), b 1534 (by simp), b 1542 (by simp)]
  rfl

theorem valueEx_xa10_off (d : D) (recv : Value) (B : Nat → Value) {r : Nat}
    (h : r ≠ 1521 ∧ r ≠ 1522 ∧ r ≠ 167 ∧ r ≠ 1523 ∧ r ≠ 1524 ∧ r ≠ 1270 ∧ r ≠ 168 ∧ r ≠ 1269 ∧
      r ≠ 507 ∧ r ≠ 1525 ∧ r ≠ 1526) : valueEx B (xa10 d recv) r = B r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp only [xa10, xa9, xa8, xa7, xa6, xa5, xa4, xa3, xa2, xa1, xa0]
  rw [valueEx_cons_ne _ _ h11, valueEx_cons_ne _ _ h10, valueEx_cons_ne _ _ h9,
    valueEx_cons_ne _ _ h8, valueEx_cons_ne _ _ h7, valueEx_cons_ne _ _ h6,
    valueEx_cons_ne _ _ h5, valueEx_cons_ne _ _ h4, valueEx_cons_ne _ _ h3,
    valueEx_cons_ne _ _ h2, valueEx_cons_ne _ _ h1, valueEx_nil]

theorem StA.xE_ne_top {d : D} {recv : Value} (h : StA d recv) {k : Nat} (hk : k < 64) :
    d.xE (eOf recv) k ≠ ⊤ := by
  unfold D.xE
  have hs : (0 : ℝ) < slOf d.e := sl_pos h.ok
  have hw := (h.w k hk).ne_top
  refine lt_top_iff_ne_top.mp (EReal.add_lt_top ?_ (EReal.coe_ne_top _))
  induction hx : eOf (d.stg.fsv k).1 using EReal.rec with
  | bot => rw [EReal.bot_mul_coe_of_pos hs]; exact bot_ne_top
  | coe y => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd hx hw

theorem seg_fmaX1 {d : D} {recv : Value} (hA : StA d recv) {j : Nat} (hj : j < 64) :
    Seg kernel asms L g 1 (1849 + j)
      (factsFrom (Flow.live (1849 + j))
        (valueEx (valueOf L g d) (fx d (eOf recv) j ++ xa10 d recv)))
      (1849 + j + 1)
      (factsFrom (Flow.live (1849 + j + 1))
        (valueEx (valueOf L g d) (fx d (eOf recv) (j + 1) ++ xa10 d recv))) := by
  obtain ⟨la, lb, lc, ld⟩ := live_fmaX j hj
  have hr := colReg_range j hj
  refine Seg.set1 (K := kernel) (fmaAt_spec (fmaX_code j hj)) rfl (fun t h => ?_) (subX_sound ld)
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_fmaX j hj
  have hp : t.pc = 1849 + j := h.1
  have F := h.2.2.2.2
  have hfx : ∀ k < j, colReg j ≠ 1288 + 2 * k := fun k hk => by omega
  have ra : t.regs (colReg j) = some (d.stg.fsv j).1 :=
    reg_of F la (by
      rw [valueEx_fx_off d (eOf recv) _ _ j hfx,
        valueEx_xa10_off d recv _ (by omega), valueOf_word d hj])
  have rb : t.regs 498 = some (.float .f32 (slOf d.e)) :=
    reg_of F lb (by
      rw [valueEx_fx_off d (eOf recv) _ _ j (fun k hk => by omega),
        valueEx_xa10_off d recv _ (by omega), valueOf_r37])
  have rc : t.regs 1526 = some (.float .f32 (d.mUse (eOf recv) * -(slOf d.e))) :=
    reg_of F lc (by
      rw [valueEx_fx_off d (eOf recv) _ _ j (fun k hk => by omega)]
      simp [valueEx, List.lookup])
  show execLocalA asms L g t (fmaOp (1288 + 2 * j) (colReg j) 498 1526) = _
  have hs : (0 : ℝ) < slOf d.e := sl_pos hA.ok
  have hfma : (mulEReal (eOf (d.stg.fsv j).1) (slOf d.e : EReal)).bind
      (addEReal · ((d.mUse (eOf recv) * -(slOf d.e) : ℝ) : EReal)) = some (d.xE (eOf recv) j) := by
    have hw := (hA.w j hj).ne_top
    have hm : mulEReal (eOf (d.stg.fsv j).1) (slOf d.e : EReal) =
        some (eOf (d.stg.fsv j).1 * (slOf d.e : EReal)) := by
      unfold mulEReal
      refine if_neg ?_
      rintro (⟨-, h2 | h2⟩ | ⟨h1, -⟩)
      · exact EReal.coe_ne_top _ h2
      · exact EReal.coe_ne_bot _ h2
      · exact absurd h1 (by exact_mod_cast hs.ne')
    rw [hm]
    simp only [Option.bind_some]
    unfold addEReal
    refine if_neg ?_
    rintro (⟨-, h2⟩ | ⟨-, h2⟩)
    · exact EReal.coe_ne_bot _ h2
    · exact EReal.coe_ne_top _ h2
  rw [exec_fmaEE (idealAtSc (L := L) (g := g) (by decide) hE) ra rb rc (readEReal_sw (hA.w j hj))
    (readEReal_of_valFloat (valFloat_float _)) (readEReal_of_valFloat (valFloat_float _)) hfma]

/-- **The first `m` fused multiply-adds.** -/
theorem seg_fmaXs {d : D} {recv : Value} (hA : StA d recv) : ∀ m, m ≤ 64 →
    Seg kernel asms L g m 1849
      (factsFrom (Flow.live 1849) (valueEx (valueOf L g d) (xa10 d recv))) (1849 + m)
      (factsFrom (Flow.live (1849 + m))
        (valueEx (valueOf L g d) (fx d (eOf recv) m ++ xa10 d recv))) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih => exact fun hm => (ih (by omega)).comp (seg_fmaX1 hA (j := m) (by omega))

/-! ### The 16 software exponentials (pcs 1913 to 2088)

Block `i` (pc `1913 + 11 i`) reads the exponent of column `colR i` (`%r(827 + 2 colR i)`) and
writes `%r(810 + i)`. -/

/-- The overlay after `i` software exponentials. -/
def em (d : D) (rE : EReal) : Nat → List (Nat × Value)
  | 0 => []
  | i + 1 => (1271 + i, Value.float .f32 (Softmax.pow2 (d.xE rE (colR i)))) :: em d rE i

/-- The coverage of an instance: the live registers after it are its output or were live
before and are not written by it. -/
def emuCov (i : Nat) : Bool :=
  (Flow.live (1913 + 11 * i + 11)).all fun r =>
    r == 1271 + i || (!(emuW (1913 + 11 * i)).contains r && (Flow.live (1913 + 11 * i)).contains r)

theorem emu_chk : ∀ i < 16, emuOk (1913 + 11 * i) = true ∧
    Assumptions.emuReg (emuAsg (1913 + 11 * i)) .x = 1288 + 2 * colR i ∧
    Assumptions.emuReg (emuAsg (1913 + 11 * i)) .y = 1271 + i ∧
    (1288 + 2 * colR i) ∈ Flow.live (1913 + 11 * i) ∧ emuCov i = true := by
  decide +kernel

theorem valueEx_em_off (d : D) (rE : EReal) (B : Nat → Value) (ex : List (Nat × Value)) {r : Nat}
    (i : Nat) (h : ∀ k < i, r ≠ 1271 + k) : valueEx B (em d rE i ++ ex) r = valueEx B ex r := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [em, List.cons_append, valueEx_cons_ne _ _ (h i (by omega))]
    exact ih fun k hk => h k (by omega)

theorem colR_lt : ∀ i < 16, colR i < 64 := by decide +kernel

theorem seg_emu1 {d : D} {recv : Value} (hA : StA d recv) {i : Nat} (hi : i < 16) :
    Seg kernel asms L g 1 (1913 + 11 * i)
      (factsFrom (Flow.live (1913 + 11 * i))
        (valueEx (valueOf L g d) (em d (eOf recv) i ++ (fx d (eOf recv) 64 ++ xa10 d recv))))
      (1913 + 11 * i + 11)
      (factsFrom (Flow.live (1913 + 11 * i + 11))
        (valueEx (valueOf L g d)
          (em d (eOf recv) (i + 1) ++ (fx d (eOf recv) 64 ++ xa10 d recv)))) := by
  obtain ⟨hok, hx, hy, hl, hc⟩ := emu_chk i hi
  have hcov : ∀ r ∈ Flow.live (1913 + 11 * i + 11),
      r = 1271 + i ∨ (r ∉ emuW (1913 + 11 * i) ∧ r ∈ Flow.live (1913 + 11 * i)) := by
    intro r hr
    have := List.all_eq_true.mp hc r hr
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_iff_mem] at this
    rcases this with h1 | ⟨h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨by simpa using h2, h3⟩
  have hk := colR_lt i hi
  have h := seg_emu (L := L) (g := g) (x := d.xE (eOf recv) (colR i))
    (liveS := Flow.live (1913 + 11 * i)) (liveT := Flow.live (1913 + 11 * i + 11))
    (base := valueOf L g d) (ex := em d (eOf recv) i ++ (fx d (eOf recv) 64 ++ xa10 d recv))
    hok (hA.xE_ne_top hk) (by rw [hx]; exact hl)
    (by
      rw [hx, valueEx_em_off d _ _ _ i (fun k hk' => by
        have := colR_lt i hi; unfold colR at this ⊢; omega)]
      exact valueEx_fx_in d _ _ _ hk)
    (by rw [hy]; exact hcov)
  rw [hy] at h
  exact h

/-- **The first `n` software exponentials.** -/
theorem seg_emuN {d : D} {recv : Value} (hA : StA d recv) : ∀ n, n ≤ 16 →
    Seg kernel asms L g n 1913
      (factsFrom (Flow.live 1913) (valueEx (valueOf L g d) (fx d (eOf recv) 64 ++ xa10 d recv)))
      (1913 + 11 * n)
      (factsFrom (Flow.live (1913 + 11 * n))
        (valueEx (valueOf L g d) (em d (eOf recv) n ++ (fx d (eOf recv) 64 ++ xa10 d recv)))) := by
  intro n
  induction n with
  | zero => exact fun _ => Seg.refl _ _
  | succ n ih =>
    exact fun hn => (ih (by omega)).comp (seg_emu1 hA (i := n) (by omega))

/-! ### The 64 exponentials (pcs 2089 to 2152)

`%r(826 + 2 j) = ex2(%r(827 + 2 j))`: the probability of column `j`. -/

/-- The overlay after `j` exponentials. -/
def e2 (d : D) (rE : EReal) : Nat → List (Nat × Value)
  | 0 => []
  | j + 1 => (1287 + 2 * j, Value.float .f32 (Softmax.pow2 (d.xE rE j))) :: e2 d rE j

/-- The overlay of the facts after the fused multiply-adds and the software exponentials. -/
abbrev base2 (d : D) (recv : Value) : List (Nat × Value) :=
  em d (eOf recv) 16 ++ (fx d (eOf recv) 64 ++ xa10 d recv)

/-- The instruction at `pc` is `ex2.approx.ftz.f32 d, a`. -/
def ex2At (pc d a : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .float f⟩ =>
    f == { op := .ex2, ty := ty1 .f32, mode := .approx, ftz := true, dsts := [some d],
           srcs := [.reg a] }
  | _ => false

theorem ex2At_spec {pc d a : Nat} (h : ex2At pc d a = true) :
    kernel.code[pc]? = some ⟨none, ex2Op d a⟩ := by
  unfold ex2At at h
  split at h
  · rename_i f hc
    rw [hc, ex2Op, beq_iff_eq.mp h]
  · cases h

theorem ex2_code : ∀ j < 64, ex2At (2089 + j) (1287 + 2 * j) (1288 + 2 * j) = true := by
  decide +kernel

theorem emu_ex2 : ∀ j < 64, Assumptions.emuSites.contains (2089 + j) = false := by
  decide +kernel

theorem live_ex2 : ∀ j < 64, (1288 + 2 * j) ∈ Flow.live (2089 + j) ∧
    subX (Flow.live (2089 + j + 1)) (Flow.live (2089 + j)) [1287 + 2 * j] = true := by
  decide +kernel

theorem valueEx_e2_off (d : D) (rE : EReal) (B : Nat → Value) (ex : List (Nat × Value)) {r : Nat}
    (j : Nat) (h : ∀ k < j, r ≠ 1287 + 2 * k) : valueEx B (e2 d rE j ++ ex) r = valueEx B ex r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [e2, List.cons_append, valueEx_cons_ne _ _ (h j (by omega))]
    exact ih fun k hk => h k (by omega)

theorem valueEx_base2_fx (d : D) (recv : Value) (B : Nat → Value) {k : Nat} (hk : k < 64) :
    valueEx B (base2 d recv) (1288 + 2 * k) = erealValue .f32 (d.xE (eOf recv) k) := by
  unfold base2
  rw [valueEx_em_off d _ _ _ 16 (fun i hi => by omega)]
  exact valueEx_fx_in d _ _ _ hk

theorem seg_ex2one {d : D} {recv : Value} (hA : StA d recv) {j : Nat} (hj : j < 64) :
    Seg kernel asms L g 1 (2089 + j)
      (factsFrom (Flow.live (2089 + j))
        (valueEx (valueOf L g d) (e2 d (eOf recv) j ++ base2 d recv)))
      (2089 + j + 1)
      (factsFrom (Flow.live (2089 + j + 1))
        (valueEx (valueOf L g d) (e2 d (eOf recv) (j + 1) ++ base2 d recv))) := by
  obtain ⟨la, ld⟩ := live_ex2 j hj
  refine Seg.set1 (K := kernel) (ex2At_spec (ex2_code j hj)) rfl (fun t h => ?_) (subX_sound ld)
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_ex2 j hj
  have hp : t.pc = 2089 + j := h.1
  have ra : t.regs (1288 + 2 * j) = some (erealValue .f32 (d.xE (eOf recv) j)) :=
    reg_of h.2.2.2.2 la (by
      rw [valueEx_e2_off d _ _ _ j (fun k hk => by omega)]
      exact valueEx_base2_fx d recv _ hj)
  rw [exec_ex2V (hA.xE_ne_top hj) hE (by omega) (by omega) (by omega) ra]

/-- **The first `m` exponentials.** -/
theorem seg_ex2N {d : D} {recv : Value} (hA : StA d recv) : ∀ m, m ≤ 64 →
    Seg kernel asms L g m 2089
      (factsFrom (Flow.live 2089) (valueEx (valueOf L g d) (base2 d recv))) (2089 + m)
      (factsFrom (Flow.live (2089 + m))
        (valueEx (valueOf L g d) (e2 d (eOf recv) m ++ base2 d recv))) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih => exact fun hm => (ih (by omega)).comp (seg_ex2one hA (j := m) (by omega))

theorem valueEx_e2_in (d : D) (rE : EReal) (B : Nat → Value) (ex : List (Nat × Value))
    {j k : Nat} (hk : k < j) : valueEx B (e2 d rE j ++ ex) (1287 + 2 * k) =
      Value.float .f32 (Softmax.pow2 (d.xE rE k)) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [e2, List.cons_append]
    by_cases h : k = j
    · subst h; exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

theorem valueEx_em_in (d : D) (rE : EReal) (B : Nat → Value) (ex : List (Nat × Value))
    {n k : Nat} (hk : k < n) : valueEx B (em d rE n ++ ex) (1271 + k) =
      Value.float .f32 (Softmax.pow2 (d.xE rE (colR k))) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [em, List.cons_append]
    by_cases h : k = n
    · subst h; exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

/-! ### The 16 selections (pcs 2153 to 2168)

`%r(47 + i) = selp(%r(810 + i), %r(826 + 2 colR i), %p179 or %p180)`: both candidates are the
probability of column `colR i`. -/

/-- The overlay after `i` selections. -/
def sl16 (d : D) (rE : EReal) : Nat → List (Nat × Value)
  | 0 => []
  | i + 1 => (508 + i, Value.float .f32 (Softmax.pow2 (d.xE rE (colR i)))) :: sl16 d rE i

/-- The overlay of the facts after the exponentials. -/
abbrev base3 (d : D) (recv : Value) : List (Nat × Value) :=
  e2 d (eOf recv) 64 ++ base2 d recv

/-- The instruction at `pc` is `selp.f32 d, a, b, p` over registers. -/
def selp3At (pc d a b p : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .int i⟩ => i == ⟨.selp, .float .f32, false, [some d], [.reg a, .reg b, .reg p]⟩
  | _ => false

theorem selp3At_spec {pc d a b p : Nat} (h : selp3At pc d a b p = true) :
    kernel.code[pc]? = some ⟨none, selpOp d (.reg a) (.reg b) p⟩ := by
  unfold selp3At at h
  split at h
  · rename_i f hc
    rw [hc, selpOp, beq_iff_eq.mp h]
  · cases h

theorem selp_code : ∀ i < 16, selp3At (2153 + i) (508 + i) (1271 + i) (1287 + 2 * colR i)
    (179 + i / 8) = true := by decide +kernel

theorem emu_selp : ∀ i < 16, Assumptions.emuSites.contains (2153 + i) = false := by
  decide +kernel

theorem live_selp : ∀ i < 16, (1271 + i) ∈ Flow.live (2153 + i) ∧
    (1287 + 2 * colR i) ∈ Flow.live (2153 + i) ∧ (179 + i / 8) ∈ Flow.live (2153 + i) ∧
    subX (Flow.live (2153 + i + 1)) (Flow.live (2153 + i)) [508 + i] = true := by
  decide +kernel

theorem valueOf_p180 (d : D) : valueOf L g d 179 = .pred (pe0 d.e (g % L.block) d.n) := by
  sm_vals

theorem valueOf_p181 (d : D) : valueOf L g d 180 = .pred (pe1 d.e (g % L.block) d.n) := by
  sm_vals

theorem valueOf_p18x (d : D) (i : Nat) (hi : i < 16) : ∃ b : Bool,
    valueOf L g d (179 + i / 8) = .pred b := by
  have : i / 8 = 0 ∨ i / 8 = 1 := by omega
  rcases this with h | h <;> rw [h]
  · exact ⟨_, valueOf_p180 d⟩
  · exact ⟨_, valueOf_p181 d⟩

theorem valueEx_sl16_off (d : D) (rE : EReal) (B : Nat → Value) (ex : List (Nat × Value))
    {r : Nat} (n : Nat) (h : ∀ k < n, r ≠ 508 + k) :
    valueEx B (sl16 d rE n ++ ex) r = valueEx B ex r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sl16, List.cons_append, valueEx_cons_ne _ _ (h n (by omega))]
    exact ih fun k hk => h k (by omega)

theorem seg_selp1 {d : D} {recv : Value} (hA : StA d recv) {i : Nat} (hi : i < 16) :
    Seg kernel asms L g 1 (2153 + i)
      (factsFrom (Flow.live (2153 + i))
        (valueEx (valueOf L g d) (sl16 d (eOf recv) i ++ base3 d recv))) (2153 + i + 1)
      (factsFrom (Flow.live (2153 + i + 1))
        (valueEx (valueOf L g d) (sl16 d (eOf recv) (i + 1) ++ base3 d recv))) := by
  obtain ⟨la, lb, lp, ld⟩ := live_selp i hi
  have hk := colR_lt i hi
  refine Seg.set1 (K := kernel) (selp3At_spec (selp_code i hi)) rfl (fun t h => ?_)
    (subX_sound ld)
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_selp i hi
  have F := h.2.2.2.2
  obtain ⟨b, hb⟩ := valueOf_p18x (L := L) (g := g) d i hi
  have ra : t.regs (1271 + i) = some (.float .f32 (Softmax.pow2 (d.xE (eOf recv) (colR i)))) :=
    reg_of F la (by
      rw [valueEx_sl16_off d _ _ _ i (fun k hk => by omega), base3,
        valueEx_e2_off d _ _ _ 64 (fun k hk => by omega)]
      exact valueEx_em_in d _ _ _ (by omega))
  have rb : t.regs (1287 + 2 * colR i) =
      some (.float .f32 (Softmax.pow2 (d.xE (eOf recv) (colR i)))) :=
    reg_of F lb (by
      rw [valueEx_sl16_off d _ _ _ i (fun k hk => by omega), base3]
      exact valueEx_e2_in d _ _ _ hk)
  have rp : t.regs (179 + i / 8) = some (.pred b) :=
    reg_of F lp (by
      rw [valueEx_sl16_off d _ _ _ i (fun k hk => by omega), base3,
        valueEx_e2_off d _ _ _ 64 (fun k hk => by omega), base2,
        valueEx_em_off d _ _ _ 16 (fun k hk => by omega),
        valueEx_fx_off d _ _ _ 64 (fun k hk => by omega),
        valueEx_xa10_off d recv _ (by omega), hb])
  show execLocalA asms L g t (selpOp (508 + i) (.reg (1271 + i)) (.reg (1287 + 2 * colR i))
    (179 + i / 8)) = _
  rw [exec_selp (segFree hE) rp (readValue_reg ra) (readValue_reg rb) rfl rfl, ite_self]

/-- **The first `m` selections.** -/
theorem seg_selpN {d : D} {recv : Value} (hA : StA d recv) : ∀ m, m ≤ 16 →
    Seg kernel asms L g m 2153
      (factsFrom (Flow.live 2153) (valueEx (valueOf L g d) (base3 d recv))) (2153 + m)
      (factsFrom (Flow.live (2153 + m))
        (valueEx (valueOf L g d) (sl16 d (eOf recv) m ++ base3 d recv))) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih => exact fun hm => (ih (by omega)).comp (seg_selp1 hA (i := m) (by omega))

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
