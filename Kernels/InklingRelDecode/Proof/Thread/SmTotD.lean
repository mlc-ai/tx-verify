-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmStgB
public import Lemmas.Flow.EmuStep

@[expose] public section

/-! # The score stage's second half on any words: the scalars and the exponents (pcs 1839-1912)

The pieces of `SmStgA` (`seg_a1` … `seg_a10`, `seg_fmaX1`) for any running maximum, any received
maximum and any words of the columns at the shuffle of the row maximum: the registers hold the
outcomes of Core's rules (`maxE`, `setpE`, `movE` for a `selp`, `subE`, `mulE`, `ex2E`, `floatE`
of `fma`) on the values of the table of the state at the shuffle. An instruction that faults
kills the thread (`SegD`). The overlays `xb1` … `xb10` and `fxT` have the registers of `xa1` …
`xa10` and `fx`, with the outcomes' values (`okVal`, `b32 0` where an outcome faults; a predicate
is `false` there). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### Tools -/


theorem toBool_map_pred (e : Exec Bool) : (e.map Value.pred).toBool = e.toBool := by
  rcases e with _ | _ <;> rfl

theorem okB_pred {e : Exec Bool} {x : Value} (h : e.map Value.pred = .ok x) :
    Value.pred (okB e) = x := by
  rcases e with _ | b
  · cases h
  · simp only [Except.map] at h
    cases h
    rfl

/-- `selp.b32 d, a, b, p` at a state without a segment: the outcome of the move of the picked
value. -/
theorem exec_selpE {t : TState} {d p : Nat} {a b : Opnd} {va vb : Value} {pick : Bool}
    (hS : Assumption.SegFreePc asms t.pc) (hp : t.regs p = some (.pred pick))
    (ha : readValue L g t 32 a = .ok va) (hb : readValue L g t 32 b = .ok vb) :
    execLocalA asms L g t (selpOp d a b p) =
      (movE (if pick then va else vb)).map fun x => PTX.next (setReg t d x) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  cases pick
  · by_cases h4 : vb.bytes = 4 <;>
    simp [selpOp, execLocal, Op.rule, IntInstr.rule, execMove, DType.width, readReg, hp, hb, h4,
      movE, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]
  · by_cases h4 : va.bytes = 4 <;>
    simp [selpOp, execLocal, Op.rule, IntInstr.rule, execMove, DType.width, readReg, hp, ha, h4,
      movE, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]

/-- No assumption of the kernel has a local rule for a move. -/
theorem asms_movesSm : CoreMoves asms := fun _ _ _ _ => asms_none (by simp) (by simp)

/-- **One instruction that writes `d` with the outcome `E`** between overlays: the thread
continues with the overlay that gives `d` the value `w` of the outcome, or is dead where it
faults. -/
theorem SegD.set1 {pc d : Nat} {op : Op} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} {E : Exec Value} {w : Value}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom liveS (valueEx base ex)) →
      execLocalA asms L g t op = E.map fun x => PTX.next (setReg t d x))
    (hw : ∀ x, E = .ok x → w = x) (hcov : subX liveT liveS [d] = true) :
    SegD kernel asms L g 1 pc (factsFrom liveS (valueEx base ex)) (pc + 1)
      (factsFrom liveT (valueEx base ((d, w) :: ex))) (E.toBool = true) := by
  refine SegD.oneT hc hl hex (fun x hx _ => ?_) (fun r hr => ?_)
  · rw [valueEx_cons_self]; exact hw x hx
  · rcases subX_sound hcov r hr with h | ⟨h1, h2⟩
    · exact Or.inl (by simpa using h)
    · have hne : r ≠ d := by simpa using h1
      exact Or.inr ⟨hne, h2, valueEx_cons_ne _ _ hne⟩

/-- `SegD.set1` for an outcome that is the value of an instruction's register. -/
theorem SegD.set1v {pc d : Nat} {op : Op} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} {E : Exec Value}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom liveS (valueEx base ex)) →
      execLocalA asms L g t op = E.map fun x => PTX.next (setReg t d x))
    (hcov : subX liveT liveS [d] = true) :
    SegD kernel asms L g 1 pc (factsFrom liveS (valueEx base ex)) (pc + 1)
      (factsFrom liveT (valueEx base ((d, okVal (b32 0) E) :: ex))) (E.toBool = true) :=
  SegD.set1 hc hl hex (fun x hx => okVal_of_ok hx) hcov

/-- `SegD.set1` for a comparison that writes a predicate. -/
theorem SegD.set1p {pc d : Nat} {op : Op} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} {E : Exec Bool}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom liveS (valueEx base ex)) →
      execLocalA asms L g t op = E.map fun r => PTX.next (setReg t d (.pred r)))
    (hcov : subX liveT liveS [d] = true) :
    SegD kernel asms L g 1 pc (factsFrom liveS (valueEx base ex)) (pc + 1)
      (factsFrom liveT (valueEx base ((d, .pred (okB E)) :: ex))) (E.toBool = true) := by
  have h := SegD.set1 (E := E.map Value.pred) (w := .pred (okB E)) (L := L) (g := g) hc hl
    (fun t ht => by rw [hex t ht]; rcases E with _ | _ <;> rfl) (fun x hx => okB_pred hx) hcov
  exact SegD.iff h (by rw [toBool_map_pred])

/-! ### The numbers of pcs 1839 to 1848 -/


theorem emuSc (k : Nat) (hk : k < 10) {t : TState} (h : t.pc = 1839 + k) :
    Assumptions.emuSites.contains t.pc = false := by
  rw [h]; exact emu_xa k hk

theorem segA1T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1839
      (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) 1840
      (factsFrom (Flow.live 1840) (valueEx (valueOf L g d) (xb1 d recv)))
      ((d.t1E recv).toBool = true) := by
  refine SegD.set1v Flow.code_1839 rfl (fun t h => ?_) (live_xa 0 (by omega))
  have hE := emuSc 0 (by omega) h.1
  have hp : t.pc = 1839 := h.1
  have ra : t.regs 1914 = some d.m :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_m])
  have rb : t.regs 1520 = some (ownV fun k => (d.stg.fsv k).1) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_r1061])
  have rc : t.regs 1521 = some recv :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (maxOp 1522 [1914, 1520, 1521]) = _
  exact exec_maxE3 (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega)) ra rb rc

theorem segA2T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1840
      (factsFrom (Flow.live 1840) (valueEx (valueOf L g d) (xb1 d recv))) 1841
      (factsFrom (Flow.live 1841) (valueEx (valueOf L g d) (xb2 d recv)))
      ((d.t2E recv).toBool = true) := by
  refine SegD.set1p Flow.code_1840 rfl (fun t h => ?_) (live_xa 1 (by omega))
  have hE := emuSc 1 (by omega) h.1
  have hp : t.pc = 1840 := h.1
  have ra : t.regs 1522 = some (d.t1 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (setpOp .eq 167 1522 4286578688) = _
  exact exec_setpInfE (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (Or.inl rfl) (by decide) (OpndIs.reg ra) OpndIs.imm

theorem segA3T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1841
      (factsFrom (Flow.live 1841) (valueEx (valueOf L g d) (xb2 d recv))) 1842
      (factsFrom (Flow.live 1842) (valueEx (valueOf L g d) (xb3 d recv)))
      ((d.t3E recv).toBool = true) := by
  refine SegD.set1v Flow.code_1841 rfl (fun t h => ?_) (live_xa 2 (by omega))
  have hE := emuSc 2 (by omega) h.1
  have hp : t.pc = 1841 := h.1
  have rp : t.regs 167 = some (.pred (d.t2 recv)) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  have rb : t.regs 1522 = some (d.t1 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (selpOp 1523 (.f32imm 0) (.reg 1522) 167) = _
  exact exec_selpE (segFree hE) rp readValue_imm (readValue_reg rb)

theorem segA4T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1842
      (factsFrom (Flow.live 1842) (valueEx (valueOf L g d) (xb3 d recv))) 1843
      (factsFrom (Flow.live 1843) (valueEx (valueOf L g d) (xb4 d recv)))
      ((d.t4E recv).toBool = true) := by
  refine SegD.set1v Flow.code_1842 rfl (fun t h => ?_) (live_xa 3 (by omega))
  have hE := emuSc 3 (by omega) h.1
  have hp : t.pc = 1842 := h.1
  have ra : t.regs 1914 = some d.m :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_m])
  have rb : t.regs 1523 = some (d.t3 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (subOp 1524 1914 1523) = _
  exact PTX.Flow.exec_subE (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg ra) (OpndIs.reg rb)

theorem segA5T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1843
      (factsFrom (Flow.live 1843) (valueEx (valueOf L g d) (xb4 d recv))) 1844
      (factsFrom (Flow.live 1844) (valueEx (valueOf L g d) (xb5 d recv)))
      ((d.t5E recv).toBool = true) := by
  refine SegD.set1v Flow.code_1843 rfl (fun t h => ?_) (live_xa 4 (by omega))
  have hE := emuSc 4 (by omega) h.1
  have hp : t.pc = 1843 := h.1
  have ra : t.regs 498 = some (.float .f32 (slOf d.e)) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_r37])
  have rb : t.regs 1524 = some (d.t4 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (mulOp 1270 498 1524) = _
  exact PTX.Flow.exec_mulE (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg ra) (OpndIs.reg rb)

theorem segA6T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1844
      (factsFrom (Flow.live 1844) (valueEx (valueOf L g d) (xb5 d recv))) 1845
      (factsFrom (Flow.live 1845) (valueEx (valueOf L g d) (xb6 d recv)))
      ((d.t6E recv).toBool = true) := by
  refine SegD.set1p Flow.code_1844 rfl (fun t h => ?_) (live_xa 5 (by omega))
  have hE := emuSc 5 (by omega) h.1
  have hp : t.pc = 1844 := h.1
  have ra : t.regs 1270 = some (d.t5 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (setpOp .ge 168 1270 3238002688) = _
  exact exec_setpE (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (Or.inl rfl) rfl (by decide) (OpndIs.reg ra) OpndIs.imm

theorem segA7T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1845
      (factsFrom (Flow.live 1845) (valueEx (valueOf L g d) (xb6 d recv))) 1846
      (factsFrom (Flow.live 1846) (valueEx (valueOf L g d) (xb7 d recv)))
      ((d.t7E recv).toBool = true) := by
  refine SegD.set1v Flow.code_1845 rfl (fun t h => ?_) (live_xa 6 (by omega))
  have hE := emuSc 6 (by omega) h.1
  have hp : t.pc = 1845 := h.1
  have ra : t.regs 1270 = some (d.t5 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  obtain ⟨hA, hD⟩ := approxAt_ex2 (L := L) (g := g) hE (by omega) (by omega) (by omega)
  show execLocalA asms L g t (ex2Op 1269 1270) = _
  exact exec_ex2E hA hD (OpndIs.reg ra)

theorem segA8T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1846
      (factsFrom (Flow.live 1846) (valueEx (valueOf L g d) (xb7 d recv))) 1847
      (factsFrom (Flow.live 1847) (valueEx (valueOf L g d) (xb8 d recv)))
      ((d.t8E recv).toBool = true) := by
  refine SegD.set1v Flow.code_1846 rfl (fun t h => ?_) (live_xa 7 (by omega))
  have hE := emuSc 7 (by omega) h.1
  have hp : t.pc = 1846 := h.1
  have rp : t.regs 168 = some (.pred (d.t6 recv)) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  have rb : t.regs 1269 = some (d.t7 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (selpOp 507 (.f32imm 1065353216) (.reg 1269) 168) = _
  exact exec_selpE (segFree hE) rp readValue_imm (readValue_reg rb)

theorem segA9T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1847
      (factsFrom (Flow.live 1847) (valueEx (valueOf L g d) (xb8 d recv))) 1848
      (factsFrom (Flow.live 1848) (valueEx (valueOf L g d) (xb9 d recv)))
      ((d.t9E recv).toBool = true) := by
  refine SegD.set1v Flow.code_1847 rfl (fun t h => ?_) (live_xa 8 (by omega))
  have hE := emuSc 8 (by omega) h.1
  have hp : t.pc = 1847 := h.1
  have rp : t.regs 168 = some (.pred (d.t6 recv)) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  have ra : t.regs 1914 = some d.m :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_m])
  have rb : t.regs 1523 = some (d.t3 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (selpOp 1525 (.reg 1914) (.reg 1523) 168) = _
  exact exec_selpE (segFree hE) rp (readValue_reg ra) (readValue_reg rb)

theorem segA10T (d : D) (recv : Value) :
    SegD kernel asms L g 1 1848
      (factsFrom (Flow.live 1848) (valueEx (valueOf L g d) (xb9 d recv))) 1849
      (factsFrom (Flow.live 1849) (valueEx (valueOf L g d) (xb10 d recv)))
      ((d.t10E recv).toBool = true) := by
  refine SegD.set1v Flow.code_1848 rfl (fun t h => ?_) (live_xa 9 (by omega))
  have hE := emuSc 9 (by omega) h.1
  have hp : t.pc = 1848 := h.1
  have ra : t.regs 1525 = some (d.t9 recv) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup])
  have rb : t.regs 499 = some (.float .f32 (-(slOf d.e))) :=
    reg_of h.2.2.2.2 (by decide +kernel) (by simp [valueEx, List.lookup, valueOf_r38])
  show execLocalA asms L g t (mulOp 1526 1525 499) = _
  exact PTX.Flow.exec_mulE (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg ra) (OpndIs.reg rb)

/-- **The ten instructions on any words** (pcs 1839 to 1848). -/
theorem segAT (d : D) (recv : Value) :
    SegD kernel asms L g 10 1839
      (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) 1849
      (factsFrom (Flow.live 1849) (valueEx (valueOf L g d) (xb10 d recv))) (d.okA recv) :=
  SegD.of_len ((((((((((segA1T d recv).comp (segA2T d recv)).comp (segA3T d recv)).comp
    (segA4T d recv)).comp (segA5T d recv)).comp (segA6T d recv)).comp (segA7T d recv)).comp
    (segA8T d recv)).comp (segA9T d recv)).comp (segA10T d recv)) rfl

theorem valueEx_xb10_off (d : D) (recv : Value) (B : Nat → Value) {r : Nat}
    (h : r ≠ 1521 ∧ r ≠ 1522 ∧ r ≠ 167 ∧ r ≠ 1523 ∧ r ≠ 1524 ∧ r ≠ 1270 ∧ r ≠ 168 ∧ r ≠ 1269 ∧
      r ≠ 507 ∧ r ≠ 1525 ∧ r ≠ 1526) : valueEx B (xb10 d recv) r = B r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp only [xb10, xb9, xb8, xb7, xb6, xb5, xb4, xb3, xb2, xb1, xa0]
  rw [valueEx_cons_ne _ _ h11, valueEx_cons_ne _ _ h10, valueEx_cons_ne _ _ h9,
    valueEx_cons_ne _ _ h8, valueEx_cons_ne _ _ h7, valueEx_cons_ne _ _ h6,
    valueEx_cons_ne _ _ h5, valueEx_cons_ne _ _ h4, valueEx_cons_ne _ _ h3,
    valueEx_cons_ne _ _ h2, valueEx_cons_ne _ _ h1, valueEx_nil]

/-! ### The 64 exponents (pcs 1849 to 1912) -/


theorem valueEx_fxT_off (d : D) (recv : Value) (B : Nat → Value) (ex : List (Nat × Value))
    {r : Nat} (j : Nat) (h : ∀ k < j, r ≠ 1288 + 2 * k) :
    valueEx B (fxT d recv j ++ ex) r = valueEx B ex r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [fxT, List.cons_append, valueEx_cons_ne _ _ (h j (by omega))]
    exact ih fun k hk => h k (by omega)

theorem valueEx_fxT_in (d : D) (recv : Value) (B : Nat → Value) (ex : List (Nat × Value))
    {j k : Nat} (hk : k < j) : valueEx B (fxT d recv j ++ ex) (1288 + 2 * k) = d.xT recv k := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [fxT, List.cons_append]
    by_cases h : k = j
    · subst h; exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

theorem segFmaT1 (d : D) (recv : Value) {j : Nat} (hj : j < 64) :
    SegD kernel asms L g 1 (1849 + j)
      (factsFrom (Flow.live (1849 + j))
        (valueEx (valueOf L g d) (fxT d recv j ++ xb10 d recv)))
      (1849 + j + 1)
      (factsFrom (Flow.live (1849 + j + 1))
        (valueEx (valueOf L g d) (fxT d recv (j + 1) ++ xb10 d recv)))
      ((d.xTE recv j).toBool = true) := by
  obtain ⟨la, lb, lc, ld⟩ := live_fmaX j hj
  have hr := colReg_range j hj
  refine SegD.set1v (fmaAt_spec (fmaX_code j hj)) rfl (fun t h => ?_) ld
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_fmaX j hj
  have hp : t.pc = 1849 + j := h.1
  have F := h.2.2.2.2
  have ra : t.regs (colReg j) = some (d.stg.fsv j).1 :=
    reg_of F la (by
      rw [valueEx_fxT_off d recv _ _ j (fun k hk => by omega),
        valueEx_xb10_off d recv _ (by omega), valueOf_word d hj])
  have rb : t.regs 498 = some (.float .f32 (slOf d.e)) :=
    reg_of F lb (by
      rw [valueEx_fxT_off d recv _ _ j (fun k hk => by omega),
        valueEx_xb10_off d recv _ (by omega), valueOf_r37])
  have rc : t.regs 1526 = some (d.t10 recv) :=
    reg_of F lc (by
      rw [valueEx_fxT_off d recv _ _ j (fun k hk => by omega)]
      simp [valueEx, List.lookup])
  show execLocalA asms L g t (fmaOp (1288 + 2 * j) (colReg j) 498 1526) = _
  exact exec_floatE_fma_at (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg ra) (OpndIs.reg rb) (OpndIs.reg rc)

/-- **The first `m` fused multiply-adds on any words.** -/
theorem segFmaTN (d : D) (recv : Value) : ∀ m, m ≤ 64 →
    SegD kernel asms L g m 1849
      (factsFrom (Flow.live 1849) (valueEx (valueOf L g d) (xb10 d recv))) (1849 + m)
      (factsFrom (Flow.live (1849 + m))
        (valueEx (valueOf L g d) (fxT d recv m ++ xb10 d recv)))
      (∀ j < m, (d.xTE recv j).toBool = true) := by
  intro m
  induction m with
  | zero =>
    exact fun _ => SegD.iff (SegD.of_seg (Seg.refl _ _)) ⟨fun _ j hj => absurd hj (by omega),
      fun _ => trivial⟩
  | succ m ih =>
    exact fun hm => SegD.iff ((ih (by omega)).comp (segFmaT1 d recv (j := m) (by omega)))
      ⟨fun ⟨h1, h2⟩ j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h1 j h
        · exact h2,
       fun h => ⟨fun j hj => h j (by omega), h m (by omega)⟩⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
