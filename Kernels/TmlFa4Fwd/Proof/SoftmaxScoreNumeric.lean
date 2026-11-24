-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Flow.FmaRun
public import Mathlib.Data.EReal.Operations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Assumption

noncomputable section

/-- A masked score is stored as the exact negative-infinity encoding. -/
def scoreValue : Option ℝ → Value
  | none => .bits 32 (BitVec.ofNat 64 0xFF800000)
  | some x => .float .f32 x

/-- A positive softmax denominator has a finite score maximum. -/
structure DenominatorValid (sum : ℝ) (maximum : Option ℝ) : Prop where
  nonnegative : 0 ≤ sum
  finiteMaximum : 0 < sum → ∃ maximumValue, maximum = some maximumValue

def scoreReal : Option ℝ → EReal
  | none => ⊥
  | some x => x

theorem scoreValue_bytes (x : Option ℝ) : (scoreValue x).bytes = 4 := by
  cases x <;> rfl

theorem readScoreValue (x : Option ℝ) :
    readEReal .f32 (scoreValue x) = some (.ok (scoreReal x)) := by
  cases x with
  | none =>
    have hz := classify_bits (fmt := .f32) (n := 0xFF800000) (x := .inf true)
      (by decide) (by decide)
    change readEReal.ofDatum (classify .f32 (.bits 32 (BitVec.ofNat 64 0xFF800000))) =
      some (.ok ⊥)
    change classify .f32 (.bits 32 (BitVec.ofNat 64 0xFF800000)) = .ok (.inf true) at hz
    rw [hz]
    rfl
  | some x => rfl

theorem scoreReal_value (x : Option ℝ) : erealValue .f32 (scoreReal x) = scoreValue x := by
  cases x with
  | none => simp [scoreReal, scoreValue, erealValue]; rfl
  | some x =>
    unfold scoreReal erealValue scoreValue
    rw [ite_eq_right (EReal.coe_ne_top x), ite_eq_right (EReal.coe_ne_bot x)]
    rfl

/-- The packed affine transform used both for adding bias and for shifting by a finite reference.
The scale is positive, so negative infinity remains the mask in each lane. -/
def affineScore (scale offset : ℝ) (x : Option ℝ) : Option ℝ :=
  x.map (fun a => a * scale + offset)

private theorem affineScore_real {scale offset : ℝ} (hs : 0 < scale) (x : Option ℝ) :
    (mulEReal (scoreReal x) (scale : EReal)).bind (addEReal · (offset : EReal)) =
      some (scoreReal (affineScore scale offset x)) := by
  cases x with
  | none =>
    have hScale : (scale : EReal) ≠ 0 := ne_of_gt (EReal.coe_pos.mpr hs)
    simp [scoreReal, affineScore, mulEReal, addEReal, hScale, EReal.bot_mul_coe_of_pos hs,
      EReal.bot_add]
  | some x =>
    simp [scoreReal, affineScore, mulEReal, addEReal, ← EReal.coe_mul, ← EReal.coe_add]

theorem splitScorePair (x y : Option ℝ) :
    splitValue 64 (joinValue (scoreValue x) (scoreValue y)) = (scoreValue x, scoreValue y) := by
  cases x <;> cases y <;> rfl

variable {l : Launch}

private theorem readPackedScores {g r : Nat} {t : TState} {word : Value} {x y : Option ℝ}
    (h : t.regs r = some word) (hSplit : splitValue 64 word = (scoreValue x, scoreValue y)) :
    readERealPair l g t (.reg r) = some (.ok (scoreReal x, scoreReal y)) := by
  rw [readERealPair_reg_val h]
  simp [pairRead, hSplit, readScoreValue, pure, Except.pure]

/-- One actual packed FMA preserves the causal mask independently in both lanes. Its positive
scale and finite addend are read through the same register rules as the decoded instruction. -/
theorem execMaskedFmaOfSplit {g d a c z : Nat} {t : TState} {x y : Option ℝ} {scale z₀ z₁ : ℝ}
    (hs : 0 < scale) {word : Value} (ha : t.regs a = some word)
    (hSplit : splitValue 64 word = (scoreValue x, scoreValue y))
    (hc : readERealPair l g t (.reg c) = some (.ok ((scale : EReal), (scale : EReal))))
    (hz : readERealPair l g t (.reg z) = some (.ok ((z₀ : EReal), (z₁ : EReal))))
    (hS : SegFreePc (Assumptions.all.drop 1) t.pc) :
    execLocalA Assumptions.all l g t (fma2Op d a c z) =
      .ok (next (setReg t d (.pair (scoreValue (affineScore scale z₀ x))
        (scoreValue (affineScore scale z₁ y))))) := by
  have hra := readPackedScores (l := l) (g := g) ha hSplit
  have hExec : execIdealFloat l g t (fma2Op d a c z) =
      some (.ok (next (setReg t d (.pair (scoreValue (affineScore scale z₀ x))
        (scoreValue (affineScore scale z₁ y)))))) := by
    simp only [fma2Op, execIdealFloat, hra, hc, hz, bindRead, affineScore_real hs,
      scoreReal_value, pure, Except.pure]
  exact execLocalA_idealReal (f := .fmaRnF32x2) (by simp [fma2Op, FloatForm.ofOp])
    (by simp [Assumptions.arithScope]) hS hExec

private theorem segFree {pc : Nat} (h : pc ∉ Assumptions.swExp2Sites) :
    SegFreePc Assumptions.all pc := by
  intro a ha l g t ht
  rcases List.mem_append.mp ha with ha | hInput
  · rcases List.mem_append.mp ha with hNum | hSync
    · exact (Assumptions.numeric_segSites.pc h) a hNum l g t ht
    · simp only [Assumptions.synchronization, List.mem_cons, List.not_mem_nil, or_false] at hSync
      rcases hSync with rfl | rfl | rfl | rfl <;> rfl
  · obtain rfl := List.mem_singleton.mp hInput
    rfl

private theorem readPair_congr {g r : Nat} {t u : TState} (h : u.regs r = t.regs r) :
    readERealPair l g u (.reg r) = readERealPair l g t (.reg r) := by
  simp [readERealPair, readValue, readReg, h]

private theorem execScorePack {g dst lo hi : Nat} {t : TState} {x y : Value}
    (hs : t.pc ∉ Assumptions.swExp2Sites) (hlo : t.regs lo = some x) (hhi : t.regs hi = some y)
    (hSize : x.bytes = 4 ∧ y.bytes = 4) :
    execLocalA Assumptions.all l g t
      (.move ⟨.pack, .int .b 64, [some dst], [.reg lo, .reg hi]⟩) =
      .ok (next (setReg t dst (joinValue x y))) := by
  rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hs rfl]
  simpa only [ite_eq_left hSize] using
    exec_pack (A := []) (L := l) (g := g) (d := dst) (by simp [NoPack])
      hlo hhi SegFreePc.nil

private theorem execScoreUnpack {g src lo hi : Nat} {t : TState} {x y : Option ℝ}
    (hs : t.pc ∉ Assumptions.swExp2Sites)
    (h : t.regs src = some (.pair (scoreValue x) (scoreValue y))) :
    execLocalA Assumptions.all l g t
      (.move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg src]⟩) =
      .ok (next (setReg (setReg t lo (scoreValue x)) hi (scoreValue y))) := by
  rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hs rfl]
  exact exec_unpack64 h (scoreValue_bytes x) (scoreValue_bytes y)
    SegFreePc.nil (by simp [NoUnpack64])

/-- The optional pack places the original score bytes into the FMA operand. -/
private theorem maskedFmaPack {g c z : Nat} {t : TState} {it : FmaItem} (v : Nat → Value)
    (hCode : it.codeB kernel c z t.pc = true) (hf : t.fault = none)
    (hr : ∀ r ∈ it.reads, t.regs r = some (v r)) (hP : it.packOk v = true)
    (hSites : ∀ n < it.len, t.pc + n ∉ Assumptions.swExp2Sites) :
    ∃ u, run kernel Assumptions.all l g (it.len - 2) t = some u ∧
      u.pc = t.pc + (it.len - 2) ∧ u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      u.regs it.a = some (it.src v) ∧ ∀ r ≠ it.a, u.regs r = t.regs r := by
  cases h : it.pk with
  | none =>
    have ha : t.regs it.a = some (it.src v) := by
      simpa only [FmaItem.src, h] using hr it.a (by simp [FmaItem.reads, h])
    exact ⟨t, by simp [FmaItem.len, h, run], by simp [FmaItem.len, h],
      hf, rfl, rfl, ha, fun _ _ => rfl⟩
  | some pair =>
    obtain ⟨lo, hi⟩ := pair
    have hL : it.len = 3 := by simp [FmaItem.len, h]
    have hLo := hr lo (by simp [FmaItem.reads, h])
    have hHi := hr hi (by simp [FmaItem.reads, h])
    have hSize : (v lo).bytes = 4 ∧ (v hi).bytes = 4 := by
      simpa only [FmaItem.packOk, h, Bool.and_eq_true, beq_iff_eq] using hP
    have hPack := execScorePack (l := l) (g := g) (dst := it.a)
      (by simpa using hSites 0 (by rw [hL]; decide)) hLo hHi hSize
    let u := next (setReg t it.a (it.src v))
    have hRun := run_step (K := kernel) (n := 0) ((FmaItem.code_of hCode).1 lo hi h)
      rfl hf hPack
    refine ⟨u, ?_, ?_, hf, rfl, rfl, ?_, ?_⟩
    · rw [hL]
      simpa only [u, FmaItem.src, h, Nat.reduceSub, run] using hRun
    · rw [hL]
      rfl
    · simp [u, next, setReg]
    · intro r hNe
      simp [u, next, setReg, Function.update_of_ne hNe]

/-- The optional pack, FMA and unpack preserve the masks and affect only their decoded
destination registers. -/
theorem maskedFmaItemOfSplit {g c z : Nat} {t : TState} {it : FmaItem} {x y : Option ℝ}
    {scale z₀ z₁ : ℝ} (hs : 0 < scale) (v : Nat → Value) (hCode : it.codeB kernel c z t.pc = true)
    (hf : t.fault = none) (hr : ∀ r ∈ it.reads, t.regs r = some (v r)) (hP : it.packOk v = true)
    (hSrc : splitValue 64 (it.src v) = (scoreValue x, scoreValue y))
    (hc : readERealPair l g t (.reg c) = some (.ok ((scale : EReal), (scale : EReal))))
    (hz : readERealPair l g t (.reg z) = some (.ok ((z₀ : EReal), (z₁ : EReal))))
    (ha : it.a ≠ c ∧ it.a ≠ z) (hxy : it.x ≠ it.y)
    (hSites : ∀ n < it.len, t.pc + n ∉ Assumptions.swExp2Sites) :
    ∃ u, run kernel Assumptions.all l g it.len t = some u ∧ u.pc = t.pc + it.len ∧
      u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      u.regs it.x = some (scoreValue (affineScore scale z₀ x)) ∧
      u.regs it.y = some (scoreValue (affineScore scale z₁ y)) ∧
      ∀ r ∉ it.writes, u.regs r = t.regs r := by
  have hLen : 2 ≤ it.len := by unfold FmaItem.len; split <;> decide
  obtain ⟨t₁, hRun₁, hPlace₁, hF, hSub, hAcc, hArg, hFrame⟩ :=
    maskedFmaPack (l := l) (g := g) v hCode hf hr hP hSites
  have hc₁ := (readPair_congr (l := l) (g := g) (hFrame c ha.1.symm)).trans hc
  have hz₁ := (readPair_congr (l := l) (g := g) (hFrame z ha.2.symm)).trans hz
  obtain ⟨_, h₂, h₃⟩ := FmaItem.code_of hCode
  let vx := scoreValue (affineScore scale z₀ x)
  let vy := scoreValue (affineScore scale z₁ y)
  let t₂ := next (setReg t₁ it.q (.pair vx vy))
  let u := next (setReg (setReg t₂ it.x vx) it.y vy)
  have hPlace₂ : t₂.pc = t.pc + (it.len - 1) := by
    change t₁.pc + 1 = _
    rw [hPlace₁]
    omega
  have hRun₂ : run kernel Assumptions.all l g 2 t₁ = run kernel Assumptions.all l g 1 t₂ := by
    apply run_step (by rwa [hPlace₁]) rfl hF
    apply execMaskedFmaOfSplit hs hArg hSrc hc₁ hz₁
    rw [hPlace₁]
    exact (segFree (hSites _ (by omega))).tail
  have hRun₃ : run kernel Assumptions.all l g 1 t₂ = some u := by
    apply run_step (by rwa [hPlace₂]) rfl (show t₂.fault = none from hF)
    exact execScoreUnpack (hPlace₂ ▸ hSites _ (by omega)) (by simp [t₂, vx, vy, next, setReg])
  refine ⟨u, ?_, ?_, hF, hSub, hAcc, ?_, ?_, ?_⟩
  · have hTotal : it.len = it.len - 2 + 2 := by omega
    conv_lhs => rw [hTotal]
    exact run_comp hRun₁ (hRun₂.trans hRun₃)
  · change t₂.pc + 1 = _
    rw [hPlace₂]
    omega
  · simp [u, vx, next, setReg, Function.update_of_ne hxy]
  · simp [u, vy, next, setReg]
  · intro r hNot
    have hQ : r ≠ it.q := by intro hr; apply hNot; simp [FmaItem.writes, hr]
    have hX : r ≠ it.x := by intro hr; apply hNot; simp [FmaItem.writes, hr]
    have hY : r ≠ it.y := by intro hr; apply hNot; simp [FmaItem.writes, hr]
    have hR : t₁.regs r = t.regs r := by
      cases hk : it.pk with
      | none =>
        have hBase : it.len - 2 = 0 := by simp [FmaItem.len, hk]
        rw [hBase] at hRun₁
        cases hRun₁
        rfl
      | some =>
        exact hFrame r (by intro hr; apply hNot; simp [FmaItem.writes, hk, hr])
    simpa [u, t₂, next, setReg, Function.update_of_ne hQ, Function.update_of_ne hX,
      Function.update_of_ne hY] using hR

/-- A sequence of independent affine score items reads the original values of all its
operands. Its register frame supports the next exponentiation stage. -/
theorem maskedFmaRunOfSplit {g c z : Nat} {scale z₀ z₁ : ℝ} (hs : 0 < scale) (v : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) :
    ∀ (items : List FmaItem) (t : TState),
      fmaCodeB kernel c z t.pc items = true → t.fault = none →
      (∀ it ∈ items, ∀ r ∈ it.reads, t.regs r = some (v r)) →
      (∀ it ∈ items, it.packOk v = true ∧ splitValue 64 (it.src v) =
        (scoreValue (scores it).1, scoreValue (scores it).2)) →
      readERealPair l g t (.reg c) = some (.ok ((scale : EReal), (scale : EReal))) →
      readERealPair l g t (.reg z) = some (.ok ((z₀ : EReal), (z₁ : EReal))) →
      (∀ it ∈ items, ∀ r ∈ it.writes, r ≠ c ∧ r ≠ z ∧ ∀ other ∈ items, r ∉ other.reads) →
      (∀ it ∈ items, it.a ≠ c ∧ it.a ≠ z) →
      (items.flatMap FmaItem.writes).Nodup →
      (∀ n < fmaLen items, t.pc + n ∉ Assumptions.swExp2Sites) →
      ∃ u, run kernel Assumptions.all l g (fmaLen items) t = some u ∧
        u.pc = t.pc + fmaLen items ∧ u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
        (∀ r ∉ items.flatMap FmaItem.writes, u.regs r = t.regs r) ∧
        ∀ it ∈ items,
          u.regs it.x = some (scoreValue (affineScore scale z₀ (scores it).1)) ∧
          u.regs it.y = some (scoreValue (affineScore scale z₁ (scores it).2)) := by
  intro items
  induction items with
  | nil =>
    intro t _ hf _ _ _ _ _ _ _ _
    exact ⟨t, rfl, rfl, hf, rfl, rfl, fun _ _ => rfl, by simp⟩
  | cons it its ih =>
    intro t hCode hf hR hP hc hz hD hA hN hSites
    simp only [fmaCodeB, Bool.and_eq_true] at hCode
    simp only [List.flatMap_cons, List.nodup_append] at hN
    have hXY : it.x ≠ it.y := by
      have h := hN.1
      cases hp : it.pk <;>
        simp only [FmaItem.writes, hp, List.cons_append, List.nil_append, List.nodup_cons,
          List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at h
      · exact h.2.1
      · exact h.2.2.1
    have h := hP it (by simp)
    obtain ⟨t₁, hStep, hPc, hF, hSub, hAcc, hX, hY, hFrame⟩ := maskedFmaItemOfSplit hs v
      hCode.1 hf (hR it (by simp)) h.1 h.2 hc hz (hA it (by simp)) hXY
      (fun n hn => hSites n (by simp only [fmaLen]; omega))
    have hc₁ := (readPair_congr (l := l) (g := g) (hFrame c
      (fun h => (hD it (by simp) c h).1 rfl))).trans hc
    have hz₁ := (readPair_congr (l := l) (g := g) (hFrame z
      (fun h => (hD it (by simp) z h).2.1 rfl))).trans hz
    obtain ⟨u, hRun, hU, hUF, hUSub, hUAcc, hUFrame, hOut⟩ := ih t₁
      (by rw [hPc]; exact hCode.2) hF
      (fun j hj r hr => (hFrame r
        (fun h => (hD it (by simp) r h).2.2 j (by simp [hj]) hr)).trans
        (hR j (by simp [hj]) r hr))
      (fun j hj => hP j (by simp [hj])) hc₁ hz₁
      (fun j hj r hr => ⟨(hD j (by simp [hj]) r hr).1, (hD j (by simp [hj]) r hr).2.1,
        fun k hk => (hD j (by simp [hj]) r hr).2.2 k (by simp [hk])⟩)
      (fun j hj => hA j (by simp [hj]))
      hN.2.1 (fun n hn => by
        rw [hPc, Nat.add_assoc]
        exact hSites (it.len + n) (by simp only [fmaLen]; omega))
    refine ⟨u, run_comp hStep hRun, ?_, hUF, hUSub.trans hSub, hUAcc.trans hAcc, ?_, ?_⟩
    · rw [hU, hPc, fmaLen, Nat.add_assoc]
    · intro r hr
      simp only [List.flatMap_cons, List.mem_append, not_or] at hr
      exact (hUFrame r hr.2).trans (hFrame r hr.1)
    · intro j hj
      rcases List.mem_cons.mp hj with heq | hj
      · subst j
        have hx : it.x ∈ it.writes := by simp [FmaItem.writes]
        have hy : it.y ∈ it.writes := by simp [FmaItem.writes]
        rw [hUFrame it.x (fun h => hN.2.2 it.x hx it.x h rfl),
          hUFrame it.y (fun h => hN.2.2 it.y hy it.y h rfl)]
        exact ⟨hX, hY⟩
      · exact hOut j hj

theorem execMaskedFma {g d a c z : Nat} {t : TState} {x y : Option ℝ} {scale z₀ z₁ : ℝ}
    (hs : 0 < scale) (ha : t.regs a = some (joinValue (scoreValue x) (scoreValue y)))
    (hc : readERealPair l g t (.reg c) = some (.ok ((scale : EReal), (scale : EReal))))
    (hz : readERealPair l g t (.reg z) = some (.ok ((z₀ : EReal), (z₁ : EReal))))
    (hS : SegFreePc (Assumptions.all.drop 1) t.pc) :
    execLocalA Assumptions.all l g t (fma2Op d a c z) =
      .ok (next (setReg t d (.pair (scoreValue (affineScore scale z₀ x))
        (scoreValue (affineScore scale z₁ y))))) :=
  execMaskedFmaOfSplit hs ha (splitScorePair x y) hc hz hS

end
end PTX.Kernels.TmlFa4Fwd.Softmax
