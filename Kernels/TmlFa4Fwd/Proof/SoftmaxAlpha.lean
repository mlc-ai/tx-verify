-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlphaValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMax

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Numeric

noncomputable section

/-- Register fields of a seven-instruction reference update in either repeated path. -/
structure AlphaSite where
  pc : Nat
  prior : Nat
  candidate : Nat
  guarded : Nat
  scale : Nat
  diff : Nat
  delta : Nat
  exponent : Nat
  pred : Nat
  finite : Nat
  alpha : Nat

def alphaSite (biased : Bool) : AlphaSite :=
  if biased then ⟨5668, 7251, 4560, 4561, 7132, 4562, 4563, 4564, 636, 4565, 1362⟩
  else ⟨6879, 7255, 5509, 5510, 7133, 5511, 5512, 5513, 646, 5514, 1492⟩

def AlphaSite.items (s : AlphaSite) : List OItem :=
  [.sub false s.diff s.prior s.guarded, .mul false s.delta s.scale s.diff,
    .ex2 true s.exponent s.delta, .setp (.ord .ge) false s.pred s.delta 0xC1000000,
    .selp 7256 (.reg s.prior) (.reg s.candidate) s.pred,
    .selp s.finite (.reg s.prior) (.reg s.guarded) s.pred,
    .selp s.alpha (.f32imm 0x3F800000) (.reg s.exponent) s.pred]

def AlphaSite.inputs (s : AlphaSite) : List Nat := [s.prior, s.candidate, s.guarded, s.scale]

def AlphaSite.valuesOfWord (s : AlphaSite) (word : Value) (old candidate : Option ℝ)
    (r : Nat) : Value :=
  if r = s.prior then scoreValue old
  else if r = s.candidate then scoreValue candidate
  else if r = s.guarded then finiteRefValue candidate
  else if r = s.scale then word
  else .pred false

def AlphaSite.values (s : AlphaSite) (scale : ℝ) (old candidate : Option ℝ) (r : Nat) : Value :=
  s.valuesOfWord (.float .f32 scale) old candidate r

def alphaWord (scale : ℝ) (old candidate : Option ℝ) : Value :=
  if keepReference scale old candidate then .bits 32 (BitVec.ofNat 64 0x3F800000)
  else .float .f32 (correctionAlpha scale old candidate)

theorem alphaWord_valFloat (scale : ℝ) (old candidate : Option ℝ) :
    valFloat .f32 (alphaWord scale old candidate) =
      .ok (maskedRescale (old.map (scale * ·))
        ((chosenReference scale old candidate).map (scale * ·))) := by
  rw [← correctionAlpha_eq]
  by_cases h : keepReference scale old candidate
  · have hNum : f32Value 0x3F800000 = some 1 := by
      norm_num [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
        Layout.magnitude, Layout.bias, Layout.width, FVal.num]
    simpa [alphaWord, correctionAlpha, h, b32] using
      valFloat_b32 (by decide : 0x3F800000 < 2 ^ 64) hNum
  · simp only [alphaWord, h, Bool.false_eq_true, ↓reduceIte]
    rfl

private theorem alphaCode (biased : Bool) :
    oCodeB kernel (alphaSite biased).pc (alphaSite biased).items = true := by
  cases biased <;>
    simp only [alphaSite, Bool.false_eq_true, ↓reduceIte, AlphaSite.items, oCodeB, OItem.codeB,
      Flow.code_5668, Flow.code_5669, Flow.code_5670, Flow.code_5671, Flow.code_5672,
      Flow.code_5673, Flow.code_5674, Flow.code_6879, Flow.code_6880, Flow.code_6881,
      Flow.code_6882, Flow.code_6883, Flow.code_6884, Flow.code_6885, Nat.reduceAdd] <;> rfl

private theorem alphaReads (biased : Bool) :
    oReadsB (alphaSite biased).inputs (alphaSite biased).items = true := by
  cases biased <;> decide +kernel

private theorem alphaLocal (biased : Bool) : oLocalB (alphaSite biased).items = true := by
  cases biased <;> decide +kernel

private theorem alphaOff (biased : Bool) {n : Nat} (hn : n < 7) :
    (alphaSite biased).pc + n ∉ Assumptions.swExp2Sites := by
  cases biased <;>
    simp only [alphaSite, Bool.false_eq_true, ↓reduceIte, Assumptions.swExp2Sites,
      List.mem_cons, List.not_mem_nil, or_false] <;> omega

variable {l : Launch} {g : Nat}

private theorem alphaForms {t : TState} {f : FloatForm}
    (hf : f ∈ [.subRn .f32, .mul .f32, .setp .f32]) (hp : t.pc ∉ Assumptions.swExp2Sites) :
    IdealAt Assumptions.all f l g t ∧ DeclineAt Assumptions.all f l g t := by
  have hSeg := (Assumptions.numeric_segSites.pc hp)
  have hArith : f ∈ Assumptions.arithScope.float := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_⟩
  · intro op ho result hr
    rw [Assumptions.execLocalA_all_eq_numeric]
    exact (idealAt_head hArith hSeg.tail : IdealAt Assumptions.numeric f l g t) op ho result hr
  · intro op ho hr
    rw [Assumptions.execLocalA_all_eq_numeric]
    apply declineAt_head _ hSeg.tail op ho hr
    intro a ha op ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · apply approxExact_localRule_none
      intro x hx
      rw [approxForm_none_of_float ho] at hx
      cases hx
    · have hLog : Assumptions.lg2Operands op = none := by
        cases op <;> try rfl
        rename_i i
        cases h : i.op <;> simp [Assumptions.lg2Operands, h]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl <;> simp [FloatForm.ofOp, h] at ho
      simp [Assumptions.lg2, hLog]
    · cases op <;> try rfl
      rename_i c
      simp only [FloatForm.ofOp] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> split_ifs at ho <;> cases ho
    · rfl

private theorem alphaEx2Rule {t : TState} (hp : t.pc ∉ Assumptions.swExp2Sites) :
    ApproxAt Assumptions.all (.ex2 .f32) l g t ∧
      ApproxDeclineAt Assumptions.all (.ex2 .f32) l g t := by
  have key (op : Op) (hf : ApproxForm.ofOp op = some (.ex2 .f32)) :
      execLocalA Assumptions.all l g t op =
        (execApproxExact t op).getD (execLocal l g t op) := by
    rw [Assumptions.execLocalA_all_eq_numeric, ((Assumptions.numeric_segSites.pc hp).at rfl).exec]
    have hi : Assumptions.idealArith.localRule l g t op = none :=
      idealReal_localRule_none fun f hf' => by rw [floatForm_none_of_approx hf] at hf'; cases hf'
    have ha : Assumptions.approx.localRule l g t op = execApproxExact t op :=
      approxExact_localRule_of hf (by decide)
    have hl : Assumptions.lg2Operands op = none := by
      cases op <;> try rfl
      rename_i i
      cases he : i.op <;> simp [Assumptions.lg2Operands, he]
      simp [ApproxForm.ofOp, he] at hf
    have hL : Assumptions.lg2.localRule l g t op = none := by simp [Assumptions.lg2, hl]
    have hB : Assumptions.bf16Convert.localRule l g t op = none := by
      cases op <;> try rfl
      cases hf
    simp only [execLocalRule, Assumptions.numeric, List.findSome?_cons, hi, ha, hL, hB]
    cases execApproxExact t op <;> rfl
  exact ⟨fun op hf e he => by rw [key op hf, he]; rfl,
    fun op hf he => by rw [key op hf, he]; rfl⟩

private theorem selectRule {l : Launch} {g d p : Nat} {t : TState} {x y : Opnd} :
    (OItem.selp d x y p).Rule Assumptions.all l g t := by
  intro a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem alphaRules (biased : Bool) :
    ORules Assumptions.all l g (alphaSite biased).pc (alphaSite biased).items := by
  let s := alphaSite biased
  change ORules Assumptions.all l g s.pc s.items
  have off (n : Fin 7) : s.pc + n.val ∉ Assumptions.swExp2Sites := alphaOff biased n.isLt
  change ((_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _) ∧ True)
  refine ⟨⟨maxSeg (off 0), fun t ht => alphaForms (by decide) (ht ▸ off 0)⟩,
    ⟨maxSeg (off 1), fun t ht => alphaForms (by decide) (ht ▸ off 1)⟩,
    ⟨maxSeg (off 2), fun t ht => alphaEx2Rule (ht ▸ off 2)⟩,
    ⟨maxSeg (off 3), fun t ht => alphaForms (by decide) (ht ▸ off 3)⟩,
    ⟨maxSeg (off 4), fun _ _ => selectRule⟩, ⟨maxSeg (off 5), fun _ _ => selectRule⟩,
    ⟨maxSeg (off 6), fun _ _ => selectRule⟩, trivial⟩

private theorem alphaEvaluation (biased : Bool) {scale : ℝ} (hs : 0 < scale)
    {word : Value} (hWord : readEReal .f32 word = some (.ok (scale : EReal)))
    (old candidate : Option ℝ) :
    let s := alphaSite biased
    let V := s.valuesOfWord word old candidate
    let kept := chosenReference scale old candidate
    oReq V s.items = true ∧ oCond V s.items ∧
      oFinal V s.items 7256 = scoreValue kept ∧
      oFinal V s.items s.finite = finiteRefValue kept ∧
      oFinal V s.items s.alpha = alphaWord scale old candidate := by
  have hKeep : keepReference scale old candidate = true → old.isSome = true := by
    cases old <;> simp [keepReference, referenceDelta]
  have hFinite : keepReference scale old candidate = true →
      scoreValue old = finiteRefValue old := by
    intro h
    cases old with
    | none => exact Bool.noConfusion (hKeep h)
    | some x => rfl
  have hWidths (m : Option ℝ) : (finiteRefValue m).bytes = 4 := by
    cases m <;> rfl
  have hFloat (x : ℝ) : (Value.float .f32 x).bytes = 4 := rfl
  have hBits (b : BitVec 64) : (Value.bits 32 b).bytes = 4 := rfl
  cases biased <;>
    simp [alphaSite, AlphaSite.items, AlphaSite.valuesOfWord, oReq, oCond, oFinal, OItem.req,
      OItem.cond, OItem.upd, OItem.vals, opndVal, predOf, isPred, isRegOrF32, okVal, okPred,
      referenceSubOutcome,
      referenceMulOutcomeOfWord old candidate hs hWord, referenceExponentOutcome,
      referenceThresholdOutcome, chosenReference, correctionAlpha, alphaWord, fcmpBase] <;>
    (cases hk : keepReference scale old candidate <;>
      simp [hk, hFinite, hWidths, hFloat, hBits, scoreValue_bytes])

/-- The seven decoded operations choose the unchanged or new reference and write the exact
correction factor consumed by the repeat-round denominator and accumulator. -/
theorem alphaSegmentWithScaleWord {t : TState} (biased : Bool) {scale : ℝ} (hs : 0 < scale)
    (old candidate : Option ℝ) {word : Value}
    (hWord : readEReal .f32 word = some (.ok (scale : EReal))) (ht : At t (alphaSite biased).pc [])
    (hRead : ∀ r ∈ (alphaSite biased).inputs,
      t.regs r = some ((alphaSite biased).valuesOfWord word old candidate r)) :
    let s := alphaSite biased
    ∃ u, run kernel Assumptions.all l g 7 t = some u ∧
      At u (s.pc + 7) [(7256, scoreValue (chosenReference scale old candidate)),
        (s.finite, finiteRefValue (chosenReference scale old candidate)),
        (s.alpha, alphaWord scale old candidate)] ∧
      ∀ r, r ∉ oWrites s.items → u.regs r = t.regs r := by
  let s := alphaSite biased
  let V := s.valuesOfWord word old candidate
  obtain ⟨hReq, hCond, hRef, hFinite, hAlpha⟩ := alphaEvaluation biased hs hWord old candidate
  obtain ⟨u, hRun, hPc, hSub, hAcc, hFault, hFrame, hRegs⟩ :=
    (oRun (K := kernel) (A := Assumptions.all) (L := l) (g := g) s.items V s.inputs t
      (ht.1 ▸ alphaCode biased) ht.2.2.2.1 hRead (alphaReads biased) hReq (alphaLocal biased)
      (ht.1 ▸ alphaRules biased)).1 hCond
  have hLen : s.items.length = 7 := rfl
  have hDef (r : Nat) (hb : r ∈ oWrites s.items) :
      u.regs r = some (oFinal V s.items r) := hRegs r (List.mem_append_left _ hb)
  have hW : 7256 ∈ oWrites s.items ∧ s.finite ∈ oWrites s.items ∧
      s.alpha ∈ oWrites s.items := by
    cases biased <;> decide +kernel
  refine ⟨u, hLen ▸ hRun, ⟨by rw [hPc, ht.1, hLen], hSub.trans ht.2.1, hAcc.trans ht.2.2.1,
    hFault.trans ht.2.2.2.1, ?_⟩, hFrame⟩
  exact ⟨(hDef _ hW.1).trans (congrArg some hRef), (hDef _ hW.2.1).trans (congrArg some hFinite),
    (hDef _ hW.2.2).trans (congrArg some hAlpha), trivial⟩

/-- The same seven local operations retain their frame in a finite recorded prefix. -/
theorem alphaTraceWithScaleWordInPrefix {t : TState} {es : List Event} {ending : Option TState}
    (biased : Bool) {scale : ℝ} (hs : 0 < scale) (old candidate : Option ℝ) {word : Value}
    (hWord : readEReal .f32 word = some (.ok (scale : EReal))) (ht : At t (alphaSite biased).pc [])
    (hRead : ∀ r ∈ (alphaSite biased).inputs,
      t.regs r = some ((alphaSite biased).valuesOfWord word old candidate r))
    (hr : Run kernel Assumptions.all l g t es ending) (hMore : es ≠ []) :
    let s := alphaSite biased
    ∃ u, At u (s.pc + 7) [(7256, scoreValue (chosenReference scale old candidate)),
      (s.finite, finiteRefValue (chosenReference scale old candidate)),
      (s.alpha, alphaWord scale old candidate)] ∧ Run kernel Assumptions.all l g u es ending ∧
      ∀ r, r ∉ oWrites s.items → u.regs r = t.regs r := by
  obtain ⟨u,hLocal,hu,hFrame⟩ := alphaSegmentWithScaleWord biased hs old candidate hWord ht hRead
  exact ⟨u,hu,hr.after_local_nonempty (run_rtg hLocal) hMore,hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
