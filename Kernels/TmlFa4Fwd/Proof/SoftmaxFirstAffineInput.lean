-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMaskMaximum
public import Kernels.TmlFa4Fwd.Proof.SoftmaxReference
public import Lemmas.Flow.FloatRun
public import Lemmas.Flow.SplitJoin
import Kernels.TmlFa4Fwd.Flow.Code.Part068

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

private def firstNegInstr : FloatInstr :=
  { op := .neg, ty := ⟨.f32, 1⟩, dsts := [some 1230], srcs := [.reg 7132] }

private theorem firstNegScale {l : Launch} {g : Nat} {t : TState} {word : Nat} {q : ℚ}
    (hword : word < 2^32) (hDec : FloatFmt.f32.layout.decode word = some (.fin q))
    (ht : At t 4398 []) (hs : t.regs 7132 = some (b32 word)) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t 1230 (fl (-(q : ℝ))))) := by
  apply run_local Flow.code_4398 rfl ht
  rw [Assumptions.execLocalA_all_eq_numeric]
  have hOff : t.pc ∉ Assumptions.swExp2Sites := ht.1 ▸ (by decide)
  have hSeg : SegFreeAt Assumptions.numeric l g t :=
    (Assumptions.numeric_segSites.pc hOff).at rfl
  have hNone : ∀ a ∈ Assumptions.numeric, a.localRule l g t (.float firstNegInstr) = none := by
    intro a ha
    simp only [Assumptions.numeric, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rfl
  change execLocalA Assumptions.numeric l g t (.float firstNegInstr) = _
  rw [hSeg.exec, execLocalRule_of_none hNone]
  have hClass : classify .f32 (b32 word) = .ok (.fin q) :=
    classify_bits (by omega) hDec
  change execFloat l g t firstNegInstr = _
  simp [execFloat, firstNegInstr, FloatInstr.lane, FloatInstr.ieee, FloatInstr.flushIn,
    FVal.negate, FVal.toValue, floatLane, hs, readValue, readReg, hClass, fl, bind, Except.bind,
    pure, Except.pure, boolCombine, FloatInstr.rule, Rat.cast_neg]

private theorem firstMultiplyRef {l : Launch} {g : Nat} {t : TState} (mx : Option ℝ)
    (scale : ℝ) (ht : At t 4399 []) (hm : t.regs 3685 = some (finiteRefValue mx))
    (hs : t.regs 1230 = some (fl (-scale))) :
    run kernel Assumptions.all l g 1 t =
      some (next (setReg t 3686 (fl (-(scale * mx.getD 0))))) := by
  apply run_local Flow.code_4399 rfl ht
  have hm' : valFloat .f32 (finiteRefValue mx) = .ok (mx.getD 0) := by
    cases mx with
    | none =>
      change valFloat .f32 (b32 0) = .ok (0 : ℝ)
      simpa using valFloat_b32 (by decide) (by decide : f32Value 0 = some 0)
    | some x => rfl
  have hOff : t.pc ∉ Assumptions.swExp2Sites := ht.1 ▸ (by decide)
  rw [Assumptions.execLocalA_all_eq_numeric]
  have hModel : IdealAt Assumptions.numeric (.mul .f32) l g t :=
    idealAt_head (by decide) (Assumptions.numeric_segSites.pc hOff).tail
  have hMul := exec_fmul (d := 3686) hModel hm hs hm'
    (show valFloat .f32 (fl (-scale)) = .ok (-scale) by rfl)
  rw [show -(scale * mx.getD 0) = mx.getD 0 * (-scale) by ring]
  exact hMul

private theorem firstAffinePack {l : Launch} {g pc d a b : Nat} {t : TState}
    {x y : Value}
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.pack, .int .b 64, [some d],
      [.reg a, .reg b]⟩⟩)
    (hOff : pc ∉ Assumptions.swExp2Sites) (ht : At t pc [])
    (ha : t.regs a = some x) (hb : t.regs b = some y) (hx : x.bytes = 4) (hy : y.bytes = 4) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t d (joinValue x y))) := by
  apply run_local hc rfl ht
  rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (ht.1 ▸ hOff) rfl]
  change execMove l g t (.move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩) = _
  simp [execMove, readValue, readReg, ha, hb, hx, hy, DType.width, bind, Except.bind,
    pure, Except.pure]

private theorem splitScalePacked {bits : Nat} (hb : bits < 2^32) :
    splitValue 64 (joinValue (b32 bits) (b32 bits)) = (b32 bits, b32 bits) := by
  exact split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact hb)

private theorem firstScaleDecode {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    ∃ q : ℚ, p.scaleLog2Bits < 2^32 ∧
      FloatFmt.f32.layout.decode p.scaleLog2Bits = some (.fin q) ∧
      abiFloat p.scaleLog2Bits = (q : ℝ) ∧
      valFloat .f32 (b32 p.scaleLog2Bits) = .ok (q : ℝ) := by
  have hMem : (12, p.scaleLog2Bits) ∈ p.scalarWords := by
    simp [Params.scalarWords]
  have hBits := (hp.values _ hMem).1
  obtain ⟨q, _, hq, _, hPos, _⟩ := hp.scales
  have hv := valFloat_b32 (by omega) hq
  have hAbi : abiFloat p.scaleLog2Bits = (q : ℝ) := by simp [abiFloat, hq]
  rw [f32Value, FloatFmt.decode, Option.bind_eq_some_iff] at hq
  obtain ⟨x, hDec, hNum⟩ := hq
  cases x with
  | fin k =>
    have hk : k = q := Option.some.inj hNum
    subst k
    exact ⟨q, hBits, hDec, hAbi, hv⟩
  | zero z =>
    have hz : q = 0 := (Option.some.inj hNum).symm
    exact (lt_irrefl _ (hz ▸ hPos)).elim
  | inf z => cases hNum
  | nan z => cases hNum

variable {p : Params} {l : Launch} {m : Mem0}

/-- The five local instructions after the first statistics notification prepare the
offset, the first score pair and the scale for the affine shift. -/
theorem firstAffineFrameWithNegScaleLocal (hp : Pre p l m) {g : Nat} {t : TState} (mx : Option ℝ)
    (ht : At t 4398 []) (hm : t.regs 3685 = some (finiteRefValue mx))
    (hs : t.regs 7132 = some (b32 p.scaleLog2Bits)) (a b : Option ℝ)
    (ha : t.regs 3240 = some (scoreValue a)) (hb : t.regs 3242 = some (scoreValue b)) :
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale * mx.getD 0
    ∃ u, At u 4403 [(8025, joinValue (scoreValue a) (scoreValue b))] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      readERealPair l g u (.reg 8026) = some (.ok ((scale : EReal), (scale : EReal))) ∧
      readERealPair l g u (.reg 8024) =
        some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))) ∧
      (∀ r ∉ [1230, 3686, 8024, 8025, 8026], u.regs r = t.regs r) ∧
      u.regs 1230 = some (fl (-scale)) := by
  obtain ⟨q, hBits, hDec, hScale, hRead⟩ := firstScaleDecode hp
  let scale := abiFloat p.scaleLog2Bits
  let ref := scale * mx.getD 0
  let offset := fl (-ref)
  let scaleWord := b32 p.scaleLog2Bits
  let scorePair := joinValue (scoreValue a) (scoreValue b)
  let t₁ := next (setReg t 1230 (fl (-scale)))
  let t₂ := next (setReg t₁ 3686 offset)
  let t₃ := next (setReg t₂ 8024 (joinValue offset offset))
  let t₄ := next (setReg t₃ 8025 scorePair)
  let u := next (setReg t₄ 8026 (joinValue scaleWord scaleWord))
  have h₁ : run kernel Assumptions.all l g 1 t = some t₁ := by
    simpa only [t₁, scale, hScale] using firstNegScale hBits hDec ht hs
  have ht₁ : At t₁ 4399 [] := (ht.set (r := 1230) (v := fl (-scale)) (by simp)).mono trivial
  have h₂ : run kernel Assumptions.all l g 1 t₁ = some t₂ :=
    firstMultiplyRef mx scale ht₁
      (by simpa [t₁, next, setReg] using hm) (by simp [t₁, next, setReg])
  have ht₂ : At t₂ 4400 [] := (ht₁.set (r := 3686) (v := offset) (by simp)).mono trivial
  have ht₃ : At t₃ 4401 [] :=
    (ht₂.set (r := 8024) (v := joinValue offset offset) (by simp)).mono trivial
  have ht₄ : At t₄ 4402 [] := (ht₃.set (r := 8025) (v := scorePair) (by simp)).mono trivial
  have hO : t₂.regs 3686 = some offset := by simp [t₂, next, setReg]
  have h₃ : run kernel Assumptions.all l g 1 t₂ = some t₃ :=
    firstAffinePack Flow.code_4400 (by decide) ht₂ hO hO rfl rfl
  have h₄ : run kernel Assumptions.all l g 1 t₃ = some t₄ :=
    firstAffinePack Flow.code_4401 (by decide) ht₃
      (by simpa [t₃, t₂, t₁, next, setReg] using ha)
      (by simpa [t₃, t₂, t₁, next, setReg] using hb)
      (scoreValue_bytes a) (scoreValue_bytes b)
  have hS : t₄.regs 7132 = some scaleWord := by
    simpa [t₄, t₃, t₂, t₁, scaleWord, next, setReg] using hs
  have h₅ : run kernel Assumptions.all l g 1 t₄ = some u :=
    firstAffinePack Flow.code_4402 (by decide) ht₄ hS hS rfl rfl
  have hFull := run_comp (run_comp (run_comp (run_comp h₁ h₂) h₃) h₄) h₅
  have hAt : At u 4403 [] :=
    (ht₄.set (r := 8026) (v := joinValue scaleWord scaleWord) (by simp)).mono trivial
  have hPair : u.regs 8025 = some scorePair := by simp [u, t₄, next, setReg]
  have hPackedScale : u.regs 8026 = some (joinValue scaleWord scaleWord) := by
    simp [u, next, setReg]
  have hPackedOffset : u.regs 8024 = some (joinValue offset offset) := by
    simp [u, t₄, t₃, next, setReg]
  have hvScale : valFloat .f32 scaleWord = .ok scale := by simpa [hScale, scale] using hRead
  have hPairScale : splitValue 64 (joinValue scaleWord scaleWord) = (scaleWord, scaleWord) :=
    splitScalePacked hBits
  refine ⟨u, hAt.mono ⟨hPair, trivial⟩, run_rtg hFull,
    readERealPair_reg hPackedScale (by rw [hPairScale]; exact hvScale)
      (by rw [hPairScale]; exact hvScale), readERealPair_reg hPackedOffset rfl rfl, ?_,?_⟩
  · intro r hr'
    have hn (r' : Nat) (hm : r' ∈ [1230, 3686, 8024, 8025, 8026]) : r ≠ r' := by
      intro h
      exact hr' (h.symm ▸ hm)
    have h0 := hn 1230 (by decide)
    have h1 := hn 3686 (by decide)
    have h2 := hn 8024 (by decide)
    have h3 := hn 8025 (by decide)
    have h4 := hn 8026 (by decide)
    simp only [u, t₄, t₃, t₂, t₁, next, setReg]
    rw [Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
      Function.update_of_ne h1, Function.update_of_ne h0]
  · simp [u,t₄,t₃,t₂,t₁,next,setReg,scale]

theorem firstAffineFrameLocal (hp : Pre p l m) {g : Nat} {t : TState} (mx : Option ℝ)
    (ht : At t 4398 []) (hm : t.regs 3685 = some (finiteRefValue mx))
    (hs : t.regs 7132 = some (b32 p.scaleLog2Bits)) (a b : Option ℝ)
    (ha : t.regs 3240 = some (scoreValue a)) (hb : t.regs 3242 = some (scoreValue b)) :
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale * mx.getD 0
    ∃ u, At u 4403 [(8025, joinValue (scoreValue a) (scoreValue b))] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      readERealPair l g u (.reg 8026) = some (.ok ((scale : EReal), (scale : EReal))) ∧
      readERealPair l g u (.reg 8024) =
        some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))) ∧
      ∀ r ∉ [1230, 3686, 8024, 8025, 8026], u.regs r = t.regs r := by
  obtain ⟨u,hu,hPath,hScale,hOff,hFrame,_⟩ := firstAffineFrameWithNegScaleLocal hp mx ht hm hs
    a b ha hb
  exact ⟨u,hu,hPath,hScale,hOff,hFrame⟩

theorem firstAffineFrameInPrefix (hp : Pre p l m) {g : Nat} {t : TState} {es : List Event}
    {ending : Option TState} (mx : Option ℝ) (ht : At t 4398 [])
    (hm : t.regs 3685 = some (finiteRefValue mx)) (hs : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (a b : Option ℝ) (ha : t.regs 3240 = some (scoreValue a))
    (hb : t.regs 3242 = some (scoreValue b)) (hr : Run kernel Assumptions.all l g t es ending)
    (hne : es ≠ []) :
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale * mx.getD 0
    ∃ u, At u 4403 [(8025, joinValue (scoreValue a) (scoreValue b))] ∧
      Run kernel Assumptions.all l g u es ending ∧
      readERealPair l g u (.reg 8026) = some (.ok ((scale : EReal), (scale : EReal))) ∧
      readERealPair l g u (.reg 8024) =
        some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))) ∧
      ∀ r ∉ [1230, 3686, 8024, 8025, 8026], u.regs r = t.regs r := by
  obtain ⟨u,hU,hLocal,hScale,hOffset,hFrame⟩ := firstAffineFrameLocal hp mx ht hm hs a b ha hb
  exact ⟨u,hU,hr.after_local_nonempty hLocal hne,hScale,hOffset,hFrame⟩

/-- The shift sees exactly the same masked scores consumed by the row maximum. -/
def firstShiftLogits (score : Nat → Option ℝ) (it : FmaItem) : Option ℝ × Option ℝ :=
  (score (it.x - 3687), score (it.y - 3687))

/-- The five local instructions after the first statistics notification prepare the
offset, the first score pair and the scale for the affine shift. -/
theorem firstAffineFrame (hp : Pre p l m) {g : Nat} {t : TState} {es : List Event} (mx : Option ℝ)
    (ht : At t 4398 []) (hm : t.regs 3685 = some (finiteRefValue mx))
    (hs : t.regs 7132 = some (b32 p.scaleLog2Bits)) (a b : Option ℝ)
    (ha : t.regs 3240 = some (scoreValue a)) (hb : t.regs 3242 = some (scoreValue b))
    (hr : Run kernel Assumptions.all l g t es none) :
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale * mx.getD 0
    ∃ u, At u 4403 [(8025, joinValue (scoreValue a) (scoreValue b))] ∧
      Run kernel Assumptions.all l g u es none ∧
      readERealPair l g u (.reg 8026) = some (.ok ((scale : EReal), (scale : EReal))) ∧
      readERealPair l g u (.reg 8024) =
        some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))) ∧
      ∀ r ∉ [1230, 3686, 8024, 8025, 8026], u.regs r = t.regs r := by
  refine firstAffineFrameInPrefix hp mx ht hm hs a b ha hb hr ?_
  intro hEmpty
  rw [hEmpty] at hr
  cases hr

def firstShiftValues (t : TState) (r : Nat) : Value := (t.regs r).getD (.pred false)

private def firstShiftInputB (it : FmaItem) : Bool :=
  match it.pk with
  | none => it.a == 8025 && it.x == 3687 && it.y == 3688
  | some (lo, hi) => decide (it.x - 3687 < 128) && decide (it.y - 3687 < 128) &&
    lo == firstMaskScalarReg (it.x - 3687) && hi == firstMaskScalarReg (it.y - 3687)

private theorem firstShiftInputChecked : (shiftItems 0).all firstShiftInputB = true := by
  decide +kernel

private theorem firstPrepareInputs {t : TState} (score : Nat → Option ℝ)
    (hs : ∀ group : Fin 4, firstMaskOutputs t group score)
    (hFirst : t.regs 8025 = some (joinValue (scoreValue (score 0)) (scoreValue (score 1)))) :
    (∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, t.regs r = some (firstShiftValues t r)) ∧
    ∀ it ∈ shiftItems 0, it.packOk (firstShiftValues t) = true ∧
      it.src (firstShiftValues t) =
        joinValue (scoreValue (firstShiftLogits score it).1)
          (scoreValue (firstShiftLogits score it).2) := by
  have hRead : ∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, (t.regs r).isSome := by
    intro it hi r hr
    have h := List.all_eq_true.mp firstShiftInputChecked it hi
    cases hpk : it.pk with
    | none =>
      simp only [firstShiftInputB, hpk, Bool.and_eq_true, beq_iff_eq] at h
      simp only [FmaItem.reads, hpk, List.mem_singleton] at hr
      rw [hr, h.1.1, hFirst]
      rfl
    | some pair =>
      obtain ⟨lo, hi'⟩ := pair
      simp only [firstShiftInputB, hpk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      simp only [FmaItem.reads, hpk, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.2, firstMaskOutputColumn hs h.1.1.1]
        rfl
      · rw [h.2, firstMaskOutputColumn hs h.1.1.2]
        rfl
  refine ⟨fun it hi r hr => ?_, fun it hi => ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hRead it hi r hr)
    simp [firstShiftValues, hv]
  · have h := List.all_eq_true.mp firstShiftInputChecked it hi
    cases hpk : it.pk with
    | none =>
      simp only [firstShiftInputB, hpk, Bool.and_eq_true, beq_iff_eq] at h
      simp [FmaItem.packOk, FmaItem.src, hpk, firstShiftValues, firstShiftLogits, h.1.1,
        h.1.2, h.2, hFirst]
    | some pair =>
      obtain ⟨lo, hi'⟩ := pair
      simp only [firstShiftInputB, hpk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      have hLo := firstMaskOutputColumn hs h.1.1.1
      have hHi := firstMaskOutputColumn hs h.1.1.2
      simp [FmaItem.packOk, FmaItem.src, hpk, firstShiftValues, firstShiftLogits, h.1.2, h.2,
        hLo, hHi, scoreValue_bytes]

/-- From the first row maximum, the decoded program emits the statistics notification and
enters its affine shift with all 128 masked sources, its scale, and its finite offset. -/
theorem firstShiftInputTrace {X : Execution} (hp : Pre p l m) (warp : Fin 8) {g j : Nat}
    {t : TState} (score : Nat → Option ℝ) (ht : At t 4329 [])
    (hs : ∀ group : Fin 4, firstMaskOutputs t group score)
    (hScaleWord : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (hBar : t.regs 5127 = some (b32 (3 + warp.val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let mx := scoreMax score (List.range 128)
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale * mx.getD 0
    ∃ u, At u 4403 [] ∧
      X.get (g, j) = some ⟨4397, .bar (3 + warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+1)) none ∧
      readERealPair l g u (.reg 8026) = some (.ok ((scale : EReal), (scale : EReal))) ∧
      readERealPair l g u (.reg 8024) =
        some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))) ∧
      (∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, u.regs r = some (firstShiftValues u r)) ∧
      (∀ it ∈ shiftItems 0, it.packOk (firstShiftValues u) = true ∧
        it.src (firstShiftValues u) =
          joinValue (scoreValue (firstShiftLogits score it).1)
            (scoreValue (firstShiftLogits score it).2)) ∧
      u.regs 7256 = some (scoreValue mx) ∧
      ∀ r ∉ (rWrites (firstMaxItems.map MaxItem.item) ++ [622, 3685, 1230, 3686, 8024, 8025, 8026]),
        u.regs r = t.regs r := by
  let mx := scoreMax score (List.range 128)
  obtain ⟨s, hsAt, hsRun, hsScore, hsFrame⟩ := firstMaskedMaxTrace score ht hs hRun
  obtain ⟨v, hvAt, hvRun, hvFrame⟩ :=
    finiteReferenceTrace .first mx (hsAt.mono trivial) hsAt.2.2.2.2.1 hsRun
  have hBarV : v.regs 5127 = some (b32 (3 + warp.val)) :=
    (hvFrame _ (by decide)).trans ((hsFrame _ (by decide +kernel)).trans hBar)
  obtain ⟨hEvent, hTail⟩ := statsTrace hp.block (some .first) warp hvAt.1 hvAt.2.2.2.1 hBarV hvRun
  have hnAt : At (next v) 4398 [] := (hvAt.next).mono trivial
  have hnScale : (next v).regs 7132 = some (b32 p.scaleLog2Bits) :=
    (hvFrame _ (by decide)).trans ((hsFrame _ (by decide +kernel)).trans hScaleWord)
  have hvScore : ∀ group : Fin 4, firstMaskOutputs (next v) group score := by
    intro group pair hPair
    have hGroup := group.isLt
    obtain ⟨hLo, hHi⟩ := hsScore group pair hPair
    have hNotLo : (firstMaskPairRegs group pair).low ∉ [3685, 622] := by
      simp only [firstMaskPairRegs, maskScratch, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      omega
    have hNotHi : (firstMaskPairRegs group pair).high ∉ [3685, 622] := by
      simp only [firstMaskPairRegs, maskScratch, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      split <;> omega
    exact ⟨(hvFrame _ hNotLo).trans hLo, (hvFrame _ hNotHi).trans hHi⟩
  obtain ⟨u, hu, huRun, hScale, hOff, hKeep⟩ :=
    firstAffineFrame hp mx hnAt hvAt.2.2.2.2.1 hnScale (score 0) (score 1)
      (firstMaskOutputColumn hvScore (by decide : 0 < 128))
      (firstMaskOutputColumn hvScore (by decide : 1 < 128)) hTail
  have huScore : ∀ group : Fin 4, firstMaskOutputs u group score := by
    intro group pair hPair
    have hGroup := group.isLt
    obtain ⟨hLo, hHi⟩ := hvScore group pair hPair
    have hNotLo : (firstMaskPairRegs group pair).low ∉ [1230, 3686, 8024, 8025, 8026] := by
      simp only [firstMaskPairRegs, maskScratch, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      omega
    have hNotHi : (firstMaskPairRegs group pair).high ∉ [1230, 3686, 8024, 8025, 8026] := by
      simp only [firstMaskPairRegs, maskScratch, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      split <;> omega
    exact ⟨(hKeep _ hNotLo).trans hLo, (hKeep _ hNotHi).trans hHi⟩
  obtain ⟨hRead, hSource⟩ := firstPrepareInputs score huScore hu.2.2.2.2.1
  refine ⟨u, hu.mono trivial, hEvent, huRun, hScale, hOff, hRead, hSource,
    (hKeep _ (by decide)).trans hvAt.2.2.2.2.2.1, ?_⟩
  intro r hNo
  have hN1 : r ∉ rWrites (firstMaxItems.map MaxItem.item) :=
    fun hm => hNo (List.mem_append_left _ hm)
  have hN2 : r ∉ [3685, 622] := fun hm => hNo (List.mem_append_right _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    tauto))
  have hN3 : r ∉ [1230, 3686, 8024, 8025, 8026] := fun hm => hNo (List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))
  exact (hKeep r hN3).trans ((hvFrame r hN2).trans (hsFrame r hN1))

/-- From the first row maximum, the decoded program emits the statistics notification and
enters its affine shift with all 128 masked sources, its scale, and its finite offset. -/
theorem firstShiftInputInPrefix {X : Execution} (hp : Pre p l m) (warp : Fin 8) {g j : Nat}
    {t : TState} (score : Nat → Option ℝ) {ending : Option TState} (ht : At t 4329 [])
    (hs : ∀ group : Fin 4, firstMaskOutputs t group score)
    (hScaleWord : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (hBar : t.regs 5127 = some (b32 (3 + warp.val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hLater : j+1 < (X.tr g).length) :
    let mx := scoreMax score (List.range 128)
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale * mx.getD 0
    ∃ u, At u 4403 [] ∧
      X.get (g, j) = some ⟨4397, .bar (3 + warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+1)) ending ∧
      readERealPair l g u (.reg 8026) = some (.ok ((scale : EReal), (scale : EReal))) ∧
      readERealPair l g u (.reg 8024) =
        some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))) ∧
      (∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, u.regs r = some (firstShiftValues u r)) ∧
      (∀ it ∈ shiftItems 0, it.packOk (firstShiftValues u) = true ∧
        it.src (firstShiftValues u) =
          joinValue (scoreValue (firstShiftLogits score it).1)
            (scoreValue (firstShiftLogits score it).2)) ∧
      u.regs 7256 = some (scoreValue mx) ∧
      ∀ r ∉ (rWrites (firstMaxItems.map MaxItem.item) ++ [622, 3685, 1230, 3686, 8024, 8025, 8026]),
        u.regs r = t.regs r := by
  let mx := scoreMax score (List.range 128)
  have hNonempty (index : Nat) (hi : index < (X.tr g).length) :
      (X.tr g).drop index ≠ [] := by
    intro he
    have hz := congrArg List.length he
    simp only [List.length_drop,List.length_nil] at hz
    omega
  have hNow := hNonempty j (by omega)
  have hAfter := hNonempty (j+1) hLater
  obtain ⟨s, hsAt, hsRun, hsScore, hsFrame⟩ := firstMaskedMaxInPrefix score ht hs hRun hNow
  obtain ⟨v, hvAt, hvRun, hvFrame⟩ :=
    finiteReferenceInPrefix .first mx (hsAt.mono trivial) hsAt.2.2.2.2.1 hsRun hNow
  have hBarV : v.regs 5127 = some (b32 (3 + warp.val)) :=
    (hvFrame _ (by decide)).trans ((hsFrame _ (by decide +kernel)).trans hBar)
  obtain ⟨hEvent, hTail⟩ :=
    statsTracePrefix hp.block (some .first) warp hvAt.1 hvAt.2.2.2.1 hBarV hvRun hNow
  have hnAt : At (next v) 4398 [] := (hvAt.next).mono trivial
  have hnScale : (next v).regs 7132 = some (b32 p.scaleLog2Bits) :=
    (hvFrame _ (by decide)).trans ((hsFrame _ (by decide +kernel)).trans hScaleWord)
  have hvScore : ∀ group : Fin 4, firstMaskOutputs (next v) group score := by
    intro group pair hPair
    have hGroup := group.isLt
    obtain ⟨hLo, hHi⟩ := hsScore group pair hPair
    have hNotLo : (firstMaskPairRegs group pair).low ∉ [3685, 622] := by
      simp only [firstMaskPairRegs, maskScratch, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      omega
    have hNotHi : (firstMaskPairRegs group pair).high ∉ [3685, 622] := by
      simp only [firstMaskPairRegs, maskScratch, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      split <;> omega
    exact ⟨(hvFrame _ hNotLo).trans hLo, (hvFrame _ hNotHi).trans hHi⟩
  obtain ⟨u, hu, huRun, hScale, hOff, hKeep⟩ :=
    firstAffineFrameInPrefix hp mx hnAt hvAt.2.2.2.2.1 hnScale (score 0) (score 1)
      (firstMaskOutputColumn hvScore (by decide : 0 < 128))
      (firstMaskOutputColumn hvScore (by decide : 1 < 128)) hTail hAfter
  have huScore : ∀ group : Fin 4, firstMaskOutputs u group score := by
    intro group pair hPair
    have hGroup := group.isLt
    obtain ⟨hLo, hHi⟩ := hvScore group pair hPair
    have hNotLo : (firstMaskPairRegs group pair).low ∉ [1230, 3686, 8024, 8025, 8026] := by
      simp only [firstMaskPairRegs, maskScratch, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      omega
    have hNotHi : (firstMaskPairRegs group pair).high ∉ [1230, 3686, 8024, 8025, 8026] := by
      simp only [firstMaskPairRegs, maskScratch, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      split <;> omega
    exact ⟨(hKeep _ hNotLo).trans hLo, (hKeep _ hNotHi).trans hHi⟩
  obtain ⟨hRead, hSource⟩ := firstPrepareInputs score huScore hu.2.2.2.2.1
  refine ⟨u, hu.mono trivial, hEvent, huRun, hScale, hOff, hRead, hSource,
    (hKeep _ (by decide)).trans hvAt.2.2.2.2.2.1, ?_⟩
  intro r hNo
  have hN1 : r ∉ rWrites (firstMaxItems.map MaxItem.item) :=
    fun hm => hNo (List.mem_append_left _ hm)
  have hN2 : r ∉ [3685, 622] := fun hm => hNo (List.mem_append_right _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    tauto))
  have hN3 : r ∉ [1230, 3686, 8024, 8025, 8026] := fun hm => hNo (List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))
  exact (hKeep r hN3).trans ((hvFrame r hN2).trans (hsFrame r hN1))

/-- A recorded first statistics arrival preserves the local inputs needed by the initial
affine shift, even if the actual trace has not recorded any following event yet. -/
theorem firstShiftAfterStatsWithNegScaleLocal (hp : Pre p l m) {g : Nat} {t : TState}
    (score : Nat → Option ℝ) (ht : At t 4398 [])
    (hs : ∀ group : Fin 4, firstMaskOutputs t group score)
    (hFinite : t.regs 3685 = some (finiteRefValue (scoreMax score (List.range 128))))
    (hScaleWord : t.regs 7132 = some (b32 p.scaleLog2Bits)) :
    let mx := scoreMax score (List.range 128)
    let scale := abiFloat p.scaleLog2Bits
    let reference := scale * mx.getD 0
    ∃ u, At u 4403 [] ∧
      readERealPair l g u (.reg 8026) = some (.ok ((scale : EReal), (scale : EReal))) ∧
      readERealPair l g u (.reg 8024) =
        some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))) ∧
      (∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, u.regs r = some (firstShiftValues u r)) ∧
      (∀ it ∈ shiftItems 0, it.packOk (firstShiftValues u) = true ∧
        it.src (firstShiftValues u) =
          joinValue (scoreValue (firstShiftLogits score it).1)
            (scoreValue (firstShiftLogits score it).2)) ∧
      (∀ r ∉ [1230,3686,8024,8025,8026], u.regs r = t.regs r) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      u.regs 1230 = some (fl (-scale)) := by
  obtain ⟨u,hu,hLocal,hScale,hOff,hKeep,hNeg⟩ :=
    firstAffineFrameWithNegScaleLocal hp _ ht hFinite hScaleWord (score 0) (score 1)
      (firstMaskOutputColumn hs (by decide : 0 < 128))
      (firstMaskOutputColumn hs (by decide : 1 < 128))
  have huScore : ∀ group : Fin 4, firstMaskOutputs u group score := by
    intro group pair hPair
    have hGroup := group.isLt
    obtain ⟨hLo,hHi⟩ := hs group pair hPair
    have hNotLo : (firstMaskPairRegs group pair).low ∉ [1230,3686,8024,8025,8026] := by
      simp only [firstMaskPairRegs,maskScratch,List.mem_cons,List.not_mem_nil,or_false,not_or]
      omega
    have hNotHi : (firstMaskPairRegs group pair).high ∉ [1230,3686,8024,8025,8026] := by
      simp only [firstMaskPairRegs,maskScratch,List.mem_cons,List.not_mem_nil,or_false,not_or]
      split <;> omega
    exact ⟨(hKeep _ hNotLo).trans hLo,(hKeep _ hNotHi).trans hHi⟩
  obtain ⟨hRead,hSource⟩ := firstPrepareInputs score huScore hu.2.2.2.2.1
  exact ⟨u,hu.mono trivial,hScale,hOff,hRead,hSource,hKeep,hLocal,hNeg⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
