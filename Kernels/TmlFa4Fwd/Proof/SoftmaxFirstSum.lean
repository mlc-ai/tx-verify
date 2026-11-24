-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstNumeric
import Kernels.TmlFa4Fwd.Flow.Code.Part078

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

private def add2 (d a b : Nat) : Op :=
  .float { op := .add, ty := ⟨.f32, 2⟩, rnd := some .rn, dsts := [some d],
           srcs := [.reg a, .reg b] }

private def add1 (d a b : Nat) : Op :=
  .float { op := .add, ty := ⟨.f32, 1⟩, dsts := [some d], srcs := [.reg a, .reg b] }

private theorem idealSum {x y : ℝ} :
    addEReal (x : EReal) (y : EReal) = some ((x + y : ℝ) : EReal) := by
  simp [addEReal]

private theorem idealValue (x : ℝ) : erealValue .f32 (x : EReal) = fl x := by
  simp [erealValue, fl]

private theorem execAdd2 {l : Launch} {g : Nat} {t : TState} {d a b : Nat}
    {x y u v : ℝ} (hI : IdealAt Assumptions.numeric .addRnF32x2 l g t)
    (ha : t.regs a = some (.pair (fl x) (fl y)))
    (hb : t.regs b = some (.pair (fl u) (fl v))) :
    execLocalA Assumptions.all l g t (add2 d a b) =
      .ok (next (setReg t d (.pair (fl (x + u)) (fl (y + v))))) := by
  have hA := readERealPair_reg (L := l) (g := g) (x0 := x) (x1 := y) ha rfl rfl
  have hB := readERealPair_reg (L := l) (g := g) (x0 := u) (x1 := v) hb rfl rfl
  rw [Assumptions.execLocalA_all_eq_numeric]
  apply hI _ rfl
  simp only [add2, execIdealFloat, hA, hB, bindRead, idealSum, idealValue, pure, Except.pure]

private theorem execAdd1 {l : Launch} {g : Nat} {t : TState} {d a b : Nat}
    {x y : ℝ} (hI : IdealAt Assumptions.numeric (.add .f32) l g t)
    (ha : t.regs a = some (fl x)) (hb : t.regs b = some (fl y)) :
    execLocalA Assumptions.all l g t (add1 d a b) =
      .ok (next (setReg t d (fl (x + y)))) := by
  have hA : readERealOpnd t .f32 (.reg a) = some (.ok (x : EReal)) :=
    (readERealOpnd_reg ha).trans rfl
  have hB : readERealOpnd t .f32 (.reg b) = some (.ok (y : EReal)) :=
    (readERealOpnd_reg hb).trans rfl
  rw [Assumptions.execLocalA_all_eq_numeric]
  apply hI _ rfl
  simp only [add1, execIdealFloat, hA, hB, bindRead, idealSum, idealValue, pure, Except.pure,
    Option.map_some]

/-- The reduction records which columns contribute to each of its packed accumulators. -/
private inductive SumStep
  | pack (dst columnPair : Nat)
  | add (dst left right : Nat)

private def SumStep.dst : SumStep → Nat
  | .pack d _ | .add d _ _ => d

private def SumStep.op : SumStep → Op
  | .pack d k => .move ⟨.pack, .int .b 64, [some d], [.reg (1231 + 2 * k), .reg (1232 + 2 * k)]⟩
  | .add d a b => add2 d a b

private def sumSteps : List SumStep :=
  (List.range 5).map (fun k => .pack (8188 + k) k) ++
    (List.range 59).flatMap (fun k =>
      [.add (8193 + 2 * k) (if k < 4 then 8188 + k else 8193 + 2 * (k - 4))
        (8192 + 2 * k), .pack (8194 + 2 * k) (k + 5)]) ++
    [.add 8311 8303 8310, .add 8312 8305 8307, .add 8313 8309 8311, .add 8314 8312 8313]

private def SumStep.checked (step : SumStep) (pc : Nat) : Bool :=
  match kernel.code[pc]?, step with
  | some ⟨none, .move m⟩, .pack d k =>
    decide (m = ⟨.pack, .int .b 64, [some d], [.reg (1231 + 2 * k), .reg (1232 + 2 * k)]⟩)
  | some ⟨none, .float f⟩, .add d a b =>
    decide (f = { op := .add, ty := ⟨.f32, 2⟩, rnd := some .rn, dsts := [some d],
                  srcs := [.reg a, .reg b] })
  | _, _ => false

private theorem SumStep.checked_code {step : SumStep} {pc : Nat}
    (h : step.checked pc = true) : kernel.code[pc]? = some ⟨none, step.op⟩ := by
  unfold checked at h
  split at h
  · rename_i m d k hc
    rw [hc, of_decide_eq_true h]
    rfl
  · rename_i f d a b hc
    rw [hc, of_decide_eq_true h]
    rfl
  · cases h

set_option maxRecDepth 100000 in
private theorem sumStepsChecked :
    sumSteps.zipIdx.all (fun (step, idx) => step.checked (4877 + idx)) = true := by
  kernel_rfl

private abbrev Contributors := List Nat × List Nat
private abbrev Reduction := Nat → Option Contributors

private def SumStep.columns (st : SumStep) (s : Reduction) : Option Reduction := do
  match st with
  | .pack d k =>
    if k < 64 ∧ 1358 < d then
      some (Function.update s d (some ([2 * k], [2 * k + 1])))
    else none
  | .add d a b =>
    if 1358 < d then
      let p ← s a
      let q ← s b
      some (Function.update s d (some (p.1 ++ q.1, p.2 ++ q.2)))
    else none

private def reducedColumns : Option Contributors := do
  let s ← sumSteps.foldlM (fun s step => step.columns s) (fun _ => none)
  s 8314

set_option maxRecDepth 100000 in
private theorem packedColumns :
    reducedColumns.isSome = true ∧
      (reducedColumns.map (fun (a, b) => (a ++ b).isPerm (List.range 128))).getD false = true := by
  constructor <;> kernel_rfl

private def columnSum (weights : Nat → ℝ) (cols : List Nat) : ℝ :=
  (cols.map weights).sum

private theorem columnSum_append (weights : Nat → ℝ) (a b : List Nat) :
    columnSum weights (a ++ b) = columnSum weights a + columnSum weights b := by
  simp [columnSum]

private def pairSum (weights : Nat → ℝ) (p : Contributors) : Value :=
  .pair (fl (columnSum weights p.1)) (fl (columnSum weights p.2))

private structure SumRegisters (weights : Nat → ℝ) (s : Reduction) (t : TState) : Prop where
  input : ∀ i < 128, t.regs (1231 + i) = some (fl (weights i))
  scratch : ∀ r p, s r = some p → t.regs r = some (pairSum weights p)

private theorem sumStepOff {pc : Nat} (hlo : 4877 ≤ pc) (hhi : pc < 5006) :
    pc ∉ Assumptions.swExp2Sites := by
  simp [Assumptions.swExp2Sites]
  omega

private theorem sumIdeal {l : Launch} {g : Nat} {t : TState} {pc : Nat} {f : FloatForm}
    (h : t.pc = pc) (hlo : 4877 ≤ pc) (hhi : pc < 5006)
    (hf : f ∈ Assumptions.arithScope.float) : IdealAt Assumptions.numeric f l g t := by
  have hs := (Assumptions.numeric_segSites.pc (sumStepOff hlo hhi)).tail
  exact idealAt_head hf (h.symm ▸ hs)

private theorem sumWriteRun {l : Launch} {g pc d : Nat} {t : TState} {op : Op}
    {weights : Nat → ℝ} {s : Reduction} {p : Contributors}
    (ht : At t pc []) (hf : SumRegisters weights s t) (hd : 1358 < d)
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (he : execLocalA Assumptions.all l g t op = .ok (next (setReg t d (pairSum weights p)))) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧ At u (pc + 1) [] ∧
      SumRegisters weights (Function.update s d (some p)) u ∧
      ∀ r, r ≠ d → u.regs r = t.regs r := by
  let u := next (setReg t d (pairSum weights p))
  refine ⟨u, run_local hc hl ht he,
    (ht.set (r := d) (v := pairSum weights p) (by simp)).mono trivial, ?_,
    fun r hr => Function.update_of_ne hr _ _⟩
  constructor
  · intro i hi
    have hn : 1231 + i ≠ d := by omega
    simpa only [u, next, setReg, Function.update_of_ne hn] using hf.input i hi
  · intro r ps hr
    by_cases hn : r = d
    · subst r
      simp only [Function.update_self, Option.some.injEq] at hr
      subst ps
      exact Function.update_self ..
    · rw [Function.update_of_ne hn] at hr
      simpa only [u, next, setReg, Function.update_of_ne hn] using hf.scratch r ps hr

private theorem sumStepRun {l : Launch} {g pc : Nat} {t : TState}
    {weights : Nat → ℝ} {s s' : Reduction} (step : SumStep)
    (hlo : 4877 ≤ pc) (hhi : pc < 5004) (ht : At t pc []) (hf : SumRegisters weights s t)
    (hc : step.checked pc = true) (hs : step.columns s = some s') :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧ At u (pc + 1) [] ∧
      SumRegisters weights s' u ∧
      ∀ r, r ≠ step.dst → u.regs r = t.regs r := by
  have hCode := SumStep.checked_code hc
  cases step with
  | pack d k =>
    simp only [SumStep.columns] at hs
    split at hs
    · rename_i hd
      cases hs
      have hLo := hf.input (2 * k) (by omega)
      have hHi := hf.input (2 * k + 1) (by omega)
      have he : execLocalA Assumptions.all l g t (SumStep.op (.pack d k)) =
          .ok (next (setReg t d (pairSum weights ([2 * k], [2 * k + 1])))) := by
        rw [Assumptions.execLocalA_all_eq_numeric,
          Assumptions.execLocalA_eq_nil (ht.1 ▸ sumStepOff hlo (by omega)) rfl]
        have hHi' : t.regs (1232 + 2 * k) = some (fl (weights (2 * k + 1))) := by
          convert hHi using 2
          omega
        have hh := exec_pack (A := []) (L := l) (g := g) (d := d) (by simp [NoPack]) hLo hHi'
          SegFreePc.nil
        rw [ite_eq_left (show (fl (weights (2 * k))).bytes = 4 ∧
          (fl (weights (2 * k + 1))).bytes = 4 from ⟨rfl, rfl⟩)] at hh
        simpa only [SumStep.op, pairSum, columnSum, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, fl, joinValue] using hh
      exact sumWriteRun ht hf hd.2 hCode rfl he
    · contradiction
  | add d a b =>
    simp only [SumStep.columns] at hs
    split at hs
    · rename_i hd
      cases ha : s a with
      | some p =>
        simp only [ha, bind, Option.bind] at hs
        cases hb : s b with
        | some q =>
          simp only [hb] at hs
          cases hs
          have he := execAdd2 (d := d)
            (sumIdeal (l := l) (g := g) ht.1 hlo (by omega) (by decide))
            (hf.scratch a p ha) (hf.scratch b q hb)
          simp only [← columnSum_append] at he
          exact sumWriteRun ht hf hd hCode rfl he
        | none => simp [hb] at hs
      | none => simp [ha, bind, Option.bind] at hs
    · contradiction

private theorem sumBlockRun {l : Launch} {g : Nat} (weights : Nat → ℝ) :
    ∀ (steps : List SumStep) (pc : Nat) (s s' : Reduction) (t : TState),
      4877 ≤ pc → pc + steps.length ≤ 5004 →
      (∀ i (hi : i < steps.length), steps[i].checked (pc + i) = true) →
      steps.foldlM (fun s step => step.columns s) s = some s' →
      At t pc [] → SumRegisters weights s t →
      ∃ u, run kernel Assumptions.all l g steps.length t = some u ∧
        At u (pc + steps.length) [] ∧ SumRegisters weights s' u ∧
        ∀ r ∉ steps.map SumStep.dst, u.regs r = t.regs r := by
  intro steps
  induction steps with
  | nil =>
    intro pc s s' t _ _ _ hs ht hf
    cases hs
    exact ⟨t, rfl, ht, hf, fun _ _ => rfl⟩
  | cons step steps ih =>
    intro pc s s' t hlo hhi hCode hs ht hf
    simp only [List.foldlM_cons, List.length_cons] at hs hhi
    cases he : step.columns s with
    | none => simp [he, bind, Option.bind] at hs
    | some nextS =>
      rw [he] at hs
      change steps.foldlM (fun s step => step.columns s) nextS = some s' at hs
      obtain ⟨v, hv, hV, hVF, hKeepStep⟩ :=
        sumStepRun step hlo (by omega) ht hf (hCode 0 (by simp)) he
      have hTail (i : Nat) (hi : i < steps.length) :
          steps[i].checked (pc + 1 + i) = true := by
        rw [Nat.add_right_comm]
        exact hCode (i + 1) (by simp [hi])
      obtain ⟨u, hu, hU, hUF, hKeepTail⟩ := ih (pc + 1) nextS s' v (by omega) (by omega)
        hTail hs hV hVF
      refine ⟨u, ?_, ?_, hUF, ?_⟩
      · simpa only [List.length_cons, Nat.add_comm 1] using run_comp hv hu
      · simpa only [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm pc 1] using hU
      · intro r hr
        simp only [List.map_cons, List.mem_cons, not_or] at hr
        exact (hKeepTail r hr.2).trans (hKeepStep r hr.1)

private theorem sumCodeAt (i : Nat) (hi : i < sumSteps.length) :
    sumSteps[i].checked (4877 + i) = true := by
  have hiz : i < sumSteps.zipIdx.length := by simpa using hi
  have hm := List.getElem_mem (l := sumSteps.zipIdx) hiz
  have h := List.all_eq_true.mp sumStepsChecked _ hm
  simpa only [List.getElem_zipIdx, Nat.zero_add] using h

private theorem columnSum_range (weights : Nat → ℝ) (n : Nat) :
    columnSum weights (List.range n) = ∑ i ∈ Finset.range n, weights i := by
  induction n with
  | zero => simp [columnSum]
  | succ n ih =>
    rw [List.range_succ, columnSum_append, Finset.sum_range_succ, ih]
    simp [columnSum]

private theorem reductionTotal {weights : Nat → ℝ} {p : Contributors}
    (hp : reducedColumns = some p) :
    columnSum weights p.1 + columnSum weights p.2 = ∑ i ∈ Finset.range 128, weights i := by
  have hc := packedColumns.2
  rw [hp] at hc
  change (p.1 ++ p.2).isPerm (List.range 128) = true at hc
  rw [← columnSum_append, ← columnSum_range, columnSum, columnSum]
  exact ((List.isPerm_iff.mp hc).map weights).sum_eq

def firstSumResidentRegs : List Nat :=
  [1062,2535,5127,7132,1230] ++ firstTransitionRegs

private theorem firstSumResidentAudit :
    ∀ r ∈ firstSumResidentRegs, r ∉ sumSteps.map SumStep.dst ∧ r ∉ [3952, 3953, 7257] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Beginning just after the first correction acknowledgement, the thread executes the four
packed accumulator chains and writes the first row sum to the running FP32 register. -/
theorem firstRowSumWithResidentsLocal {l : Launch} {g : Nat} {t : TState}
    (weights : Nat → ℝ) (ht : At t 4877 [])
    (hWeights : ∀ i < 128, t.regs (1231 + i) = some (fl (weights i))) :
    ∃ u, At u 5006 [(7257, fl (∑ i ∈ Finset.range 128, weights i))] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      ∀ r ∈ firstSumResidentRegs, u.regs r = t.regs r := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp packedColumns.1
  unfold reducedColumns at hp
  cases hReduce : sumSteps.foldlM (fun s step => step.columns s) (fun _ => none) with
  | none => simp [hReduce, bind, Option.bind] at hp
  | some columns =>
    simp only [hReduce, bind, Option.bind] at hp
    have hTotal := reductionTotal (weights := weights) (p := p)
      (by unfold reducedColumns; rw [hReduce]; exact hp)
    have hLen : sumSteps.length = 127 := by decide
    have hInputs : SumRegisters weights (fun _ => none) t :=
      ⟨hWeights, fun _ _ h => by cases h⟩
    obtain ⟨v, hv, hV, hFields, hFrame⟩ :=
      sumBlockRun weights sumSteps 4877 (fun _ => none) columns t (by decide)
        (by rw [hLen]) sumCodeAt hReduce ht hInputs
    have hV' : At v 5004 [] := by simpa only [hLen] using hV
    have hv' : run kernel Assumptions.all l g 127 t = some v := hLen ▸ hv
    let x := columnSum weights p.1
    let y := columnSum weights p.2
    let w := next (setReg (setReg v 3952 (fl x)) 3953 (fl y))
    have hPair : v.regs 8314 = some (.pair (fl x) (fl y)) := hFields.scratch 8314 p hp
    have hw : run kernel Assumptions.all l g 1 v = some w := by
      apply run_local Flow.code_5004 rfl hV'
      rw [Assumptions.execLocalA_all_eq_numeric,
        Assumptions.execLocalA_eq_nil (hV'.1 ▸ sumStepOff (by decide) (by decide)) rfl]
      exact exec_unpack64 hPair rfl rfl SegFreePc.nil (by simp [NoUnpack64])
    have hW : At w 5005 [] := ⟨congrArg (· + 1) hV'.1, hV'.2.1, hV'.2.2.1, hV'.2.2.2.1, trivial⟩
    have hXr : w.regs 3952 = some (fl x) := rfl
    have hYr : w.regs 3953 = some (fl y) := rfl
    let u := next (setReg w 7257 (fl (x + y)))
    have hu : run kernel Assumptions.all l g 1 w = some u := by
      apply run_local Flow.code_5005 rfl hW
      exact execAdd1 (sumIdeal hW.1 (by decide) (by decide) (by decide)) hXr hYr
    have hU : At u 5006 [(7257, fl (x + y))] := hW.set (by simp)
    refine ⟨u, hTotal ▸ hU, run_rtg (run_comp (run_comp hv' hw) hu), ?_⟩
    intro r hr
    obtain ⟨hNoRun, hNoLast⟩ := firstSumResidentAudit r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hNoLast
    simpa only [u, w, next, setReg, Function.update_of_ne hNoLast.1,
      Function.update_of_ne hNoLast.2.1, Function.update_of_ne hNoLast.2.2] using
        hFrame r hNoRun

theorem firstRowSumLocal {l : Launch} {g : Nat} {t : TState}
    (weights : Nat → ℝ) (ht : At t 4877 [])
    (hWeights : ∀ i < 128, t.regs (1231 + i) = some (fl (weights i))) :
    ∃ u, At u 5006 [(7257, fl (∑ i ∈ Finset.range 128, weights i))] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      ∀ r ∈ firstTransitionRegs, u.regs r = t.regs r := by
  obtain ⟨u,hu,hPath,hRegs⟩ := firstRowSumWithResidentsLocal weights ht hWeights
  exact ⟨u,hu,hPath,fun r hr => hRegs r (List.mem_append_right _ hr)⟩

theorem firstRowSumTrace {l : Launch} {X : Execution} {g j : Nat} {t : TState}
    (weights : Nat → ℝ) (ht : At t 4877 [])
    (hWeights : ∀ i < 128, t.regs (1231 + i) = some (fl (weights i)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, At u 5006 [(7257, fl (∑ i ∈ Finset.range 128, weights i))] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) none ∧
      ∀ r ∈ firstTransitionRegs, u.regs r = t.regs r := by
  obtain ⟨u,hAt,hLocal,hKeep⟩ := firstRowSumLocal weights ht hWeights
  exact ⟨u,hAt,hRun.after_local hLocal,hKeep⟩

/-- The first row sum implements the initial denominator of the masked softmax
recurrence, at the reference used to compute the FP32 weights. -/
theorem firstShiftedRowSumTrace {p : Params} {l : Launch} {X : Execution}
    {g j b h row blocks : Nat} {t : TState} (reference : ℝ) (keep : Nat → Value)
    (ht : At t 4877 (factsFrom firstTransitionRegs keep))
    (hWeights : ∀ i < 128, t.regs (1231 + i) =
      some (fl (shiftedWeight p b h row (visitKey blocks 0 i) reference)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let mass := (2 : ℝ) ^ (-reference) * maskedBlockSum (p.keyCount b row) blocks 0
      (weight p b h row)
    ∃ u, At u 5006 ((7257, fl mass) :: factsFrom firstTransitionRegs keep) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) none := by
  obtain ⟨u, hU, hTail, hFrame⟩ := firstRowSumTrace _ (ht.mono trivial) hWeights hRun
  have hSum := shiftedBlockProducts p b h row blocks 0 reference (fun _ => 1)
  simp only [mul_one] at hSum
  refine ⟨u, ?_, hTail⟩
  exact hU.mono ⟨hSum ▸ hU.2.2.2.2.1, holds_of_pointwise (fun r hr =>
    (hFrame r hr).trans (holds_mem ht.2.2.2.2 (mem_factsFrom hr)))⟩

/-- One first-round trace computes and publishes the BF16 probabilities, waits for correction,
and then writes the initial FP32 denominator from the same weights. -/
theorem firstRoundNumericSum {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j b h row blocks : Nat} {t : TState} (reference : ℝ)
    (values : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ)
    (keep : Nat → Value) (hTransition : Holds t.regs (factsFrom firstTransitionRegs keep))
    (ht : At t (shiftStart 0) (tailFrame l warp))
    (hRead : ∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems 0, it.packOk values = true ∧
      it.src values = joinValue (scoreValue (scores it).1) (scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems 0,
      (scores it).1 = maskedLogit p b h row (visitKey blocks 0 (it.x - 3687)) ∧
      (scores it).2 = maskedLogit p b h row (visitKey blocks 0 (it.y - 3687)))
    (hScale : readERealPair l g t (.reg (shiftLayout 0).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout 0).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))))
    (hAddr : ∀ q : Fin 4, t.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)))
    (hSignalBase : t.regs 3217 = some (b32 (l.sharedBase + 8 * (stageOf warp).val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let weights := fun (q : Fin 4) i =>
      shiftedWeight p b h row (visitKey blocks 0 (32 * q.val + i)) reference
    let ack := waitLoc l g (stageOf warp) 3
    let mass := (2 : ℝ) ^ (-reference) * maskedBlockSum (p.keyCount b row) blocks 0
      (weight p b h row)
    ∃ u barInst electInst leader failed,
      let post := if laneOf l g = leader then j + 11 else j + 10
      (∀ i : Fin 10, X.get (g, j + i.val) =
        (firstPublicationEvents l g (stageOf warp) weights barInst electInst leader)[i.val]?) ∧
      (laneOf l g = leader → X.get (g, j + 10) = some
        ⟨4867, .arrive (signalLoc l g (stageOf warp) 2) 0 1 true .cta⟩) ∧
      (X.tr g).drop post = List.replicate failed ⟨4874, .wait ack 0 false true .cta⟩ ++
        ⟨4874, .wait ack 0 true true .cta⟩ :: (X.tr g).drop (post + failed + 1) ∧
      At u 5006 ((7257, fl mass) :: factsFrom firstTransitionRegs keep) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (post + failed + 1)) none := by
  obtain ⟨v, barInst, electInst, leader, failed, hP, hE, hAck, hV, hExp, hTail⟩ :=
    firstRoundNumericPublication hp warp reference values scores keep hTransition
      ht hRead hSource hLogits hScale hOffset hAddr hSignalBase hRun
  obtain ⟨u, hU, hRest⟩ := firstShiftedRowSumTrace reference keep hV hExp hTail
  exact ⟨u, barInst, electInst, leader, failed, hP, hE, hAck, hU, hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
