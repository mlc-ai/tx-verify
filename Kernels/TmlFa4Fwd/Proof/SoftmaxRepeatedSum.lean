-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstSum
public import Kernels.TmlFa4Fwd.Proof.SoftmaxReductionLayout
public import Lemmas.Flow.Recip
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Kernels.TmlFa4Fwd.Flow.Code.Part118

import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Numeric

noncomputable section

namespace Repeated

def sumStart : Repeated → Nat
  | .biased => 6561
  | .unbiased => 7466

def sumEnd : Repeated → Nat
  | .biased => 6647
  | .unbiased => 7599

private def seedRegs : Repeated → Nat × Nat × Nat
  | .biased => (5122, 5123, 8605)
  | .unbiased => (5805, 5806, 8852)

private def resultRegs : Repeated → Nat × Nat × Nat
  | .biased => (8686, 5124, 5125)
  | .unbiased => (8980, 5807, 5808)

private def sumSlice : Repeated → List Instr
  | .biased => Decoded.code205 ++ Decoded.code206 ++ Decoded.code207
  | .unbiased =>
    Decoded.code233 ++ Decoded.code234 ++ Decoded.code235 ++ Decoded.code236 ++ Decoded.code237

private def sliceStart : Repeated → Nat
  | .biased => 6560
  | .unbiased => 7456

set_option maxRecDepth 100000 in
private theorem sumSlice_eq (r : Repeated) :
    (kernel.code.drop r.sliceStart).take r.sumSlice.length = r.sumSlice := by
  cases r <;> kernel_rfl

private def body : Repeated → List Instr := fun r =>
  (r.sumSlice.drop (r.sumStart + 3 - r.sliceStart)).take (r.sumEnd - r.sumStart - 5)

private theorem bodyLength (r : Repeated) :
    r.body.length = r.sumEnd - r.sumStart - 5 := by
  cases r <;> kernel_rfl

private theorem bodyCode (r : Repeated) {i : Nat} (hi : i < r.body.length) :
    kernel.code[r.sumStart + 3 + i]? = some r.body[i] := by
  have hI : i < r.sumEnd - r.sumStart - 5 := r.bodyLength ▸ hi
  have hStart : r.sliceStart ≤ r.sumStart + 3 := by cases r <;> decide
  have hSize : r.sumEnd - 2 ≤ r.sliceStart + r.sumSlice.length := by cases r <;> decide +kernel
  have hLookup : r.body[i]? = kernel.code[r.sumStart + 3 + i]? := by
    unfold body
    rw [List.getElem?_take_of_lt hI, List.getElem?_drop, ← r.sumSlice_eq,
      List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    rw [show r.sliceStart + (r.sumStart + 3 - r.sliceStart + i) = r.sumStart + 3 + i by omega]
  exact hLookup.symm.trans (List.getElem?_eq_getElem hi)

end Repeated

private inductive ReductionStep
  | pack (dst lo hi : Nat)
  | add (dst left right : Nat)

private def repeatedAdd2 (d a b : Nat) : FloatInstr :=
  { op := .add, ty := ⟨.f32, 2⟩, rnd := some .rn, dsts := [some d], srcs := [.reg a, .reg b] }

private def ReductionStep.ofInstr : Instr → Option ReductionStep
  | ⟨none, .move ⟨.pack, .int .b 64, [some d], [.reg lo, .reg hi]⟩⟩ => some (.pack d lo hi)
  | ⟨none, .float f⟩ =>
    match f.dsts, f.srcs with
    | [some d], [.reg a, .reg b] => if f = repeatedAdd2 d a b then some (.add d a b) else none
    | _, _ => none
  | _ => none

private def ReductionStep.instr : ReductionStep → Instr
  | .pack d lo hi => ⟨none, .move ⟨.pack, .int .b 64, [some d], [.reg lo, .reg hi]⟩⟩
  | .add d a b => ⟨none, .float (repeatedAdd2 d a b)⟩

private theorem ReductionStep.instr_eq {i : Instr} {s : ReductionStep}
    (h : ReductionStep.ofInstr i = some s) : i = s.instr := by
  unfold ofInstr at h
  split at h
  · cases h
    rfl
  · rename_i f _
    split at h
    · split at h
      · rename_i hF
        cases h
        rw [hF]
        rfl
      · cases h
    · cases h
  · cases h

private abbrev ColumnState := Nat → Option (List Nat × List Nat)

private def Repeated.seedColumns (r : Repeated) : ColumnState := fun reg =>
  if reg = r.seedRegs.2.2 then some ([128], []) else
    if reg ∈ r.packedInputs then
      let i := r.packedInputs.idxOf reg
      some ([2 * i], [2 * i + 1])
    else none

private def ReductionStep.columns (r : Repeated) (c : ColumnState) :
    ReductionStep → Option ColumnState
  | .pack d lo hi =>
    if lo ∈ r.scalarInputs ∧ hi ∈ r.scalarInputs ∧ d ∉ r.scalarInputs then
      let offset := 2 * r.packedInputs.length
      some (Function.update c d
        (some ([offset + r.scalarInputs.idxOf lo], [offset + r.scalarInputs.idxOf hi])))
    else none
  | .add d a b => do
    if d ∈ r.scalarInputs then none else
      let p ← c a
      let q ← c b
      some (Function.update c d (some (p.1 ++ q.1, p.2 ++ q.2)))

private def Repeated.program (r : Repeated) : Option (List ReductionStep) :=
  r.body.mapM ReductionStep.ofInstr

private def Repeated.finalColumns (r : Repeated) : Option (List Nat × List Nat) := do
  let steps ← r.program
  let columns ← steps.foldlM (ReductionStep.columns r) r.seedColumns
  columns r.resultRegs.1

set_option maxRecDepth 100000 in
private theorem Repeated.allContributors (r : Repeated) :
    r.finalColumns.isSome = true ∧
      (r.finalColumns.map fun (a, b) => (a ++ b).isPerm (List.range 129)).getD false = true ∧
      (r.finalColumns.map fun (_, b) => !b.isEmpty).getD false = true := by
  cases r <;> constructor
  all_goals first | kernel_rfl | constructor <;> kernel_rfl

private def Repeated.mass (weights : Nat → ℝ) (old alpha : ℝ) (col : Nat) : ℝ :=
  if col = 128 then old * alpha else weights col

private def reductionSum (weights : Nat → ℝ) (columns : List Nat) : ℝ := (columns.map weights).sum

private def reductionPair (mass : Nat → ℝ) (p : List Nat × List Nat) : Value :=
  .pair (fl (reductionSum mass p.1)) (fl (reductionSum mass p.2))

/-- The preloaded sum seed takes its high half from a literal zero-bit register. -/
private def rawSeed (v : ℝ) : Value := .pair (fl v) (b32 0)

private structure ReductionRegs (r : Repeated) (mass : Nat → ℝ)
    (cols : ColumnState) (t : TState) : Prop where
  input : ∀ n ∈ r.scalarInputs, t.regs n =
    some (fl (mass (2 * r.packedInputs.length + r.scalarInputs.idxOf n)))
  scratch : ∀ n p, cols n = some p →
    t.regs n = some (reductionPair mass p) ∨
      (p.2 = [] ∧ t.regs n = some (rawSeed (reductionSum mass p.1)))

private theorem repeatedOff (r : Repeated) {pc : Nat}
    (hlo : r.sumStart ≤ pc) (hhi : pc < r.sumEnd) : pc ∉ Assumptions.swExp2Sites := by
  cases r <;> simp [Repeated.sumStart, Repeated.sumEnd] at hlo hhi
  all_goals simp [Assumptions.swExp2Sites]; omega

private theorem repeatedIdeal {l : Launch} {g : Nat} {t : TState} {f : FloatForm}
    (hOff : t.pc ∉ Assumptions.swExp2Sites) (hf : f ∈ Assumptions.arithScope.float) :
    IdealAt Assumptions.numeric f l g t :=
  idealAt_head hf (Assumptions.numeric_segSites.pc hOff).tail

private theorem reductionRead {l : Launch} {g : Nat} {t : TState} {r : Nat}
    {mass : Nat → ℝ} {p : List Nat × List Nat}
    (h : t.regs r = some (reductionPair mass p) ∨
      (p.2 = [] ∧ t.regs r = some (rawSeed (reductionSum mass p.1)))) :
    readERealPair l g t (.reg r) = some (.ok
      ((reductionSum mass p.1 : EReal), (reductionSum mass p.2 : EReal))) := by
  rcases h with h | ⟨he, h⟩
  · exact readERealPair_reg h rfl rfl
  · have h0 : valFloat .f32 (splitValue 64 (rawSeed (reductionSum mass p.1))).2 =
        .ok (reductionSum mass p.2) := by
      rw [he]
      exact valFloat_zero
    exact readERealPair_reg h rfl h0

private theorem repeatedAddFinite {l : Launch} {g : Nat} {t : TState} {d a b : Nat}
    {x y u v : ℝ} (hI : IdealAt Assumptions.numeric .addRnF32x2 l g t)
    (ha : readERealPair l g t (.reg a) = some (.ok ((x : EReal), (y : EReal))))
    (hb : readERealPair l g t (.reg b) = some (.ok ((u : EReal), (v : EReal)))) :
    execLocalA Assumptions.all l g t (.float (repeatedAdd2 d a b)) =
      .ok (next (setReg t d (.pair (fl (x + u)) (fl (y + v))))) := by
  have ha' (s t : ℝ) : addEReal (s : EReal) (t : EReal) = some ((s + t : ℝ) : EReal) := by
    simp [addEReal]
  have hv (x : ℝ) : erealValue .f32 (x : EReal) = fl x := by simp [erealValue, fl]
  rw [Assumptions.execLocalA_all_eq_numeric]
  apply hI _ rfl
  simp only [repeatedAdd2, execIdealFloat, ha, hb, bindRead, ha', hv, pure, Except.pure]

private theorem reductionWrite {l : Launch} {g pc d : Nat} {t : TState} {op : Op}
    {r : Repeated} {mass : Nat → ℝ} {c : ColumnState} {p : List Nat × List Nat}
    (ht : At t pc []) (hRegs : ReductionRegs r mass c t) (hd : d ∉ r.scalarInputs)
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (he : execLocalA Assumptions.all l g t op =
      .ok (next (setReg t d (reductionPair mass p)))) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧ At u (pc + 1) [] ∧
      ReductionRegs r mass (Function.update c d (some p)) u := by
  let u := next (setReg t d (reductionPair mass p))
  refine ⟨u, run_local hc hl ht he, (ht.set (r := d) (v := reductionPair mass p)
    (by simp)).mono trivial, ?_⟩
  constructor
  · intro n hn
    have hne : n ≠ d := fun he => hd (he ▸ hn)
    simpa only [u, next, setReg, Function.update_of_ne hne] using hRegs.input n hn
  · intro n columns hc
    by_cases hne : n = d
    · subst n
      simp only [Function.update_self, Option.some.injEq] at hc
      subst columns
      exact .inl (Function.update_self ..)
    · rw [Function.update_of_ne hne] at hc
      simpa only [u, next, setReg, Function.update_of_ne hne] using hRegs.scratch n columns hc

private theorem reductionStepRun {l : Launch} {g pc : Nat} {t : TState}
    {r : Repeated} {mass : Nat → ℝ} {c c' : ColumnState} (step : ReductionStep)
    (hlo : r.sumStart ≤ pc) (hhi : pc < r.sumEnd) (ht : At t pc [])
    (hRegs : ReductionRegs r mass c t) (hc : kernel.code[pc]? = some step.instr)
    (hColumns : step.columns r c = some c') :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧ At u (pc + 1) [] ∧
      ReductionRegs r mass c' u := by
  have hOff := ht.1.symm ▸ repeatedOff r hlo hhi
  cases step with
  | pack d lo hi =>
    simp only [ReductionStep.columns] at hColumns
    split at hColumns
    · rename_i hLegal
      cases hColumns
      have hLo := hRegs.input lo hLegal.1
      have hHi := hRegs.input hi hLegal.2.1
      have hExec := exec_pack (A := []) (L := l) (g := g) (d := d) (by simp [NoPack]) hLo hHi
        SegFreePc.nil
      let offset := 2 * r.packedInputs.length
      let p : List Nat × List Nat :=
        ([offset + r.scalarInputs.idxOf lo], [offset + r.scalarInputs.idxOf hi])
      have hExec' :
          execLocalA Assumptions.all l g t (ReductionStep.instr (.pack d lo hi)).op =
            .ok (next (setReg t d (reductionPair mass p))) := by
        rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
        have hBytes (v : ℝ) : (fl v).bytes = 4 := rfl
        rw [ite_eq_left ⟨hBytes _, hBytes _⟩] at hExec
        simpa only [ReductionStep.instr, reductionPair,
          reductionSum, p, offset, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero, fl, joinValue] using hExec
      exact reductionWrite ht hRegs hLegal.2.2 hc rfl hExec'
    · contradiction
  | add d a b =>
    simp only [ReductionStep.columns] at hColumns
    split at hColumns
    · contradiction
    · rename_i hd
      cases ha : c a with
      | none => simp [ha, bind, Option.bind] at hColumns
      | some p =>
        simp only [ha, bind, Option.bind] at hColumns
        cases hb : c b with
        | none => simp [hb] at hColumns
        | some q =>
          simp only [hb] at hColumns
          cases hColumns
          have hA := reductionRead (l := l) (g := g) (hRegs.scratch _ _ ha)
          have hB := reductionRead (l := l) (g := g) (hRegs.scratch _ _ hb)
          have hSum := repeatedAddFinite (d := d) (repeatedIdeal hOff (by decide)) hA hB
          have hJoin : ∀ a b, reductionSum mass (a ++ b) =
              reductionSum mass a + reductionSum mass b := by simp [reductionSum]
          simp only [← hJoin] at hSum
          exact reductionWrite ht hRegs hd hc rfl hSum

private theorem reductionRun {l : Launch} {g : Nat} {r : Repeated} (mass : Nat → ℝ) :
    ∀ (is : List Instr) (steps : List ReductionStep) (pc : Nat) (c c' : ColumnState)
      (t : TState),
      r.sumStart ≤ pc → pc + is.length ≤ r.sumEnd →
      (∀ i (hi : i < is.length), kernel.code[pc + i]? = some is[i]) →
      is.mapM ReductionStep.ofInstr = some steps →
      steps.foldlM (ReductionStep.columns r) c = some c' →
      At t pc [] → ReductionRegs r mass c t →
      ∃ u, run kernel Assumptions.all l g is.length t = some u ∧
        At u (pc + is.length) [] ∧ ReductionRegs r mass c' u := by
  intro is
  induction is with
  | nil =>
    intro steps pc c c' t _ _ _ hi hc ht hf
    cases hi
    cases hc
    exact ⟨t, rfl, ht, hf⟩
  | cons ins instrs ih =>
    intro steps pc c c' t hlo hhi hCode hi hc ht hf
    simp only [List.mapM_cons, List.length_cons] at hi hhi
    cases hDecode : ReductionStep.ofInstr ins with
    | none => simp [hDecode, bind, Option.bind] at hi
    | some step =>
      cases hRest : instrs.mapM ReductionStep.ofInstr with
      | none => simp [hDecode, hRest, bind, Option.bind] at hi
      | some nextSteps =>
        simp only [hDecode, hRest, bind, Option.bind, pure, Option.some.injEq] at hi
        subst steps
        cases hs : step.columns r c with
        | none => simp [List.foldlM_cons, hs, bind, Option.bind] at hc
        | some nextC =>
          simp only [List.foldlM_cons, hs, bind, Option.bind] at hc
          have hC := hCode 0 (by simp)
          change kernel.code[pc]? = some ins at hC
          rw [ReductionStep.instr_eq hDecode] at hC
          obtain ⟨v, hv, hV, hVF⟩ :=
            reductionStepRun step hlo (by omega) ht hf hC hs
          have hTail (i : Nat) (hi : i < instrs.length) :
              kernel.code[pc + 1 + i]? = some instrs[i] := by
            rw [Nat.add_right_comm]
            exact hCode (i + 1) (by simp [hi])
          obtain ⟨u, hu, hU, hUF⟩ := ih nextSteps (pc + 1) nextC c' v (by omega) (by omega)
            hTail hRest hc hV hVF
          exact ⟨u, by simpa only [List.length_cons, Nat.add_comm 1] using run_comp hv hu,
            by simpa only [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm pc 1] using hU,
            hUF⟩

private theorem repeatedSeedCode (r : Repeated) :
    kernel.code[r.sumStart]? = some ⟨none, .float {
      op := .mul, ty := ⟨.f32, 1⟩, dsts := [some r.seedRegs.1],
      srcs := [.reg 7257, .reg r.alphaReg] }⟩ ∧
    kernel.code[r.sumStart + 1]? = some ⟨none, .move {
      kind := .scalar, ty := .int .b 32, dsts := [some r.seedRegs.2.1], srcs := [.f32imm 0] }⟩ ∧
    kernel.code[r.sumStart + 2]? = some ⟨none, .move {
      kind := .pack, ty := .int .b 64, dsts := [some r.seedRegs.2.2],
      srcs := [.reg r.seedRegs.1, .reg r.seedRegs.2.1] }⟩ := by
  cases r
  · exact ⟨Flow.code_6561, Flow.code_6562, Flow.code_6563⟩
  · exact ⟨Flow.code_7466, Flow.code_7467, Flow.code_7468⟩

private theorem repeatedSeedRun {l : Launch} {g : Nat} {t : TState}
    (r : Repeated) (old alpha : ℝ) (ht : At t r.sumStart [])
    (hOld : t.regs 7257 = some (fl old)) {word : Value} (hAlpha : t.regs r.alphaReg = some word)
    (hAlphaValue : valFloat .f32 word = .ok alpha) :
    ∃ u, run kernel Assumptions.all l g 3 t = some u ∧ At u (r.sumStart + 3) [] ∧
      u.regs r.seedRegs.2.2 = some (rawSeed (old * alpha)) ∧
      ∀ n, n ≠ r.seedRegs.1 → n ≠ r.seedRegs.2.1 → n ≠ r.seedRegs.2.2 →
        u.regs n = t.regs n := by
  obtain ⟨hMul, hZero, hPack⟩ := repeatedSeedCode r
  let prod := r.seedRegs.1
  let zeroReg := r.seedRegs.2.1
  let pair := r.seedRegs.2.2
  let v := next (setReg t prod (fl (old * alpha)))
  let w := next (setReg v zeroReg (b32 0))
  let u := next (setReg w pair (rawSeed (old * alpha)))
  have hLen : r.sumStart + 2 < r.sumEnd := by cases r <;> decide
  have hv : run kernel Assumptions.all l g 1 t = some v := by
    apply run_local hMul rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric]
    exact exec_fmul (repeatedIdeal (ht.1.symm ▸ repeatedOff r (Nat.le_refl _) (by omega))
      (by decide)) hOld hAlpha rfl hAlphaValue
  have hV : At v (r.sumStart + 1) [(prod, fl (old * alpha))] := ht.set (by simp)
  have hw : run kernel Assumptions.all l g 1 v = some w := by
    apply run_local hZero rfl hV
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil
      (hV.1.symm ▸ repeatedOff r (by omega) (by omega)) rfl]
    simp [w, v, zeroReg, execLocalA, execLocalRule, execLocal, Op.rule, MoveInstr.rule,
      execMove, DType.width, readValue, readBits, pure, Except.pure, bind, Except.bind,
      Value.bytes, b32]
  have hProd : prod ≠ zeroReg := by cases r <;> decide
  have hW : At w (r.sumStart + 2)
      [(zeroReg, b32 0), (prod, fl (old * alpha))] := hV.set (by simpa)
  have hu : run kernel Assumptions.all l g 1 w = some u := by
    apply run_local hPack rfl hW
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil
      (hW.1.symm ▸ repeatedOff r (by omega) hLen) rfl]
    have he := exec_pack (A := []) (L := l) (g := g) (d := pair) (by simp [NoPack])
      hW.2.2.2.2.2.1 hW.2.2.2.2.1 SegFreePc.nil
    exact he
  exact ⟨u, run_comp (run_comp hv hw) hu, (hW.set (r := pair) (v := rawSeed (old * alpha)) (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · change r.seedRegs.2.1 ≠ r.seedRegs.2.2
      cases r <;> decide
    · change r.seedRegs.1 ≠ r.seedRegs.2.2
      cases r <;> decide)).mono trivial, Function.update_self .., fun n h1 h2 h3 => by
      simp only [u, w, v, prod, zeroReg, pair, next, setReg,
        Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]⟩

private def Repeated.seedSafe (r : Repeated) (n : Nat) : Bool :=
  n != r.seedRegs.1 && n != r.seedRegs.2.1 && n != r.seedRegs.2.2

set_option maxRecDepth 100000 in
private theorem Repeated.scalarInputCheck (r : Repeated) :
    r.scalarInputs.all (fun n => r.seedSafe n &&
      decide (2 * r.packedInputs.length + r.scalarInputs.idxOf n < 128)) = true := by
  cases r <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem Repeated.packedInputCheck (r : Repeated) :
    r.packedInputs.all (fun n => r.seedSafe n &&
      decide (2 * r.packedInputs.idxOf n + 1 < 128)) = true := by
  cases r <;> kernel_rfl

/-- The physical FP32 inputs of a repeated row sum, in decoded pair order. -/
structure RepeatedWeights (r : Repeated) (t : TState) (weights : Nat → ℝ) : Prop where
  scalar : ∀ n ∈ r.scalarInputs, t.regs n =
    some (fl (weights (2 * r.packedInputs.length + r.scalarInputs.idxOf n)))
  packed : ∀ n ∈ r.packedInputs, t.regs n =
    some (.pair (fl (weights (2 * r.packedInputs.idxOf n)))
      (fl (weights (2 * r.packedInputs.idxOf n + 1))))

private theorem seedRegisters {r : Repeated} {t u : TState}
    {weights : Nat → ℝ} {old alpha : ℝ} (hWeight : RepeatedWeights r t weights)
    (hSeed : u.regs r.seedRegs.2.2 = some (rawSeed (old * alpha)))
    (hFrame : ∀ n, n ≠ r.seedRegs.1 → n ≠ r.seedRegs.2.1 → n ≠ r.seedRegs.2.2 →
      u.regs n = t.regs n) :
    ReductionRegs r (Repeated.mass weights old alpha) r.seedColumns u := by
  constructor
  · intro n hn
    have hc := List.all_eq_true.mp r.scalarInputCheck n hn
    simp only [Repeated.seedSafe, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, hcol⟩ := hc
    rw [hFrame n h1 h2 h3]
    have hCol : 2 * r.packedInputs.length + r.scalarInputs.idxOf n ≠ 128 := by omega
    simpa only [Repeated.mass, ite_eq_right hCol] using hWeight.scalar n hn
  · intro n p hp
    unfold Repeated.seedColumns at hp
    split at hp
    · rename_i hSeedN
      cases hp
      exact .inr ⟨rfl, by simpa [Repeated.mass, reductionSum, hSeedN] using hSeed⟩
    · split at hp
      · rename_i hn
        cases hp
        have hc := List.all_eq_true.mp r.packedInputCheck n hn
        simp only [Repeated.seedSafe, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, hcol⟩ := hc
        left
        rw [hFrame n h1 h2 h3]
        have hLow : 2 * r.packedInputs.idxOf n ≠ 128 := by omega
        have hHigh : 2 * r.packedInputs.idxOf n + 1 ≠ 128 := by omega
        simpa [reductionPair, reductionSum, Repeated.mass, hLow, hHigh] using hWeight.packed n hn
      · cases hp

private theorem resultCode (r : Repeated) :
    kernel.code[r.sumEnd - 2]? =
      some ⟨none, .move ⟨.unpack, .int .b 64, [some r.resultRegs.2.1, some r.resultRegs.2.2],
        [.reg r.resultRegs.1]⟩⟩ ∧
    kernel.code[r.sumEnd - 1]? = some ⟨none, .float {
      op := .add, ty := ⟨.f32, 1⟩, dsts := [some 7257],
      srcs := [.reg r.resultRegs.2.1, .reg r.resultRegs.2.2] }⟩ := by
  cases r
  · exact ⟨Flow.code_6645, Flow.code_6646⟩
  · exact ⟨Flow.code_7597, Flow.code_7598⟩

private theorem resultRun {l : Launch} {g : Nat} {t : TState} (r : Repeated) (x y : ℝ)
    (ht : At t (r.sumEnd - 2) [])
    (hPair : t.regs r.resultRegs.1 = some (.pair (fl x) (fl y))) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u r.sumEnd [(7257, fl (x + y))] := by
  obtain ⟨hCode, hAdd⟩ := resultCode r
  let low := r.resultRegs.2.1
  let high := r.resultRegs.2.2
  let s := next (setReg (setReg t low (fl x)) high (fl y))
  have hEnd : r.sumStart + 2 ≤ r.sumEnd := by cases r <;> decide
  have hs : run kernel Assumptions.all l g 1 t = some s := by
    apply run_local hCode rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (ht.1.symm ▸ repeatedOff r (by omega) (by omega)) rfl]
    exact exec_unpack64 hPair rfl rfl SegFreePc.nil (by simp [NoUnpack64])
  have hS : At s (r.sumEnd - 1) [] :=
    ⟨by have h := ht.1; change t.pc + 1 = _; omega, ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
  have hLo : s.regs low = some (fl x) := by cases r <;> rfl
  have hHi : s.regs high = some (fl y) := Function.update_self ..
  let u := next (setReg s 7257 (fl (x + y)))
  have hu : run kernel Assumptions.all l g 1 s = some u := by
    apply run_local hAdd rfl hS
    have hA : readERealOpnd s .f32 (.reg low) = some (.ok (x : EReal)) :=
      (readERealOpnd_reg hLo).trans rfl
    have hB : readERealOpnd s .f32 (.reg high) = some (.ok (y : EReal)) :=
      (readERealOpnd_reg hHi).trans rfl
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      rw [hS.1]
      exact repeatedOff r (by omega) (by omega)
    have hI := repeatedIdeal (l := l) (g := g) hOff
      (by decide : FloatForm.add .f32 ∈ Assumptions.arithScope.float)
    have hSum : addEReal (x : EReal) (y : EReal) = some ((x + y : ℝ) : EReal) := by
      simp [addEReal]
    have hVal (v : ℝ) : erealValue .f32 (v : EReal) = fl v := by simp [erealValue, fl]
    dsimp only [low, high] at hA hB
    rw [Assumptions.execLocalA_all_eq_numeric]
    apply hI _ rfl
    simp only [u, execIdealFloat, hA, hB, bindRead, hSum, hVal, pure, Except.pure, Option.map_some]
  have hStep : r.sumEnd - 1 + 1 = r.sumEnd := by omega
  exact ⟨u, run_comp hs hu, hStep ▸ hS.set (by simp)⟩

private theorem repeatedTotal {r : Repeated} {weights : Nat → ℝ} {old alpha : ℝ}
    {p : List Nat × List Nat} (h : r.finalColumns = some p) :
    reductionSum (Repeated.mass weights old alpha) p.1 +
        reductionSum (Repeated.mass weights old alpha) p.2 =
      old * alpha + ∑ i ∈ Finset.range 128, weights i := by
  let mass := Repeated.mass weights old alpha
  have hc := (r.allContributors).2.1
  rw [h] at hc
  change (p.1 ++ p.2).isPerm (List.range 129) = true at hc
  have hSum := ((List.isPerm_iff.mp hc).map mass).sum_eq
  change (p.1.map mass).sum + (p.2.map mass).sum = _
  rw [← List.sum_append, ← List.map_append, hSum]
  have hRange (n : Nat) : ((List.range n).map mass).sum = ∑ i ∈ Finset.range n, mass i := by
    induction n with
    | zero => simp
    | succ n ih => simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero, ih, Finset.sum_range_succ]
  rw [hRange 129, Finset.sum_range_succ]
  have hm : mass 128 = old * alpha := by simp [mass, Repeated.mass]
  rw [hm, add_comm]
  apply congrArg (old * alpha + ·)
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp [mass, Repeated.mass, (show i ≠ 128 by omega)]

/-- The denominator reduction leaves the next reference and loop-tail inputs live. -/
def sumContinuationRegs : List Nat := [7256,7258,7250,7253,7248,7254,7249]

private def sumFrameCode (i : Instr) : Bool :=
  sumContinuationRegs.all (fun r => !((writesRegs i.op).contains r)) &&
    match i.op with
    | .bra .. | .brx .. => false
    | _ => true

private theorem sumFrameCodeAt (r : Repeated) {pc : Nat} {i : Instr}
    (hLo : r.sumStart ≤ pc) (hHi : pc < r.sumEnd) (hc : kernel.code[pc]? = some i) :
    sumFrameCode i = true := by
  have hAudit : ((kernel.code.drop r.sumStart).take (r.sumEnd-r.sumStart)).all
      sumFrameCode = true := by
    cases r <;> set_option maxRecDepth 100000 in kernel_rfl
  have hMem : i ∈ (kernel.code.drop r.sumStart).take (r.sumEnd-r.sumStart) := by
    apply List.mem_of_getElem? (i := pc-r.sumStart)
    rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
    exact hc
  exact List.all_eq_true.mp hAudit i hMem

private theorem sumRegistersOfRun {l : Launch} {g : Nat} (r : Repeated)
    {t u : TState} {n : Nat} (hLo : r.sumStart ≤ t.pc) (hHi : t.pc+n ≤ r.sumEnd)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r ∈ sumContinuationRegs, u.regs r = t.regs r := by
  induction n generalizing t with
  | zero => cases Option.some.inj hRun; exact fun _ _ => rfl
  | succ n ih =>
    cases hStep : tauStep kernel Assumptions.all l g t with
    | none => simp [run,hStep] at hRun
    | some s =>
      have hTail : run kernel Assumptions.all l g n s = some u := by
        simpa only [run,hStep,Option.bind_some] using hRun
      obtain ⟨i,hc,_,hExec⟩ := tauScoreSource (tauStep_iff.mp hStep)
      have hAudit := sumFrameCodeAt r hLo (by omega) hc
      have hs : s.pc = t.pc+1 ∧ ∀ n ∈ sumContinuationRegs, s.regs n = t.regs n := by
        rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
        · exact ⟨rfl,fun _ _ => rfl⟩
        rcases scoreExecLocal hLocal with hFrame | ⟨_,hSite,_,_⟩
        · simp only [sumFrameCode,Bool.and_eq_true] at hAudit
          have hPC := hFrame.pc
          have hNext : s.pc = t.pc+1 := by
            cases hOp : i.op <;> try simpa only [hOp,nextPc,BrxTarget,or_false] using hPC
            all_goals simp [hOp] at hAudit
          refine ⟨hNext,?_⟩
          intro n hn
          have hKeep := List.all_eq_true.mp hAudit.1 n hn
          exact hFrame.regs n (by simpa only [Bool.not_eq_true',List.contains_eq_mem,
            decide_eq_false_iff_not] using hKeep)
        · exact (repeatedOff r hLo (by omega) hSite).elim
      intro n hn
      exact (ih (by omega) (by omega) hTail n hn).trans (hs.2 n hn)

/-- After the successful correction acknowledgement in either repeated branch, the same
thread multiplies the previous sum by alpha, adds every FP32 probability once, and
reaches the next instruction with the updated denominator. -/
theorem repeatedRowSumLocalOfWordWithFrame {l : Launch} {g : Nat} {t : TState}
    (r : Repeated) (weights : Nat → ℝ) (old alpha : ℝ)
    (ht : At t r.sumStart []) (hOld : t.regs 7257 = some (fl old))
    {word : Value} (hAlpha : t.regs r.alphaReg = some word)
    (hAlphaValue : valFloat .f32 word = .ok alpha)
    (hWeights : RepeatedWeights r t weights) :
    ∃ u, At u r.sumEnd [(7257, fl (old * alpha + ∑ i ∈ Finset.range 128, weights i))] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      ∀ n ∈ sumContinuationRegs, u.regs n = t.regs n := by
  obtain ⟨s, hs, hS, hSeed, hSFrame⟩ := repeatedSeedRun r old alpha ht hOld hAlpha hAlphaValue
  let mass := Repeated.mass weights old alpha
  have hf := seedRegisters hWeights hSeed hSFrame
  obtain ⟨p, hFinal⟩ := Option.isSome_iff_exists.mp r.allContributors.1
  have hTotal := repeatedTotal (weights := weights) (old := old) (alpha := alpha) hFinal
  have hNonempty := r.allContributors.2.2
  rw [hFinal] at hNonempty
  have hLive : p.2 ≠ [] := by
    intro hBad
    change (!p.2.isEmpty) = true at hNonempty
    simp [hBad] at hNonempty
  unfold Repeated.finalColumns at hFinal
  cases hProg : r.program with
  | none => simp [hProg, bind, Option.bind] at hFinal
  | some steps =>
    simp only [hProg, bind, Option.bind] at hFinal
    cases hCols : steps.foldlM (ReductionStep.columns r) r.seedColumns with
    | none => simp [hCols] at hFinal
    | some cols =>
      simp only [hCols] at hFinal
      have hLen : r.sumStart + 3 + r.body.length = r.sumEnd - 2 := by
        rw [r.bodyLength]
        have h : r.sumStart + 5 ≤ r.sumEnd := by cases r <;> decide
        omega
      obtain ⟨v, hv, hV, hFields⟩ := reductionRun mass r.body steps (r.sumStart + 3)
        r.seedColumns cols s (by omega) (by rw [hLen]; omega)
        (fun _ hi => r.bodyCode hi) hProg hCols hS hf
      have hPair : v.regs r.resultRegs.1 = some (reductionPair mass p) :=
        (hFields.scratch _ _ hFinal).resolve_right (fun h => hLive h.1)
      obtain ⟨u, hu, hU⟩ := resultRun r _ _ (hLen ▸ hV) hPair
      have hLocal := run_comp (run_comp hs hv) hu
      have hBound : t.pc+(3+r.body.length+2) ≤ r.sumEnd := by
        rw [ht.1]
        omega
      exact ⟨u,hTotal ▸ hU,run_rtg hLocal,
        sumRegistersOfRun r ht.1.ge hBound hLocal⟩

section
variable {l : Launch} {X : Execution} {g j : Nat} {t : TState} (r : Repeated) (weights : Nat → ℝ)
    (old alpha : ℝ) (ht : At t r.sumStart []) (hOld : t.regs 7257 = some (fl old))
include r weights old alpha ht hOld

end

end
end PTX.Kernels.TmlFa4Fwd.Softmax
