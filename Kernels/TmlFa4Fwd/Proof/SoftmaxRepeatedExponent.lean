-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedSum
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part090
import Kernels.TmlFa4Fwd.Flow.Code.Part093
import Kernels.TmlFa4Fwd.Flow.Code.Part101
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part115
import Kernels.TmlFa4Fwd.Flow.Code.Part116

import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

private structure ExponentArguments where
  shifted : Nat → Option ℝ
  original : Nat → Value
  saved : Nat → Option Value

private inductive ExponentWord
  | shifted (column : Nat)
  | fp32 (column : Nat)
  | bf16 (low high : Nat)
  deriving DecidableEq

private def ExponentWord.value (args : ExponentArguments) (weights : Nat → ℝ) :
    ExponentWord → Value
  | .shifted c => scoreValue (args.shifted c)
  | .fp32 c => fl (weights c)
  | .bf16 a b => .pair (.float .bf16 (weights a)) (.float .bf16 (weights b))

private theorem ExponentWord.bytes (args : ExponentArguments) (weights : Nat → ℝ)
    (w : ExponentWord) : (w.value args weights).bytes = 4 := by
  cases w
  · exact scoreValue_bytes _
  · rfl
  · rfl

private theorem ExponentWord.joinBytes (args : ExponentArguments) (weights : Nat → ℝ)
    (a b : ExponentWord) :
    (joinValue (a.value args weights) (b.value args weights)).bytes = 8 := by
  cases a <;> cases b <;> try rfl
  case shifted.shifted a b =>
    cases ha : args.shifted a <;> cases hb : args.shifted b <;>
      simp only [value, ha, hb, scoreValue] <;> rfl
  case shifted.fp32 a _ => cases ha : args.shifted a <;> simp only [value, ha, scoreValue] <;> rfl
  case shifted.bf16 a _ _ => cases ha : args.shifted a <;> simp only [value, ha, scoreValue] <;> rfl
  case fp32.shifted _ b => cases hb : args.shifted b <;> simp only [value, hb, scoreValue] <;> rfl
  case bf16.shifted _ _ b => cases hb : args.shifted b <;> simp only [value, hb, scoreValue] <;> rfl

private theorem ExponentWord.splitJoin (args : ExponentArguments) (weights : Nat → ℝ)
    (a b : ExponentWord) :
    splitValue 64 (joinValue (a.value args weights) (b.value args weights)) =
      (a.value args weights, b.value args weights) := by
  cases a <;> cases b <;> try rfl
  case shifted.shifted a b =>
    cases ha : args.shifted a <;> cases hb : args.shifted b <;>
      simp only [value, ha, hb, scoreValue] <;> rfl
  case shifted.fp32 a _ => cases ha : args.shifted a <;> simp only [value, ha, scoreValue] <;> rfl
  case shifted.bf16 a _ _ => cases ha : args.shifted a <;> simp only [value, ha, scoreValue] <;> rfl

private inductive ExponentValue
  | word (w : ExponentWord)
  | pack (lo hi : ExponentWord)
  | constant (v : Value)
  | original (reg : Nat)
  | saved (reg : Nat)

private def ExponentValue.value (args : ExponentArguments) (weights : Nat → ℝ) :
    ExponentValue → Value
  | .word w => w.value args weights
  | .pack a b => joinValue (a.value args weights) (b.value args weights)
  | .constant v => v
  | .original r => args.original r
  | .saved r => (args.saved r).getD (.pred false)

private def ExponentValue.read (args : ExponentArguments) (weights : Nat → ℝ)
    (v : ExponentValue) : Option Value :=
  match v with
  | .saved r => args.saved r
  | _ => some (v.value args weights)

private abbrev ExponentRegs := Nat → Option ExponentValue

private def ExponentHolds (args : ExponentArguments) (weights : Nat → ℝ)
    (s : ExponentRegs) (t : TState) : Prop :=
  ∀ r x, s r = some x → t.regs r = x.read args weights

private theorem expUpdate {args : ExponentArguments} {weights : Nat → ℝ}
    {s : ExponentRegs} {t : TState} (h : ExponentHolds args weights s t)
    (d : Nat) (x : ExponentValue) :
    ExponentHolds args weights (Function.update s d (some x))
      {t with regs := Function.update t.regs d (x.read args weights)} := by
  intro r y hr
  by_cases hd : r = d
  · subst r
    simp only [Function.update_self, Option.some.injEq] at hr
    subst y
    exact Function.update_self ..
  · rw [Function.update_of_ne hd] at hr
    simpa only [Function.update_of_ne hd] using h r y hr

private theorem expClear {args : ExponentArguments} {weights : Nat → ℝ}
    {s : ExponentRegs} {t : TState} (h : ExponentHolds args weights s t) (d : Nat) :
    ExponentHolds args weights (Function.update s d none)
      {t with regs := Function.update t.regs d none} := by
  intro r y hr
  by_cases hd : r = d
  · subst r
    simp only [Function.update_self] at hr
    cases hr
  · rw [Function.update_of_ne hd] at hr
    simpa only [Function.update_of_ne hd] using h r y hr

private inductive ExponentStep
  | hardware (dst src : Nat)
  | convert (dst high low : Nat)
  | pack (dst lo hi : Nat)
  | unpack (lo : Nat) (hi : Option Nat) (src : Nat)
  | software (ins : Instr) (matched : SegMatch CuteSlot)

private def ex2Instr (d a : Nat) : FloatInstr :=
  {ex2I true with dsts := [some d], srcs := [.reg a]}

private def ex2ConvertInstr (d a b : Nat) : CvtInstr :=
  { dst := .packed (.float .bf16) 2, src := .float .f32, rnd := some .rn,
    d := d, srcs := [.reg a, .reg b] }

private def ExponentStep.instr : ExponentStep → Instr
  | .hardware d a => ⟨none, .float (ex2Instr d a)⟩
  | .convert d a b => ⟨none, probabilityConvertOp d a b⟩
  | .pack d a b => ⟨none, .move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩⟩
  | .unpack a b d => ⟨none, .move ⟨.unpack, .int .b 64, [some a, b], [.reg d]⟩⟩
  | .software ins _ => ins

private def ExponentStep.decode (pc : Nat) (ins : Instr) : Option ExponentStep :=
  if Assumptions.swExp2Sites.contains pc then
    if ins.guard.isNone && ins.op.isLocal then
      (cuteExp2.matchAt kernel pc).map (.software ins)
    else none
  else match ins with
  | ⟨none, .float f⟩ =>
    match f.dsts, f.srcs with
    | [some d], [.reg a] => if f = ex2Instr d a then some (.hardware d a) else none
    | _, _ => none
  | ⟨none, .cvt c⟩ =>
    match c.srcs with
    | [.reg a, .reg b] =>
      if c = ex2ConvertInstr c.d a b then
        if Assumptions.probPackSites.contains pc then some (.convert c.d a b) else none
      else none
    | _ => none
  | ⟨none, .move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩⟩ => some (.pack d a b)
  | ⟨none, .move ⟨.unpack, .int .b 64, [some a, b], [.reg d]⟩⟩ => some (.unpack a b d)
  | _ => none

private def isConstant (s : ExponentRegs) (r : Nat) (v : Value) : Bool :=
  match s r, v with
  | some (.constant (.bits w a)), .bits w' b => w == w' && a == b
  | _, _ => false

private theorem isConstant_sound {s : ExponentRegs} {r : Nat} {v : Value}
    (h : isConstant s r v = true) : s r = some (.constant v) := by
  unfold isConstant at h
  split at h
  · simp_all only [Bool.and_eq_true, beq_iff_eq]
  · cases h

private def expSoftwareRegs (m : SegMatch CuteSlot) (s : ExponentRegs)
    (outs : List (Nat × ExponentValue)) : ExponentRegs :=
  let cleared := m.shape.writes.foldl (fun rs slot => Function.update rs (m.regOf slot) none) s
  let constants := if m.shape.defines then
      m.shape.consts.foldl (fun rs (slot, v) =>
        Function.update rs (m.regOf slot) (some (.constant v))) cleared
    else cleared
  outs.foldl (fun rs p => Function.update rs p.1 (some p.2)) constants

private def ExponentStep.effect (e : ExponentStep) (s : ExponentRegs) : Option ExponentRegs :=
  match e with
  | .hardware d a => do
    let some (.word (.shifted col)) := s a | none
    some (Function.update s d (some (.word (.fp32 col))))
  | .convert d a b => do
    let some (.word (.fp32 hi)) := s a | none
    let some (.word (.fp32 lo)) := s b | none
    some (Function.update s d (some (.word (.bf16 lo hi))))
  | .pack d a b => do
    let some (.word lo) := s a | none
    let some (.word hi) := s b | none
    some (Function.update s d (some (.pack lo hi)))
  | .unpack a b d => do
    let some (.pack lo hi) := s d | none
    let afterLo := Function.update s a (some (.word lo))
    some (b.elim afterLo (fun r => Function.update afterLo r (some (.word hi))))
  | .software _ m => do
    let [p, q] := m.shape.io | none
    let some (.word (.shifted lo)) := s (m.regOf p.1) | none
    let some (.word (.shifted hi)) := s (m.regOf q.1) | none
    if m.shape.defines || m.shape.consts.all (fun c => isConstant s (m.regOf c.1) c.2) then
      some (expSoftwareRegs m s [(m.regOf p.2, .word (.fp32 lo)),
        (m.regOf q.2, .word (.fp32 hi))])
    else none

private def ExponentStep.advance (e : ExponentStep) (pc : Nat) : Nat :=
  match e with
  | .software _ matched => matched.stop
  | _ => pc + 1

private def ExponentStep.allowed (e : ExponentStep) (pc : Nat) : Prop :=
  match e with
  | .software ins m => pc ∈ Assumptions.swExp2Sites ∧ ins.guard = none ∧
      ins.op.isLocal = true ∧ cuteExp2.matchAt kernel pc = some m
  | .convert .. => pc ∈ Assumptions.probPackSites
  | _ => pc ∉ Assumptions.swExp2Sites

private theorem ExponentStep.decode_sound {pc : Nat} {ins : Instr} {e : ExponentStep}
    (h : decode pc ins = some e) : e.instr = ins ∧ e.allowed pc := by
  unfold decode at h
  split at h
  · rename_i hSite
    split at h
    · rename_i hLocal
      cases hm : cuteExp2.matchAt kernel pc with
      | none => simp [hm] at h
      | some m =>
        simp only [hm, Option.map_some, Option.some.injEq] at h
        subst e
        have hL := Bool.and_eq_true_iff.mp hLocal
        exact ⟨rfl, by simpa using hSite, Option.isNone_iff_eq_none.mp hL.1, hL.2, hm⟩
    · cases h
  · rename_i hNo
    have hOff : pc ∉ Assumptions.swExp2Sites := by simpa using hNo
    split at h
    · rename_i f hi
      split at h
      · split at h
        · rename_i he
          cases h
          rw [instr, he]
          exact ⟨rfl, hOff⟩
        · cases h
      · cases h
    · rename_i c hi
      split at h
      · split at h
        · rename_i he
          split at h
          · rename_i hPack
            cases h
            rw [instr, he]
            exact ⟨rfl,
              by simpa only [allowed, List.contains_eq_mem, decide_eq_true_eq] using hPack⟩
          · cases h
        · cases h
      · cases h
    · cases h
      exact ⟨rfl, hOff⟩
    · cases h
      exact ⟨rfl, hOff⟩
    · cases h

private theorem expFold {α : Type} {args : ExponentArguments} {weights : Nat → ℝ}
    (key : α → Nat) (value : α → Option ExponentValue) :
    ∀ (xs : List α) (s : ExponentRegs) (t : TState), ExponentHolds args weights s t →
      ExponentHolds args weights
        (xs.foldl (fun rs x => Function.update rs (key x) (value x)) s)
        {t with regs := (xs.foldl (fun rs x =>
          Function.update rs (key x) ((value x).bind (ExponentValue.read args weights)))
          t.regs)} := by
  intro xs
  induction xs with
  | nil => intro s t ht; exact ht
  | cons x xs ih =>
    intro s t ht
    simp only [List.foldl_cons]
    cases value x with
    | none =>
      simp only [Option.bind_none]
      exact ih _ _ (expClear ht (key x))
    | some v =>
      simp only [Option.bind_some]
      exact ih _ _ (expUpdate ht _ v)

private theorem expSoftwareFrame {args : ExponentArguments} {weights : Nat → ℝ}
    {s : ExponentRegs} {t : TState} (m : SegMatch CuteSlot)
    (outs : List (Nat × ExponentValue)) (h : ExponentHolds args weights s t)
    (hOut : ∀ p ∈ outs, p.2.read args weights = some (p.2.value args weights)) :
    ExponentHolds args weights (expSoftwareRegs m s outs)
      {t with
        regs := segRegs m t (outs.map fun p => (p.1, p.2.value args weights))
        pc := m.stop
        sub := 0
        acc := []} := by
  have hClear := expFold m.regOf (fun _ => none) m.shape.writes s t h
  let cleared {α : Type} (v : Nat → Option α) :=
    m.shape.writes.foldl (fun rs slot => Function.update rs (m.regOf slot) none) v
  have hUpdate (s' : ExponentRegs) (t' : TState) (h' : ExponentHolds args weights s' t') :
      ExponentHolds args weights
        (outs.foldl (fun rs p => Function.update rs p.1 (some p.2)) s')
        {t' with regs := ((outs.map fun p => (p.1, p.2.value args weights)).foldl
          (fun rs p => Function.update rs p.1 (some p.2)) t'.regs)} := by
    have hFold (ps : List (Nat × ExponentValue))
        (hRead : ∀ p ∈ ps, p.2.read args weights = some (p.2.value args weights))
        (rs : Nat → Option Value) :
        ps.foldl (fun (f : Nat → Option Value) p =>
          Function.update f p.1 (p.2.read args weights)) rs =
          ps.foldl (fun (f : Nat → Option Value) p =>
            Function.update f p.1 (some (p.2.value args weights))) rs := by
      induction ps generalizing rs with
      | nil => rfl
      | cons p ps ih =>
        simp only [List.foldl_cons, hRead p (.head _)]
        exact ih (fun q hq => hRead q (.tail _ hq)) _
    have h := expFold Prod.fst (fun p : Nat × ExponentValue => some p.2) outs s' t' h'
    simp only [Option.bind_some, hFold outs hOut] at h
    simpa only [List.foldl_map, Function.comp_apply] using h
  unfold expSoftwareRegs segRegs
  by_cases hd : m.shape.defines
  · simp only [hd, ↓reduceIte]
    have hh := expFold (fun p : CuteSlot × Value => m.regOf p.1)
      (fun p => some (.constant p.2)) m.shape.consts (cleared s)
      {t with regs := cleared t.regs} hClear
    exact hUpdate _ _ hh
  · simp only [hd]
    exact hUpdate _ _ hClear

private structure ExponentEval (args : ExponentArguments) (weights : Nat → ℝ) : Prop where
  hardware : ∀ c, ex2E true (scoreValue (args.shifted c)) = .ok (fl (weights c))
  software : ∀ c, Assumptions.swExp2Lane (scoreValue (args.shifted c)) = .ok (weights c)

private theorem readExpWeight {t : TState} {r : Nat} {x : ℝ}
    (h : t.regs r = some (fl x)) : readFinite t .f32 (.reg r) = some (.ok x) := by
  simp [readFinite, readERealOpnd_reg h, readEReal, fl, bindRead, pure, Except.pure,
    EReal.coe_ne_top, EReal.coe_ne_bot]

section
variable {l : Launch}

private theorem exponentStepRun {g pc : Nat} {t : TState} {s s' : ExponentRegs}
    {args : ExponentArguments} {weights : Nat → ℝ} (e : ExponentStep) (ht : At t pc [])
    (hRegs : ExponentHolds args weights s t) (hEval : ExponentEval args weights)
    (hAllowed : e.allowed pc) (hc : kernel.code[pc]? = some e.instr) (h : e.effect s = some s') :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (e.advance pc) [] ∧ ExponentHolds args weights s' u := by
  cases e with
  | hardware d a =>
    simp only [ExponentStep.effect] at h
    split at h
    · rename_i col ha
      cases h
      have hRun := hardwareExponentRun (l := l) (g := g) ht hAllowed hc
        (hRegs a (.word (.shifted col)) ha) (hEval.hardware col)
      exact ⟨_, hRun, (ht.set (by simp)).mono trivial, expUpdate hRegs d (.word (.fp32 col))⟩
    · cases h
  | convert d a b =>
    simp only [ExponentStep.effect] at h
    split at h
    · rename_i high ha
      split at h
      · rename_i low hb
        cases h
        have hRun := probabilityConvertRun (l := l) (g := g) ht hc hAllowed
          (readExpWeight (hRegs a (.word (.fp32 high)) ha))
          (readExpWeight (hRegs b (.word (.fp32 low)) hb))
        exact ⟨_, hRun, (ht.set (by simp)).mono trivial, expUpdate hRegs d (.word (.bf16 low high))⟩
      · cases h
    · cases h
  | pack d a b =>
    simp only [ExponentStep.effect] at h
    split at h
    · rename_i low ha
      split at h
      · rename_i high hb
        cases h
        let u := next (setReg t d ((ExponentValue.pack low high).value args weights))
        have hOff : t.pc ∉ Assumptions.swExp2Sites := ht.1.symm ▸ hAllowed
        have hRun : run kernel Assumptions.all l g 1 t = some u := by
          apply run_local hc rfl ht
          rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
          have he := exec_pack (A := []) (L := l) (g := g) (d := d) (by simp [NoPack])
            (hRegs a (.word low) ha) (hRegs b (.word high) hb) SegFreePc.nil
          simpa only [ExponentValue.value, ExponentWord.bytes, and_self,
            ↓reduceIte, u] using he
        exact ⟨u, hRun, (ht.set (r := d) (v := (ExponentValue.pack low high).value args weights)
          (by simp)).mono trivial, expUpdate hRegs d (.pack low high)⟩
      · cases h
    · cases h
  | unpack a b d =>
    simp only [ExponentStep.effect] at h
    split at h
    · rename_i low high hd
      cases h
      let u := next (setDst (setReg t a (low.value args weights)) b (high.value args weights))
      have hOff : t.pc ∉ Assumptions.swExp2Sites := ht.1.symm ▸ hAllowed
      have hRun : run kernel Assumptions.all l g 1 t = some u := by
        apply run_local hc rfl ht
        rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
        have hSrc := hRegs d (.pack low high) hd
        simp only [ExponentValue.read, ExponentValue.value] at hSrc
        have hBytes := low.joinBytes args weights high
        have hSplit := low.splitJoin args weights high
        cases b <;>
          simp [execLocalA, execLocalRule, execLocal, Op.rule, MoveInstr.rule,
            execMove, readValue, readReg, hSrc, hBytes, hSplit, ExponentWord.bytes, DType.width,
            u, setDst, bind, Except.bind, pure, Except.pure]
      have hKeep : ExponentHolds args weights
          (b.elim (Function.update s a (some (.word low)))
            (fun r => Function.update (Function.update s a (some (.word low))) r
              (some (.word high)))) u := by
        cases b with
        | none => exact expUpdate hRegs a (.word low)
        | some b => exact expUpdate (expUpdate hRegs a (.word low)) b (.word high)
      have hU : At u (pc + 1) [] := by
        cases b <;> exact ⟨congrArg (· + 1) ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
      exact ⟨u, hRun, hU, hKeep⟩
    · cases h
  | software ins m =>
    simp only [ExponentStep.effect] at h
    split at h
    · rename_i p q hIO
      split at h
      · rename_i low hLow
        split at h
        · rename_i high hHigh
          split at h
          · rename_i hC
            cases h
            obtain ⟨hSite, hGuard, hLocal, hMatch⟩ := hAllowed
            obtain ⟨guard, op⟩ := ins
            change guard = none at hGuard
            subst guard
            let getCol := fun slot =>
              match s (m.regOf slot) with | some (.word (.shifted col)) => col | _ => 0
            have hc0 : getCol p.1 = low := by simp only [getCol, hLow]
            have hc1 : getCol q.1 = high := by simp only [getCol, hHigh]
            have hConst : m.shape.defines ∨ ∀ pair ∈ m.shape.consts,
                t.regs (m.regOf pair.1) = some pair.2 := by
              rcases Bool.or_eq_true_iff.mp hC with hDef | hRem
              · exact .inl hDef
              · exact .inr fun pair hp =>
                  hRegs _ (.constant pair.2)
                    (isConstant_sound (List.all_eq_true.mp hRem pair hp))
            have hInputs : ∀ pair ∈ m.shape.io,
                t.regs (m.regOf pair.1) = some (scoreValue (args.shifted (getCol pair.1))) := by
              intro pair hp
              rw [hIO] at hp
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl
              · exact hc0.symm ▸ hRegs _ (.word (.shifted low)) hLow
              · exact hc1.symm ▸ hRegs _ (.word (.shifted high)) hHigh
            have hRun := softwareExponentValues (l := l) (g := g)
              (scoreValue ∘ args.shifted ∘ getCol) (weights ∘ getCol) ht hSite hc hLocal hMatch
              hConst hInputs (fun pair _ => hEval.software (getCol pair.1))
            have hf := expSoftwareFrame m [(m.regOf p.2, .word (.fp32 low)),
              (m.regOf q.2, .word (.fp32 high))] hRegs (by
                intro pair hm
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
                rcases hm with rfl | rfl <;> rfl)
            let u := softwareExponentResult m t (weights ∘ getCol)
            have hu : u = {t with
                regs := segRegs m t [(m.regOf p.2, fl (weights low)),
                  (m.regOf q.2, fl (weights high))], pc := m.stop, sub := 0, acc := []} := by
              unfold u softwareExponentResult segRegs
              rw [hIO]
              simp only [List.map_cons, List.map_nil, Function.comp_apply, hc0, hc1]
              rfl
            refine ⟨u, hRun, ⟨rfl, rfl, rfl, ht.2.2.2.1, trivial⟩, ?_⟩
            rw [hu]
            exact hf
          · cases h
        · cases h
      · cases h
    · cases h

private def unbiasedSlice : List Instr :=
  Decoded.code219 ++ Decoded.code220 ++ Decoded.code221 ++ Decoded.code222 ++
    Decoded.code223 ++ Decoded.code224 ++ Decoded.code225 ++ Decoded.code226 ++
    Decoded.code227 ++ Decoded.code228 ++ Decoded.code229 ++ Decoded.code230 ++
      Decoded.code231 ++ Decoded.code232

set_option maxRecDepth 100000 in
private theorem unbiasedSlice_eq :
    (kernel.code.drop 7008).take unbiasedSlice.length = unbiasedSlice := by kernel_rfl

private def unbiasedCode (pc : Nat) : Option Instr :=
  if 7008 ≤ pc then unbiasedSlice[pc - 7008]? else none

private theorem unbiasedCode_sound {pc : Nat} {i : Instr} (h : unbiasedCode pc = some i) :
    kernel.code[pc]? = some i := by
  unfold unbiasedCode at h
  split at h
  · rename_i hpc
    have hi := List.getElem?_eq_some_iff.mp h
    rw [← unbiasedSlice_eq, List.getElem?_take_of_lt hi.1, List.getElem?_drop] at h
    simpa only [Nat.add_sub_of_le hpc] using h
  · cases h

private def exponentRun (code : Nat → Option Instr) (stop : Nat) :
    Nat → Nat → ExponentRegs → Option ExponentRegs
  | 0, pc, regs => if pc = stop then some regs else none
  | fuel + 1, pc, regs =>
    if pc = stop then some regs else do
      let ins ← code pc
      let step ← ExponentStep.decode pc ins
      let nextRegs ← step.effect regs
      exponentRun code stop fuel (step.advance pc) nextRegs

private theorem exponentRun_sound {g stop : Nat} {args : ExponentArguments} {weights : Nat → ℝ}
    (hEval : ExponentEval args weights) (code : Nat → Option Instr)
    (hCode : ∀ {pc i}, code pc = some i → kernel.code[pc]? = some i) :
    ∀ (fuel pc : Nat) (regs nextRegs : ExponentRegs) (t : TState),
      exponentRun code stop fuel pc regs = some nextRegs → At t pc [] →
      ExponentHolds args weights regs t →
      ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
        At u stop [] ∧ ExponentHolds args weights nextRegs u := by
  intro fuel
  induction fuel with
  | zero =>
    intro pc regs nextRegs t hRun ht hRegs
    simp only [exponentRun] at hRun
    split at hRun
    · rename_i h
      cases hRun
      exact ⟨t, .refl, h ▸ ht, hRegs⟩
    · cases hRun
  | succ fuel ih =>
    intro pc regs nextRegs t hRun ht hRegs
    simp only [exponentRun] at hRun
    split at hRun
    · rename_i h
      cases hRun
      exact ⟨t, .refl, h ▸ ht, hRegs⟩
    · cases hc : code pc with
      | none => simp [hc, bind, Option.bind] at hRun
      | some ins =>
        simp only [hc, bind, Option.bind] at hRun
        cases hs : ExponentStep.decode pc ins with
        | none => simp [hs] at hRun
        | some step =>
          simp only [hs] at hRun
          cases he : step.effect regs with
          | none => simp [he] at hRun
          | some outRegs =>
            have hRun' : exponentRun code stop fuel (step.advance pc) outRegs = some nextRegs :=
              by simpa only [he] using hRun
            obtain ⟨hInstr, hAllow⟩ := ExponentStep.decode_sound hs
            have hDecoded : kernel.code[pc]? = some step.instr := hInstr.symm ▸ hCode hc
            obtain ⟨v, hv, hV, hVRegs⟩ := exponentStepRun step ht hRegs hEval hAllow hDecoded he
            obtain ⟨u, hu, hU, hURegs⟩ := ih _ _ _ v hRun' hV hVRegs
            exact ⟨u, (run_rtg hv).trans hu, hU, hURegs⟩

/-- The startup register facts needed for later P stores and the next row sum. -/
def unbiasedExpFrame : List Nat := [1062, 2535, 1492, 7257, 7258, 5183, 5185, 5181, 5184, 5187]

private def unbiasedExpInputs (r : Nat) : Option ExponentValue :=
  if 5520 ≤ r ∧ r < 5648 then some (.word (.shifted (r - 5520)))
  else if r ∈ unbiasedExpFrame then some (.original r)
  else if r ∈ roundContinuationRegs then some (.saved r)
  else none

private def unbiasedExpOutput : Option ExponentRegs :=
  exponentRun unbiasedCode 7416 400 7022 unbiasedExpInputs

private def hasWord (regs : ExponentRegs) (r : Nat) (w : ExponentWord) : Bool :=
  match regs r with
  | some (.word x) => decide (x = w)
  | _ => false

private theorem hasWord_sound {regs : ExponentRegs} {r : Nat} {w : ExponentWord}
    (h : hasWord regs r w = true) : regs r = some (.word w) := by
  unfold hasWord at h
  split at h
  · rename_i x hx
    rw [hx, of_decide_eq_true h]
  · cases h

private def hasOriginal (regs : ExponentRegs) (r : Nat) : Bool :=
  match regs r with
  | some (.original originalReg) => originalReg == r
  | _ => false

private theorem hasOriginal_sound {regs : ExponentRegs} {r : Nat}
    (h : hasOriginal regs r = true) : regs r = some (.original r) := by
  unfold hasOriginal at h
  split at h
  · rename_i originalReg he
    rw [he, beq_iff_eq.mp h]
  · cases h

private theorem readConvertedWords {g : Nat} {t : TState} (weights : Nat → ℝ) :
    ∀ (regs : List Nat) (offset : Nat),
      (∀ i (hi : i < regs.length), t.regs regs[i] = some (probabilityWord weights (offset + i))) →
      (regs.map Opnd.reg).mapM (readValue l g t 32) =
        .ok ((List.range' offset regs.length).map (probabilityWord weights)) := by
  intro regs
  induction regs with
  | nil => intro _ _; rfl
  | cons r rs ih =>
    intro offset hRegs
    have hr := hRegs 0 (by simp)
    have hRead : readValue l g t 32 (.reg r) = .ok (probabilityWord weights offset) := by
      simp [readValue, readReg, probabilityWord, pure, Except.pure,
        show t.regs r = some (probabilityWord weights offset) from hr]
    have hs (i : Nat) (hi : i < rs.length) :
        t.regs rs[i] = some (probabilityWord weights (offset + 1 + i)) := by
      rw [Nat.add_right_comm]
      exact hRegs (i + 1) (by simp [hi])
    rw [List.map_cons, List.mapM_cons, hRead, List.length_cons, List.range'_succ, List.map_cons]
    change (Except.ok (probabilityWord weights offset)).bind _ = _
    simp only [Except.bind, ih (offset + 1) hs, pure, Except.pure]
    rfl

private def unbiasedSources : Fin 4 → List Nat :=
  ![[5747, 5748, 5745, 5746, 5743, 5744, 5741, 5742,
     5739, 5740, 5737, 5738, 5735, 5736, 5733, 5734],
    [5763, 5764, 5761, 5762, 5759, 5760, 5751, 5752,
     5757, 5758, 5755, 5756, 5753, 5754, 5749, 5750],
    [5779, 5780, 5777, 5778, 5775, 5776, 5767, 5768,
     5773, 5774, 5771, 5772, 5769, 5770, 5765, 5766],
    [5796, 5797, 5794, 5795, 5792, 5793, 5790, 5791,
     5788, 5789, 5786, 5787, 5784, 5785, 5782, 5783]]

private theorem unbiasedStoreCode (q : Fin 4) :
    kernel.code[probabilityPc .unbiased q]? = some
      ⟨none, .tcSt (probabilityReg .unbiased q) ((unbiasedSources q).map Opnd.reg) .s32x32b⟩ := by
  fin_cases q
  · exact Flow.code_7416
  · exact Flow.code_7425
  · exact Flow.code_7434
  · exact Flow.code_7446

private def unbiasedClearSignal (s : ExponentRegs) : ExponentRegs :=
  Function.update (Function.update s 5781 none) 8850 none

private def unbiasedStoreRunStart : Fin 3 → Nat := ![7417, 7426, 7438]

private def nextUnbiasedRegs (q : Fin 3) (s : ExponentRegs) : Option ExponentRegs :=
  exponentRun unbiasedCode (probabilityPc .unbiased q.succ) 8 (unbiasedStoreRunStart q)
    (if q.val = 2 then unbiasedClearSignal s else s)

private def unbiasedStoreInputsNat : Nat → Option ExponentRegs
  | 0 => unbiasedExpOutput
  | q + 1 => if h : q < 3 then (unbiasedStoreInputsNat q).bind (nextUnbiasedRegs ⟨q, h⟩) else none

private def unbiasedStoreInputs (q : Fin 4) : Option ExponentRegs :=
  unbiasedStoreInputsNat q.val

private theorem unbiasedStoreInputs_succ (q : Fin 3) :
    unbiasedStoreInputs q.succ =
      (unbiasedStoreInputs (Fin.castSucc q)).bind (nextUnbiasedRegs q) := by
  simp only [unbiasedStoreInputs, Fin.val_succ, unbiasedStoreInputsNat, q.isLt, ↓reduceDIte,
    Fin.val_castSucc]

private def unbiasedStoreCheck (q : Fin 4) (regs : ExponentRegs) : Bool :=
  (unbiasedSources q).zipIdx.all (fun (r, i) =>
    hasWord regs r (.bf16 (32 * q.val + 2 * i) (32 * q.val + 2 * i + 1))) &&
    unbiasedExpFrame.all (hasOriginal regs) &&
    Repeated.unbiased.scalarInputs.all (fun r =>
      hasWord regs r (.fp32 (Repeated.unbiased.scalarInputs.idxOf r)))

set_option maxRecDepth 100000 in
private theorem unbiasedAllStoreChecks (q : Fin 4) :
    (unbiasedStoreInputs q).any (unbiasedStoreCheck q) = true := by
  fin_cases q <;> kernel_rfl

def repeatedStoreEvent (l : Launch) (g : Nat) (stage : Fin 2) (round : Round) (q : Fin 4)
    (weights : Nat → ℝ) : Event :=
  ⟨probabilityPc round q, .tc (.st (probabilityAddress l g stage q)
    ((List.range' (16 * q.val) 16).map (probabilityWord weights)) .s32x32b)⟩

def unbiasedStoreEvent (l : Launch) (g : Nat) (stage : Fin 2) (q : Fin 4)
    (weights : Nat → ℝ) : Event :=
  repeatedStoreEvent l g stage .unbiased q weights

private theorem probabilitySuffixNonempty {X : Execution} {g j : Nat} {t : TState}
    {ending : Option TState} (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j < (X.tr g).length) : (X.tr g).drop j ≠ [] := by
  intro hEmpty
  rcases hAvail with rfl | hLen
  · rw [hEmpty] at hr
    cases hr
  · have h := congrArg List.length hEmpty
    simp only [List.length_drop,List.length_nil] at h
    omega

private theorem probabilityAvailableEarlier {X : Execution} {g i j : Nat}
    {ending : Option TState} (h : ending = none ∨ j < (X.tr g).length) (hOrder : i ≤ j) :
    ending = none ∨ i < (X.tr g).length :=
  h.imp_right (Nat.lt_of_le_of_lt hOrder)

private theorem exponentStoreAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (round : Round) (stage : Fin 2) (q : Fin 4)
    {g j : Nat} {t : TState} {ending : Option TState} (sources : List Nat) (weights : Nat → ℝ)
    (hLen : sources.length = 16) (ht : At t (probabilityPc round q) [])
    (hCode : kernel.code[probabilityPc round q]? = some
      ⟨none, .tcSt (probabilityReg round q) (sources.map Opnd.reg) .s32x32b⟩)
    (hWord : ∀ i (hi : i < sources.length), t.regs sources[i] =
      some (probabilityWord weights (16 * q.val + i)))
    (hAddr : t.regs (probabilityReg round q) = some (b32 (probabilityAddress l g stage q)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨
      (if delayedProbability round q then j+1 else j) < (X.tr g).length) :
    let k := if delayedProbability round q then j + 1 else j
    (delayedProbability round q = true →
      X.get (g, j) = some ⟨probabilityPc round q, .tc .waitLd⟩) ∧
      X.get (g, k) = some (repeatedStoreEvent l g stage round q weights) ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (k + 1)) ending ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (k+1-j)) (next t) := by
  have hRead := readConvertedWords (l := l) (g := g) weights sources (16 * q.val) hWord
  rw [hLen] at hRead
  have hBytes : ((List.range' (16 * q.val) 16).map (probabilityWord weights)).all
      (·.bytes = 4) = true := by
    apply List.all_eq_true.mpr
    rintro v hv
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
    rfl
  obtain ⟨hWait,hStore,hRest,hPath⟩ := probabilityTraceWithPath hp round q stage
    ht.1 ht.2.2.2.1 ht.2.1 hCode hAddr hRead hBytes hRun hAvail
  exact ⟨fun hh => by simpa only [ht.1] using hWait hh,
    by simpa only [ht.1,repeatedStoreEvent] using hStore,hRest,hPath⟩

private theorem appendProbabilityPath {g j a b : Nat} {X : Execution} {s t u : TState}
    (h : TraceReach kernel Assumptions.all l g s (((X.tr g).drop j).take a) t)
    (hn : TraceReach kernel Assumptions.all l g t (((X.tr g).drop (j+a)).take b) u) :
    TraceReach kernel Assumptions.all l g s (((X.tr g).drop j).take (a+b)) u := by
  rw [List.take_add,List.drop_drop]
  exact h.append hn

private theorem preProbabilityLocal {g : Nat} {s t u : TState} {events : List Event}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hn : TraceReach kernel Assumptions.all l g t events u) :
    TraceReach kernel Assumptions.all l g s events u :=
  (TraceReach.of_local h).append hn

private theorem unbiasedStoreWords (stage : Fin 2) (q : Fin 4) {g : Nat} {t : TState}
    {args : ExponentArguments} {weights : Nat → ℝ} {regs : ExponentRegs}
    (hRegs : ExponentHolds args weights regs t) (hReady : unbiasedStoreInputs q = some regs)
    (hAddr : args.original (probabilityReg .unbiased q) = b32 (probabilityAddress l g stage q)) :
    (unbiasedSources q).length = 16 ∧
      (∀ i (hi : i < (unbiasedSources q).length),
        t.regs (unbiasedSources q)[i] = some (probabilityWord weights (16*q.val+i))) ∧
      t.regs (probabilityReg .unbiased q) = some (b32 (probabilityAddress l g stage q)) := by
  have hCheck := unbiasedAllStoreChecks q
  rw [hReady, Option.any_some] at hCheck
  simp only [unbiasedStoreCheck, Bool.and_eq_true] at hCheck
  have hWord (i : Nat) (hi : i < (unbiasedSources q).length) :
      t.regs (unbiasedSources q)[i] = some (probabilityWord weights (16 * q.val + i)) := by
    have hiz : i < (unbiasedSources q).zipIdx.length := by simpa using hi
    have hm := List.getElem_mem (l := (unbiasedSources q).zipIdx) hiz
    have h := List.all_eq_true.mp hCheck.1.1 _ hm
    simp only [List.getElem_zipIdx, Nat.zero_add] at h
    have hi0 : 2 * (16 * q.val + i) = 32 * q.val + 2 * i := by omega
    simpa only [ExponentValue.read, ExponentValue.value, ExponentWord.value, probabilityWord, hi0]
      using
      hRegs _ _ (hasWord_sound h)
  have hMem : probabilityReg .unbiased q ∈ unbiasedExpFrame := by fin_cases q <;> decide
  have hAddrT := hRegs _ _ (hasOriginal_sound (List.all_eq_true.mp hCheck.1.2 _ hMem))
  have hAddr' : t.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g stage q)) :=
    hAddrT.trans (congrArg some hAddr)

  have hLen : (unbiasedSources q).length = 16 := by fin_cases q <;> decide
  exact ⟨hLen,hWord,hAddr'⟩

private theorem unbiasedStoreAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (stage : Fin 2) (q : Fin 4) {g j : Nat} {t : TState} {ending : Option TState}
    {args : ExponentArguments} {weights : Nat → ℝ} {regs : ExponentRegs}
    (hRegs : ExponentHolds args weights regs t) (hReady : unbiasedStoreInputs q = some regs)
    (ht : At t (probabilityPc .unbiased q) [])
    (hAddr : args.original (probabilityReg .unbiased q) =
      b32 (probabilityAddress l g stage q))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j < (X.tr g).length) :
    X.get (g, j) = some (unbiasedStoreEvent l g stage q weights) ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j + 1)) ending ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 1) (next t) := by
  obtain ⟨hLen,hWord,hAddress⟩ := unbiasedStoreWords stage q hRegs hReady hAddr
  obtain ⟨_, hStore, hTail,hPath⟩ := exponentStoreAt hp .unbiased stage q _ weights hLen ht
    (unbiasedStoreCode q) hWord hAddress hRun (show _ ∨ j < _ from hAvail)
  have hDelay : delayedProbability .unbiased q = false := rfl
  exact ⟨by simpa only [ht.1, hDelay, Bool.false_eq_true, ↓reduceIte, unbiasedStoreEvent,
    repeatedStoreEvent]
    using hStore, by simpa only [hDelay, Bool.false_eq_true, ↓reduceIte] using hTail,
    by simpa only [hDelay,Bool.false_eq_true,↓reduceIte,Nat.add_sub_cancel_left] using hPath⟩

private theorem unbiasedMainArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState} {ending : Option TState}
    {args : ExponentArguments} {weights : Nat → ℝ} {regs : ExponentRegs}
    (hRegs : ExponentHolds args weights regs t) (ht : At t 7435 [])
    (hReady : unbiasedStoreInputs 2 = some regs)
    (hBase : args.original 5187 = b32 (l.sharedBase + 8 * stage.val))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+1 < (X.tr g).length) :
    ∃ u, X.get (g, j) = some ⟨7435, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨7437, .arrive (signalLoc l g stage 6) 0 1 true .cta⟩ ∧
      At u 7438 [] ∧ ExponentHolds args weights (unbiasedClearSignal regs) u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 2)) ending ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 2) u := by
  have hWaitTrace :
      X.get (g,j) = some ⟨probabilityWaitPc .unbiased false,.tc .waitSt⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j+1)) ending := by
    rcases hAvail with rfl | hi
    · exact probabilityWaitTrace hp .unbiased false ht.1 ht.2.2.2.1 hRun
    · exact probabilityWaitInPrefix hp .unbiased false ht.1 ht.2.2.2.1 hRun (by omega)
  obtain ⟨hWait,hTail⟩ := hWaitTrace
  let v := next (setReg (next t) 5781 (b32 1))
  have hLocal : run kernel Assumptions.all l g 1 (next t) = some v := by
    apply run_local Flow.code_7436 rfl ht.next
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
      rw [ht.next.1]
      decide) rfl]
    rfl
  have hV : At v 7437 [(5781, b32 1)] := ht.next.set (by simp)
  have hCheck := unbiasedAllStoreChecks 2
  rw [hReady, Option.any_some] at hCheck
  simp only [unbiasedStoreCheck, Bool.and_eq_true] at hCheck
  have hOrig := hasOriginal_sound (List.all_eq_true.mp hCheck.1.2 5187 (by decide))
  have hAddr : v.regs 5187 = some (b32 (l.sharedBase + 8 * stage.val)) :=
    (hRegs _ _ hOrig).trans (congrArg some hBase)
  have hSignalRun := hTail.after_local_nonempty (run_rtg hLocal)
    (probabilitySuffixNonempty hTail hAvail)
  have hCount := hV.2.2.2.2.1
  have hSignalTrace :
      X.get (g,j+1) = some ⟨(signalSite 6).pc,.arrive (signalLoc l g stage 6) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g (next (mbarStateDest v (some (signalSite 6).state)))
        ((X.tr g).drop ((j+1)+1)) ending := by
    rcases hAvail with rfl | hi
    · exact signalTrace hp stage 6 hV.1 hV.2.2.2.1 hAddr hCount hSignalRun
    · exact signalTraceInPrefix hp stage 6 hV.1 hV.2.2.2.1 hAddr hCount hSignalRun hi
  obtain ⟨hSignal,hAfter⟩ := hSignalTrace
  let w := next (mbarStateDest v (some 8850))
  have hW : At w 7438 [] :=
    ⟨congrArg (· + 1) hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, trivial⟩
  refine ⟨w,hWait,hSignal,hW,?_,hAfter,?_⟩
  · intro r x hr
    by_cases hw₁ : r = 5781
    · subst r
      simp [unbiasedClearSignal] at hr
    by_cases hw₂ : r = 8850
    · subst r
      simp [unbiasedClearSignal] at hr
    simp only [unbiasedClearSignal, Function.update_of_ne hw₁, Function.update_of_ne hw₂] at hr
    simpa only [w, v, next, mbarStateDest, setReg, Function.update_of_ne hw₁,
      Function.update_of_ne hw₂] using hRegs r x hr

  · have hWaitStep : EStep kernel Assumptions.all l g t
        ⟨(probabilityWaitPc .unbiased false),.tc .waitSt⟩ (some (next t)) := by
      refine ⟨_,probabilityWaitTemplate hp .unbiased false ht.1 ht.2.2.2.1,?_,rfl⟩
      rw [ht.1]
      rfl
    have hSignalStep : EStep kernel Assumptions.all l g v
        ⟨(signalSite 6).pc,.arrive (signalLoc l g stage 6) 0 1 true .cta⟩ (some w) := by
      refine ⟨_,signalTemplate hp stage 6 (g := g) hV.1 hV.2.2.2.1 hAddr hCount,?_,rfl⟩
      rw [hV.1]
      rfl
    rw [show (2 : Nat) = 1+1 from rfl,List.take_add,List.drop_drop,
      probabilityEventSingleton hWait,probabilityEventSingleton hSignal]
    exact .event hWaitStep ((TraceReach.of_local (run_rtg hLocal)).append (.event hSignalStep
      (.refl _)))

set_option maxRecDepth 100000 in
private theorem unbiasedExpStartLocal {g : Nat} {t : TState} {args : ExponentArguments}
    {weights : Nat → ℝ} (hEval : ExponentEval args weights) (ht : At t 7022 [])
    (hRaw : ∀ i < 128, t.regs (5520 + i) = some (scoreValue (args.shifted i)))
    (hFrame : ∀ r ∈ unbiasedExpFrame, t.regs r = some (args.original r))
    (hSaved : ∀ r ∈ roundContinuationRegs, t.regs r = args.saved r) :
    ∃ u regs, unbiasedStoreInputs 0 = some regs ∧ At u 7416 [] ∧
      ExponentHolds args weights regs u ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hInput : ExponentHolds args weights unbiasedExpInputs t := by
    intro r x hr
    unfold unbiasedExpInputs at hr
    split at hr
    · rename_i hh
      cases hr
      have he : 5520 + (r - 5520) = r := by omega
      simpa only [he, ExponentValue.read, ExponentValue.value, ExponentWord.value]
        using hRaw (r - 5520) (by omega)
    · split at hr
      · rename_i hh
        cases hr
        exact hFrame r hh
      · split at hr
        · rename_i hh
          cases hr
          exact hSaved r hh
        · cases hr
  have hCheck := unbiasedAllStoreChecks 0
  cases hOutput : unbiasedStoreInputs 0 with
  | none => rw [hOutput, Option.any_none] at hCheck; cases hCheck
  | some regs =>
    have hComputed : exponentRun unbiasedCode 7416 400 7022 unbiasedExpInputs = some regs := by
      simpa only [unbiasedStoreInputs, unbiasedStoreInputsNat, unbiasedExpOutput] using hOutput
    obtain ⟨u, hu, hU, hRegs⟩ :=
      exponentRun_sound (l := l) (g := g) hEval unbiasedCode unbiasedCode_sound
        400 7022 unbiasedExpInputs regs t hComputed ht hInput
    exact ⟨u, regs, rfl, hU, hRegs, hu⟩

private theorem unbiasedExpStart {X : Execution} {g j : Nat} {t : TState} {ending : Option TState}
    {args : ExponentArguments} {weights : Nat → ℝ} (hEval : ExponentEval args weights)
    (ht : At t 7022 []) (hRaw : ∀ i < 128, t.regs (5520 + i) = some (scoreValue (args.shifted i)))
    (hFrame : ∀ r ∈ unbiasedExpFrame, t.regs r = some (args.original r))
    (hSaved : ∀ r ∈ roundContinuationRegs, t.regs r = args.saved r)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j < (X.tr g).length) :
    ∃ u regs, unbiasedStoreInputs 0 = some regs ∧ At u 7416 [] ∧
      ExponentHolds args weights regs u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨u,regs,hRegs,hAt,hWords,hLocal⟩ :=
    unbiasedExpStartLocal (l := l) (g := g) hEval ht hRaw hFrame hSaved
  exact ⟨u,regs,hRegs,hAt,hWords,hRun.after_local_nonempty hLocal
    (probabilitySuffixNonempty hRun hAvail),hLocal⟩

private theorem observedUnbiasedRegs {args : ExponentArguments} {weights : Nat → ℝ}
    {regs : ExponentRegs} {t : TState} (q : Fin 4)
    (hReady : unbiasedStoreInputs q = some regs) (hRegs : ExponentHolds args weights regs t) :
    RepeatedWeights .unbiased t weights ∧
      ∀ r ∈ unbiasedExpFrame, t.regs r = some (args.original r) := by
  have hCheck := unbiasedAllStoreChecks q
  rw [hReady, Option.any_some] at hCheck
  simp only [unbiasedStoreCheck, Bool.and_eq_true] at hCheck
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simpa only [Repeated.packedInputs, List.length_nil, Nat.mul_zero, Nat.zero_add,
      ExponentValue.read, ExponentValue.value, ExponentWord.value] using
      hRegs _ _ (hasWord_sound (List.all_eq_true.mp hCheck.2 _ hr))
  · intro r hr
    cases hr
  · intro r hr
    exact hRegs _ _ (hasOriginal_sound (List.all_eq_true.mp hCheck.1.2 _ hr))

private theorem nextUnbiasedStore {X : Execution} {g j : Nat} {t : TState} {ending : Option TState}
    {args : ExponentArguments} {weights : Nat → ℝ} {regs : ExponentRegs} (q : Fin 3)
    (hEval : ExponentEval args weights) (hBefore : unbiasedStoreInputs (Fin.castSucc q) = some regs)
    (ht : At t (unbiasedStoreRunStart q) [])
    (hRegs : ExponentHolds args weights (if q.val = 2 then unbiasedClearSignal regs else regs) t)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j < (X.tr g).length) :
    ∃ u s, unbiasedStoreInputs q.succ = some s ∧
      At u (probabilityPc .unbiased q.succ) [] ∧ ExponentHolds args weights s u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hCheck := unbiasedAllStoreChecks q.succ
  cases hOutput : unbiasedStoreInputs q.succ with
  | none => rw [hOutput, Option.any_none] at hCheck; cases hCheck
  | some s =>
    have hLink : nextUnbiasedRegs q regs = some s := by
      rw [unbiasedStoreInputs_succ, hBefore, Option.bind_some] at hOutput
      exact hOutput
    obtain ⟨u, hu, hU, hReg⟩ :=
      exponentRun_sound (l := l) (g := g) hEval unbiasedCode unbiasedCode_sound 8 _ _ _ t
        hLink ht hRegs
    exact ⟨u, s, rfl, hU, hReg, hRun.after_local_nonempty hu
      (probabilitySuffixNonempty hRun hAvail),hu⟩
end

private def hasSaved (regs : ExponentRegs) (r : Nat) : Bool :=
  match regs r with
  | some (.saved savedReg) => savedReg == r
  | _ => false

private theorem hasSaved_sound {regs : ExponentRegs} {r : Nat}
    (h : hasSaved regs r = true) : regs r = some (.saved r) := by
  unfold hasSaved at h
  split at h <;> simp_all

set_option maxRecDepth 100000 in
private theorem unbiasedSavedAudit :
    (unbiasedStoreInputs 3).any (fun s => roundContinuationRegs.all (hasSaved s)) = true := by
  kernel_rfl

private theorem unbiasedStoreKeepsContinuation {s : ExponentRegs} {r : Nat}
    (h : unbiasedStoreInputs 3 = some s) (hr : r ∈ roundContinuationRegs) :
    s r = some (.saved r) := by
  have check := unbiasedSavedAudit
  rw [h, Option.any_some] at check
  exact hasSaved_sound (List.all_eq_true.mp check _ hr)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (stage : Fin 2)
    {g j : Nat} {t : TState} (raw : Nat → Option ℝ) (weights : Nat → ℝ) (values : Nat → Value)
    (ht : At t 7022 []) (hRaw : ∀ i < 128, t.regs (5520 + i) = some (scoreValue (raw i)))
    (hHardware : ∀ i, ex2E true (scoreValue (raw i)) = .ok (fl (weights i)))
    (hSoftware : ∀ i, Assumptions.swExp2Lane (scoreValue (raw i)) = .ok (weights i))
    (hFrame : ∀ r ∈ unbiasedExpFrame, t.regs r = some (values r))
    (hAddr : ∀ q, values (probabilityReg .unbiased q) = b32 (probabilityAddress l g stage q))
    (hSignal : values 5187 = b32 (l.sharedBase + 8 * stage.val))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp stage raw weights values ht hRaw hHardware hSoftware hFrame hAddr hSignal hRun

/-- In the unbiased repeated branch, the hardware and software exponents produce the same
128 probabilities for the FP32 reduction and the four BF16 TMEM stores. The first CTA
P notification follows the completion wait for the initial three stores. -/
theorem unbiasedProbabilityStoresWithPath :
    ∃ u, X.get (g, j) = some (unbiasedStoreEvent l g stage 0 weights) ∧
      X.get (g, j + 1) = some (unbiasedStoreEvent l g stage 1 weights) ∧
      X.get (g, j + 2) = some (unbiasedStoreEvent l g stage 2 weights) ∧
      X.get (g, j + 3) = some ⟨7435, .tc .waitSt⟩ ∧
      X.get (g, j + 4) = some ⟨7437, .arrive (signalLoc l g stage 6) 0 1 true .cta⟩ ∧
      X.get (g, j + 5) = some (unbiasedStoreEvent l g stage 3 weights) ∧
      At u 7447 [] ∧ RepeatedWeights .unbiased u weights ∧
      (∀ r ∈ unbiasedExpFrame, u.regs r = some (values r)) ∧
      (∀ r ∈ roundContinuationRegs, u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 6)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 6) u := by
  let args : ExponentArguments := ⟨raw, values, t.regs⟩
  have hEval : ExponentEval args weights := ⟨hHardware, hSoftware⟩
  obtain ⟨t0, s0, hs0, hAt0, hRegs0, hTail0,hLocal0⟩ :=
    unbiasedExpStart hEval ht hRaw hFrame (fun _ _ => rfl) hRun (.inl rfl)
  obtain ⟨hStore0, hAfter0,hStorePath0⟩ :=
     unbiasedStoreAt hp stage 0 hRegs0 hs0 hAt0 (hAddr 0) hTail0 (.inl rfl)
  obtain ⟨t1, s1, hs1, hAt1, hRegs1, hTail1,hLocal1⟩ :=
    nextUnbiasedStore 0 hEval hs0 hAt0.next hRegs0 hAfter0 (.inl rfl)
  obtain ⟨hStore1, hAfter1,hStorePath1⟩ :=
     unbiasedStoreAt hp stage 1 hRegs1 hs1 hAt1 (hAddr 1) hTail1 (.inl rfl)
  obtain ⟨t2, s2, hs2, hAt2, hRegs2, hTail2,hLocal2⟩ :=
    nextUnbiasedStore 1 hEval hs1 hAt1.next hRegs1 hAfter1 (.inl rfl)
  obtain ⟨hStore2, hAfter2,hStorePath2⟩ :=
     unbiasedStoreAt hp stage 2 hRegs2 hs2 hAt2 (hAddr 2)
      hTail2 (.inl rfl)
  obtain ⟨t3, hWait, hArrive, hAt3, hRegs3, hTail3,hLocal3⟩ :=
    unbiasedMainArrival hp stage (t := next t2) hRegs2 hAt2.next hs2 hSignal hAfter2 (.inl rfl)
  obtain ⟨t4, s4, hs4, hAt4, hRegs4, hTail4,hLocal4⟩ :=
    nextUnbiasedStore 2 hEval hs2 hAt3 hRegs3 hTail3 (.inl rfl)
  obtain ⟨hStore3, hAfter3,hStorePath3⟩ :=
     unbiasedStoreAt hp stage 3 hRegs4 hs4 hAt4 (hAddr 3) hTail4 (.inl rfl)
  obtain ⟨hWeights, hKeep⟩ := observedUnbiasedRegs 3 hs4 hRegs4
  refine ⟨next t4, hStore0, hStore1, hStore2, hWait, hArrive, hStore3, hAt4.next,
    ⟨hWeights.scalar, hWeights.packed⟩, hKeep,
      fun r hr => hRegs4 _ _ (unbiasedStoreKeepsContinuation hs4 hr), hAfter3,?_⟩

  have hPrefix := appendProbabilityPath (a := 1) (b := 1)
    (preProbabilityLocal hLocal0 hStorePath0) (preProbabilityLocal hLocal1 hStorePath1)
  have hThird := appendProbabilityPath (a := 2) (b := 1) hPrefix
    (preProbabilityLocal hLocal2 hStorePath2)
  have hSignalPath := appendProbabilityPath (a := 3) (b := 2) hThird hLocal3
  exact appendProbabilityPath (a := 5) (b := 1) hSignalPath
    (preProbabilityLocal hLocal4 hStorePath3)

end

private def biasedSlice : List Instr :=
    Decoded.code181 ++ Decoded.code182 ++ Decoded.code183 ++
    Decoded.code184 ++ Decoded.code185 ++ Decoded.code186 ++
    Decoded.code187 ++ Decoded.code188 ++ Decoded.code189 ++
    Decoded.code190 ++ Decoded.code191 ++ Decoded.code192 ++
    Decoded.code193 ++ Decoded.code194 ++ Decoded.code195 ++
    Decoded.code196 ++ Decoded.code197 ++ Decoded.code198 ++
    Decoded.code199 ++ Decoded.code200 ++ Decoded.code201 ++
    Decoded.code202 ++ Decoded.code203 ++ Decoded.code204 ++
    Decoded.code205

set_option maxRecDepth 100000 in
private theorem biasedSlice_eq :
    (kernel.code.drop 5792).take biasedSlice.length = biasedSlice := by kernel_rfl

private def biasedCode (pc : Nat) : Option Instr :=
  if 5792 ≤ pc then biasedSlice[pc - 5792]? else none

private theorem biasedCode_sound {pc : Nat} {i : Instr} (h : biasedCode pc = some i) :
    kernel.code[pc]? = some i := by
  unfold biasedCode at h
  split at h
  · rename_i hpc
    have hi := List.getElem?_eq_some_iff.mp h
    rw [← biasedSlice_eq, List.getElem?_take_of_lt hi.1, List.getElem?_drop] at h
    simpa only [Nat.add_sub_of_le hpc] using h
  · cases h

/-- The biased probability computation carries the stage predicate and row-sum state. -/
def biasedExpFrame : List Nat := [1062, 2535, 637, 1362, 7257, 7258]

private def biasedExpInputs (r : Nat) : Option ExponentValue :=
  if 1363 ≤ r ∧ r < 1491 then some (.word (.shifted (r - 1363)))
  else if r ∈ biasedExpFrame then some (.original r)
  else if r ∈ roundContinuationRegs then some (.saved r)
  else none

private def biasedExpStart (mixed : Bool) : Nat := if mixed then 5977 else 5816

private def biasedExpStop (mixed : Bool) : Nat := if mixed then 6299 else 5976

private def biasedPAddresses (regs : ExponentRegs) : ExponentRegs :=
  fun r => if 4821 ≤ r ∧ r < 4825 then some (.original r)
    else if 4816 ≤ r ∧ r < 4821 then none else regs r

private def biasedExpPrefix (mixed : Bool) : Option ExponentRegs :=
  exponentRun biasedCode (biasedExpStop mixed) 330 (biasedExpStart mixed) biasedExpInputs

private def biasedExpOutput (mixed : Bool) : Option ExponentRegs :=
  (biasedExpPrefix mixed).bind fun s =>
    exponentRun biasedCode 6508 200 6308 (biasedPAddresses s)

private def hasPack (regs : ExponentRegs) (r : Nat) (a b : ExponentWord) : Bool :=
  match regs r with
  | some (.pack x y) => decide (x = a ∧ y = b)
  | _ => false

private def biasedWeightCheck (regs : ExponentRegs) : Bool :=
  Repeated.biased.scalarInputs.all (fun r =>
    hasWord regs r (.fp32 (2 * Repeated.biased.packedInputs.length +
      Repeated.biased.scalarInputs.idxOf r))) &&
  Repeated.biased.packedInputs.all (fun r =>
    hasPack regs r (.fp32 (2 * Repeated.biased.packedInputs.idxOf r))
      (.fp32 (2 * Repeated.biased.packedInputs.idxOf r + 1)))

set_option maxRecDepth 100000 in
private theorem biasedExpCheck (mixed : Bool) :
    (biasedExpOutput mixed).any biasedWeightCheck = true := by
  cases mixed <;> kernel_rfl

private theorem biasedBranch {l : Launch} {g : Nat} {t : TState}
    (mixed : Bool) (ht : At t 5815 [(634, .pred mixed)]) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (biasedExpStart mixed) [] ∧ u.regs = t.regs := by
  let u := if mixed then {t with pc := 5977} else skip t
  have hEq : tauStep kernel Assumptions.all l g t = tauStep kernel [] l g t := by
    apply Assumptions.tauStep_all_eq_nil (by rw [ht.1]; decide)
      (by rw [ht.1]; exact Flow.code_5815) rfl
  have hPred := ht.2.2.2.2.1
  have hRun : run kernel Assumptions.all l g 1 t = some u := by
    rw [run, hEq]
    cases mixed <;>
      simp [u, run, tauStep, out, ht.1, ht.2.2.2.1, Flow.code_5815, guardHolds, readReg, hPred,
        Op.isLocal,
        execLocalA, execLocalRule, execLocal, Op.rule, execBranch, pure, Except.pure,
        bind, Except.bind]
  refine ⟨u, hRun, ?_, ?_⟩
  · cases mixed
    · exact ⟨congrArg (· + 1) ht.1, rfl, rfl, ht.2.2.2.1, trivial⟩
    · exact ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
  · cases mixed <;> rfl

private theorem biasedBranchJoin {l : Launch} {g : Nat} {t : TState}
    (mixed : Bool) (ht : At t (biasedExpStop mixed) []) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 6299 [] ∧ u.regs = t.regs := by
  cases mixed
  · let u := {t with pc := 6299}
    have hRun : run kernel Assumptions.all l g 1 t = some u := by
      apply run_local Flow.code_5976 rfl ht
      rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil (by
        rw [ht.1]
        decide) rfl]
      rfl
    exact ⟨u, run_rtg hRun, ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩, rfl⟩
  · exact ⟨t, .refl, ht, rfl⟩

private theorem biasedExponentPrefixLocal {l : Launch}
    {g : Nat} {t : TState} {args : ExponentArguments} {weights : Nat → ℝ}
    (mixed : Bool) (hEval : ExponentEval args weights) (ht : At t 5815 [(634, .pred mixed)])
    (hRaw : ∀ i < 128, t.regs (1363 + i) = some (scoreValue (args.shifted i)))
    (hFrame : ∀ r ∈ biasedExpFrame, t.regs r = some (args.original r))
    (hSaved : ∀ r ∈ roundContinuationRegs, t.regs r = args.saved r)
 :
    ∃ u regs, biasedExpPrefix mixed = some regs ∧ At u 6299 [] ∧
      ExponentHolds args weights regs u ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hInput : ExponentHolds args weights biasedExpInputs t := by
    intro r x hr
    unfold biasedExpInputs at hr
    split at hr
    · rename_i hh
      cases hr
      have he : 1363 + (r - 1363) = r := by omega
      simpa only [he, ExponentValue.read, ExponentValue.value, ExponentWord.value]
        using hRaw (r - 1363) (by omega)
    · split at hr
      · rename_i hh
        cases hr
        exact hFrame r hh
      · split at hr
        · rename_i hh
          cases hr
          exact hSaved r hh
        · cases hr
  obtain ⟨a, ha, hA, hAFrame⟩ := biasedBranch (l := l) (g := g) mixed ht
  have hp := biasedExpCheck mixed
  cases hReg : biasedExpPrefix mixed with
  | none =>
    simp only [biasedExpOutput, hReg, Option.bind_none, Option.any_none] at hp
    cases hp
  | some s =>
    have hComputed : exponentRun biasedCode (biasedExpStop mixed) 330 (biasedExpStart mixed)
        biasedExpInputs = some s := hReg
    have hARegs : ExponentHolds args weights biasedExpInputs a := by
      intro r x hr
      rw [hAFrame]
      exact hInput r x hr
    obtain ⟨b, hb, hB, hBRegs⟩ := exponentRun_sound (l := l) (g := g) hEval
      biasedCode biasedCode_sound 330 _ _ _ a hComputed hA hARegs
    obtain ⟨u, hu, hU, hUFrame⟩ := biasedBranchJoin (l := l) (g := g) mixed hB
    have hURegs : ExponentHolds args weights s u := by
      intro r x hr
      rw [hUFrame]
      exact hBRegs r x hr
    exact ⟨u, s, rfl, hU, hURegs, (run_rtg ha).trans (hb.trans hu)⟩

set_option maxRecDepth 100000 in
private theorem biasedPrefixKeeps (mixed : Bool) :
    (biasedExpPrefix mixed).any (fun s => biasedExpFrame.all (hasOriginal s)) = true := by
  cases mixed <;> kernel_rfl

section
variable {p : Params} {l : Launch} {m : Mem0}

private theorem biasedExponentAddressLocal (hp : Pre p l m) (stage : Fin 2) (mixed : Bool) {g : Nat}
    {t : TState} {args : ExponentArguments} {weights : Nat → ℝ} {regs : ExponentRegs}
    (hData : biasedExpPrefix mixed = some regs) (ht : At t 6299 [])
    (hRegs : ExponentHolds args weights regs t) (hStage : args.original 637 = .pred (stage.val = 1))
    (hAddresses : ∀ q, args.original (probabilityReg .biased q) =
      b32 (probabilityAddress l g stage q)) :
    ∃ u, At u 6308 [] ∧ ExponentHolds args weights (biasedPAddresses regs) u ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hc := biasedPrefixKeeps mixed
  rw [hData, Option.any_some] at hc
  have hStageT : t.regs 637 = some (.pred (stage.val = 1)) :=
    (hRegs _ _ (hasOriginal_sound (List.all_eq_true.mp hc 637 (by decide)))).trans
      (congrArg some hStage)
  have hT := ht.mono (G := [(637, .pred (stage.val = 1))]) ⟨hStageT, trivial⟩
  obtain ⟨u, hr, hU⟩ := biasedPAddressSegment hp g stage t hT
  have hFrame := biasedPAddressFrame (l := l) (g := g) (t := t) (u := u)
    (by rw [ht.1]) (by rw [ht.1]) hr
  refine ⟨u, hU.mono trivial, ?_, run_rtg hr⟩
  intro r x hx
  unfold biasedPAddresses at hx
  split at hx
  · rename_i hrange
    cases hx
    have hExist : ∃ q : Fin 4, probabilityReg .biased q = r := by
      have h : r = 4821 ∨ r = 4822 ∨ r = 4823 ∨ r = 4824 := by omega
      rcases h with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
    obtain ⟨q, hq⟩ := hExist
    have hMem : (probabilityReg .biased q, b32 (probabilityAddress l g stage q)) ∈
        biasedAddressFacts l g stage := by
      fin_cases q
      · exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · exact List.Mem.tail _ (List.Mem.head _)
    rw [← hq]
    exact (holds_mem hU.2.2.2.2 hMem).trans (congrArg some (hAddresses q).symm)
  · rename_i hn
    split at hx
    · cases hx
    · rename_i hm
      rw [hFrame r (by omega)]
      exact hRegs r x hx

private def biasedSources (q : Fin 4) : List Nat :=
  (List.range 16).map ((![5048, 5064, 5080, 5099] : Fin 4 → Nat) q + ·)

private theorem biasedStoreCode (q : Fin 4) :
    kernel.code[probabilityPc .biased q]? = some
      ⟨none, .tcSt (probabilityReg .biased q) ((biasedSources q).map Opnd.reg) .s32x32b⟩ := by
  fin_cases q
  · exact Flow.code_6508
  · exact Flow.code_6517
  · exact Flow.code_6526
  · exact Flow.code_6541

private def biasedSignalWrites : List Nat := 8603 :: biasedReleaseScratch

private def biasedClearSignal (s : ExponentRegs) : ExponentRegs :=
  fun r => if r ∈ biasedSignalWrites then none else s r

private def biasedStoreRunStart : Fin 3 → Nat := ![6509, 6518, 6533]

private def nextBiasedRegs (q : Fin 3) (s : ExponentRegs) : Option ExponentRegs :=
  exponentRun biasedCode (probabilityPc .biased q.succ) 8 (biasedStoreRunStart q)
    (if q.val = 2 then biasedClearSignal s else s)

private def biasedStoreInputsNat (mixed : Bool) : Nat → Option ExponentRegs
  | 0 => biasedExpOutput mixed
  | q + 1 => if h : q < 3 then (biasedStoreInputsNat mixed q).bind (nextBiasedRegs ⟨q, h⟩) else none

private def biasedStoreInputs (mixed : Bool) (q : Fin 4) : Option ExponentRegs :=
  biasedStoreInputsNat mixed q.val

private theorem biasedStoreInputs_succ (mixed : Bool) (q : Fin 3) :
    biasedStoreInputs mixed q.succ =
      (biasedStoreInputs mixed (Fin.castSucc q)).bind (nextBiasedRegs q) := by
  simp only [biasedStoreInputs, Fin.val_succ, biasedStoreInputsNat, q.isLt, ↓reduceDIte,
    Fin.val_castSucc]

private def biasedStoreCheck (q : Fin 4) (regs : ExponentRegs) : Bool :=
  (biasedSources q).zipIdx.all (fun (r, i) =>
    hasWord regs r (.bf16 (32 * q.val + 2 * i) (32 * q.val + 2 * i + 1))) &&
    biasedExpFrame.all (hasOriginal regs) &&
    ((List.range 4).map (4821 + ·)).all (hasOriginal regs) &&
    biasedWeightCheck regs

set_option maxRecDepth 100000 in
private theorem biasedHardwareStore0Check :
    (biasedStoreInputs false 0).any (biasedStoreCheck 0) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem biasedHardwareStore1Check :
    (biasedStoreInputs false 1).any (biasedStoreCheck 1) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem biasedHardwareStore2Check :
    (biasedStoreInputs false 2).any (biasedStoreCheck 2) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem biasedHardwareStore3Check :
    (biasedStoreInputs false 3).any (biasedStoreCheck 3) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem biasedMixedStore0Check :
    (biasedStoreInputs true 0).any (biasedStoreCheck 0) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem biasedMixedStore1Check :
    (biasedStoreInputs true 1).any (biasedStoreCheck 1) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem biasedMixedStore2Check :
    (biasedStoreInputs true 2).any (biasedStoreCheck 2) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem biasedMixedStore3Check :
    (biasedStoreInputs true 3).any (biasedStoreCheck 3) = true := by
  kernel_rfl

private theorem biasedAllStoreChecks (mixed : Bool) (q : Fin 4) :
    (biasedStoreInputs mixed q).any (biasedStoreCheck q) = true := by
  cases mixed
  · fin_cases q
    · exact biasedHardwareStore0Check
    · exact biasedHardwareStore1Check
    · exact biasedHardwareStore2Check
    · exact biasedHardwareStore3Check
  · fin_cases q
    · exact biasedMixedStore0Check
    · exact biasedMixedStore1Check
    · exact biasedMixedStore2Check
    · exact biasedMixedStore3Check

private theorem biasedExpStartStoreLocal (hp : Pre p l m) (stage : Fin 2) (mixed : Bool) {g : Nat}
    {t : TState} {args : ExponentArguments} {weights : Nat → ℝ} (hEval : ExponentEval args weights)
    (ht : At t 5815 [(634, .pred mixed)])
    (hRaw : ∀ i < 128, t.regs (1363 + i) = some (scoreValue (args.shifted i)))
    (hFrame : ∀ r ∈ biasedExpFrame, t.regs r = some (args.original r))
    (hSaved : ∀ r ∈ roundContinuationRegs, t.regs r = args.saved r)
    (hStage : args.original 637 = .pred (stage.val = 1))
    (hAddresses : ∀ q, args.original (probabilityReg .biased q) =
      b32 (probabilityAddress l g stage q)) :
    ∃ u regs, biasedStoreInputs mixed 0 = some regs ∧ At u 6508 [] ∧
      ExponentHolds args weights regs u ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨a, sa, hSA, hA, hRA, hPathA⟩ :=
    biasedExponentPrefixLocal (l := l) (g := g) mixed hEval ht hRaw hFrame hSaved
  obtain ⟨b, hB, hRB, hPathB⟩ :=
    biasedExponentAddressLocal hp stage mixed hSA hA hRA hStage hAddresses
  have hCheck := biasedAllStoreChecks mixed 0
  cases hOutput : biasedStoreInputs mixed 0 with
  | none => rw [hOutput, Option.any_none] at hCheck; cases hCheck
  | some regs =>
    have hRunTo : exponentRun biasedCode 6508 200 6308 (biasedPAddresses sa) = some regs := by
      simpa only [biasedStoreInputs, biasedStoreInputsNat, biasedExpOutput, hSA, Option.bind_some]
        using hOutput
    obtain ⟨u, hu, hU, hRegs⟩ :=
      exponentRun_sound (l := l) (g := g) hEval biasedCode biasedCode_sound
        200 6308 _ _ b hRunTo hB hRB
    exact ⟨u, regs, rfl, hU, hRegs, (hPathA.trans hPathB).trans hu⟩

private theorem biasedExpStartStore {X : Execution} (hp : Pre p l m) (stage : Fin 2) (mixed : Bool)
    {g j : Nat} {t : TState} {ending : Option TState} {args : ExponentArguments} {weights : Nat → ℝ}
    (hEval : ExponentEval args weights) (ht : At t 5815 [(634, .pred mixed)])
    (hRaw : ∀ i < 128, t.regs (1363 + i) = some (scoreValue (args.shifted i)))
    (hFrame : ∀ r ∈ biasedExpFrame, t.regs r = some (args.original r))
    (hSaved : ∀ r ∈ roundContinuationRegs, t.regs r = args.saved r)
    (hStage : args.original 637 = .pred (stage.val = 1))
    (hAddresses : ∀ q, args.original (probabilityReg .biased q) =
      b32 (probabilityAddress l g stage q))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j < (X.tr g).length) :
    ∃ u regs, biasedStoreInputs mixed 0 = some regs ∧ At u 6508 [] ∧
      ExponentHolds args weights regs u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨u,regs,hRegs,hAt,hWords,hLocal⟩ :=
    biasedExpStartStoreLocal hp stage mixed hEval ht hRaw hFrame hSaved hStage hAddresses
  exact ⟨u,regs,hRegs,hAt,hWords,hRun.after_local_nonempty hLocal
    (probabilitySuffixNonempty hRun hAvail),hLocal⟩

private theorem biasedStoreWords {l : Launch} (stage : Fin 2) (mixed : Bool)
    (q : Fin 4) {g : Nat} {t : TState}
    {args : ExponentArguments} {weights : Nat → ℝ} {regs : ExponentRegs}
    (hRegs : ExponentHolds args weights regs t)
    (hReady : biasedStoreInputs mixed q = some regs)
    (hAddr : args.original (probabilityReg .biased q) =
      b32 (probabilityAddress l g stage q)) :
    (biasedSources q).length = 16 ∧
      (∀ i (hi : i < (biasedSources q).length),
        t.regs (biasedSources q)[i] = some (probabilityWord weights (16*q.val+i))) ∧
      t.regs (probabilityReg .biased q) = some (b32 (probabilityAddress l g stage q)) := by
  have hCheck := biasedAllStoreChecks mixed q
  rw [hReady, Option.any_some] at hCheck
  simp only [biasedStoreCheck, Bool.and_eq_true] at hCheck
  have hWord (i : Nat) (hi : i < (biasedSources q).length) :
      t.regs (biasedSources q)[i] = some (probabilityWord weights (16 * q.val + i)) := by
    have hiz : i < (biasedSources q).zipIdx.length := by simpa using hi
    have hm := List.getElem_mem (l := (biasedSources q).zipIdx) hiz
    have h := List.all_eq_true.mp hCheck.1.1.1 _ hm
    simp only [List.getElem_zipIdx, Nat.zero_add] at h
    have hi0 : 2 * (16 * q.val + i) = 32 * q.val + 2 * i := by omega
    simpa only [ExponentValue.read, ExponentValue.value, ExponentWord.value, probabilityWord, hi0]
      using
      hRegs _ _ (hasWord_sound h)
  have hMem : probabilityReg .biased q ∈ (List.range 4).map (4821 + ·) := by
    fin_cases q <;> decide
  have hAddrT := hRegs _ _ (hasOriginal_sound (List.all_eq_true.mp hCheck.1.2 _ hMem))
  have hLen : (biasedSources q).length = 16 := by fin_cases q <;> decide
  exact ⟨hLen,hWord,hAddrT.trans (congrArg some hAddr)⟩

private theorem biasedStoreAt {X : Execution} (hp : Pre p l m) (stage : Fin 2) (mixed : Bool)
    (q : Fin 4) {g j : Nat} {t : TState} {ending : Option TState} {args : ExponentArguments}
    {weights : Nat → ℝ} {regs : ExponentRegs} (hRegs : ExponentHolds args weights regs t)
    (hReady : biasedStoreInputs mixed q = some regs) (ht : At t (probabilityPc .biased q) [])
    (hAddr : args.original (probabilityReg .biased q) = b32 (probabilityAddress l g stage q))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ (if delayedProbability .biased q then j+1 else j) < (X.tr g).length) :
    let k := if delayedProbability .biased q then j + 1 else j
    (delayedProbability .biased q = true →
      X.get (g, j) = some ⟨probabilityPc .biased q, .tc .waitLd⟩) ∧
      X.get (g, k) = some (repeatedStoreEvent l g stage .biased q weights) ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (k + 1)) ending ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (k+1-j)) (next t) := by
  obtain ⟨hLen,hWord,hAddress⟩ := biasedStoreWords stage mixed q hRegs hReady hAddr
  exact exponentStoreAt hp .biased stage q _ weights hLen ht (biasedStoreCode q)
    hWord hAddress hRun hAvail

private theorem nextBiasedStore {l : Launch} {X : Execution} {g j : Nat} {t : TState}
    {ending : Option TState}
    {args : ExponentArguments} {weights : Nat → ℝ} {regs : ExponentRegs}
    (mixed : Bool) (q : Fin 3) (hEval : ExponentEval args weights)
    (hBefore : biasedStoreInputs mixed (Fin.castSucc q) = some regs)
    (ht : At t (biasedStoreRunStart q) [])
    (hRegs : ExponentHolds args weights
      (if q.val = 2 then biasedClearSignal regs else regs) t)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j < (X.tr g).length) :
    ∃ u s, biasedStoreInputs mixed q.succ = some s ∧
      At u (probabilityPc .biased q.succ) [] ∧ ExponentHolds args weights s u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hCheck := biasedAllStoreChecks mixed q.succ
  cases hOutput : biasedStoreInputs mixed q.succ with
  | none => rw [hOutput, Option.any_none] at hCheck; cases hCheck
  | some s =>
    have hLink : nextBiasedRegs q regs = some s := by
      rw [biasedStoreInputs_succ, hBefore, Option.bind_some] at hOutput
      exact hOutput
    obtain ⟨u, hu, hU, hReg⟩ :=
      exponentRun_sound (l := l) (g := g) hEval biasedCode biasedCode_sound 8 _ _ _ t
        hLink ht hRegs
    exact ⟨u, s, rfl, hU, hReg, hRun.after_local_nonempty hu
      (probabilitySuffixNonempty hRun hAvail),hu⟩

private theorem biasedMainArrival {X : Execution} (hp : Pre p l m) (stage : Fin 2) (mixed : Bool)
    {g j : Nat} {t : TState} {ending : Option TState} {args : ExponentArguments} {weights : Nat → ℝ}
    {regs : ExponentRegs} (hRegs : ExponentHolds args weights regs t) (ht : At t 6527 [])
    (hReady : biasedStoreInputs mixed 2 = some regs)
    (hStage : args.original 637 = .pred (stage.val = 1))
    (hBase : args.original 2535 = b32 l.sharedBase)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+1 < (X.tr g).length) :
    ∃ u, X.get (g, j) = some ⟨6527, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨6532, .arrive (signalLoc l g stage 4) 0 1 true .cta⟩ ∧
      At u 6533 [] ∧ ExponentHolds args weights (biasedClearSignal regs) u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 2)) ending ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 2) u := by
  have hWaitTrace :
      X.get (g,j) = some ⟨probabilityWaitPc .biased false,.tc .waitSt⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j+1)) ending := by
    rcases hAvail with rfl | hi
    · exact probabilityWaitTrace hp .biased false ht.1 ht.2.2.2.1 hRun
    · exact probabilityWaitInPrefix hp .biased false ht.1 ht.2.2.2.1 hRun (by omega)
  obtain ⟨hWait,hTail⟩ := hWaitTrace
  have hCheck := biasedAllStoreChecks mixed 2
  rw [hReady, Option.any_some] at hCheck
  simp only [biasedStoreCheck, Bool.and_eq_true] at hCheck
  have hStageT : t.regs 637 = some (.pred (stage.val = 1)) :=
    (hRegs _ _ (hasOriginal_sound (List.all_eq_true.mp hCheck.1.1.2 637 (by decide)))).trans
      (congrArg some hStage)
  have hBaseT : t.regs 2535 = some (b32 l.sharedBase) :=
    (hRegs _ _ (hasOriginal_sound (List.all_eq_true.mp hCheck.1.1.2 2535 (by decide)))).trans
      (congrArg some hBase)
  have hT := ht.next.mono (G := firstPublicationFacts l stage .biased)
    ⟨hStageT, hBaseT, trivial⟩
  obtain ⟨v, hv, hV⟩ := firstPublicationSetup hp g .biased stage (next t) hT
  have hFrame := biasedReleaseFrame (t := next t) (u := v) (by rw [hT.1])
    (by rw [hT.1]; decide) hv
  have hSignalRun := hTail.after_local_nonempty (run_rtg hv)
    (probabilitySuffixNonempty hTail hAvail)
  have hAddr := hV.2.2.2.2.1
  have hCount := hV.2.2.2.2.2.1
  have hSignalTrace :
      X.get (g,j+1) = some ⟨(signalSite 4).pc,.arrive (signalLoc l g stage 4) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g (next (mbarStateDest v (some (signalSite 4).state)))
        ((X.tr g).drop ((j+1)+1)) ending := by
    rcases hAvail with rfl | hi
    · exact signalTrace hp stage 4 hV.1 hV.2.2.2.1 hAddr hCount hSignalRun
    · exact signalTraceInPrefix hp stage 4 hV.1 hV.2.2.2.1 hAddr hCount hSignalRun hi
  obtain ⟨hSignal,hAfter⟩ := hSignalTrace
  let w := next (mbarStateDest v (some 8603))
  have hW : At w 6533 [] :=
    ⟨congrArg (· + 1) hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, trivial⟩
  refine ⟨w,hWait,hSignal,hW,?_,hAfter,?_⟩
  · intro r x hr
    unfold biasedClearSignal at hr
    split at hr
    · cases hr
    · rename_i hn
      have hn0 : r ≠ 8603 := fun he => hn (he.symm ▸ List.Mem.head _)
      have hn1 : r ∉ biasedReleaseScratch := fun he => hn (List.Mem.tail _ he)
      simpa only [w, next, mbarStateDest, Function.update_of_ne hn0, hFrame r hn1] using hRegs r
        x hr
  · have hWaitStep : EStep kernel Assumptions.all l g t
        ⟨(probabilityWaitPc .biased false),.tc .waitSt⟩ (some (next t)) := by
      refine ⟨_,probabilityWaitTemplate hp .biased false ht.1 ht.2.2.2.1,?_,rfl⟩
      rw [ht.1]
      rfl
    have hSignalStep : EStep kernel Assumptions.all l g v
        ⟨(signalSite 4).pc,.arrive (signalLoc l g stage 4) 0 1 true .cta⟩ (some w) := by
      refine ⟨_,signalTemplate hp stage 4 (g := g) hV.1 hV.2.2.2.1 hAddr hCount,?_,rfl⟩
      rw [hV.1]
      rfl
    rw [show (2 : Nat) = 1+1 from rfl,List.take_add,List.drop_drop,
      probabilityEventSingleton hWait,probabilityEventSingleton hSignal]
    exact .event hWaitStep ((TraceReach.of_local (run_rtg hv)).append (.event hSignalStep (.refl
      _)))
end

private theorem hasPack_sound {regs : ExponentRegs} {r : Nat} {a b : ExponentWord}
    (h : hasPack regs r a b = true) : regs r = some (.pack a b) := by
  unfold hasPack at h
  split at h
  · rename_i x y hx
    rcases of_decide_eq_true h with ⟨h1, h2⟩
    rw [hx, h1, h2]
  · cases h

private theorem observedBiasedRegs {args : ExponentArguments} {weights : Nat → ℝ}
    {regs : ExponentRegs} {t : TState} (mixed : Bool) (q : Fin 4)
    (hReady : biasedStoreInputs mixed q = some regs) (hRegs : ExponentHolds args weights regs t) :
    RepeatedWeights .biased t weights ∧
      ∀ r ∈ biasedExpFrame, t.regs r = some (args.original r) := by
  have hCheck := biasedAllStoreChecks mixed q
  rw [hReady, Option.any_some] at hCheck
  simp only [biasedStoreCheck, biasedWeightCheck, Bool.and_eq_true] at hCheck
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    exact hRegs _ _ (hasWord_sound (List.all_eq_true.mp hCheck.2.1 _ hr))
  · intro r hr
    simpa only [ExponentValue.read, ExponentValue.value, ExponentWord.value, fl, joinValue] using
      hRegs _ _ (hasPack_sound (List.all_eq_true.mp hCheck.2.2 _ hr))
  · intro r hr
    exact hRegs _ _ (hasOriginal_sound (List.all_eq_true.mp hCheck.1.1.2 _ hr))

private def biasedOriginal (l : Launch) (g : Nat) (stage : Fin 2) (values : Nat → Value)
    (r : Nat) : Value :=
  ((biasedAddressFacts l g stage).lookup r).getD (values r)

private theorem biasedOriginalFrame (l : Launch) (g : Nat) (stage : Fin 2)
    (values : Nat → Value) {r : Nat} (hr : r ∈ biasedExpFrame) :
    biasedOriginal l g stage values r = values r := by
  simp only [biasedExpFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
private theorem biasedSavedAudit (mixed : Bool) :
    (biasedStoreInputs mixed 3).any (fun s => roundContinuationRegs.all (hasSaved s)) =
      true := by
  cases mixed <;> kernel_rfl

private theorem biasedStoreKeepsContinuation (mixed : Bool) {s : ExponentRegs} {r : Nat}
    (h : biasedStoreInputs mixed 3 = some s) (hr : r ∈ roundContinuationRegs) :
    s r = some (.saved r) := by
  have check := biasedSavedAudit mixed
  rw [h, Option.any_some] at check
  exact hasSaved_sound (List.all_eq_true.mp check _ hr)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (stage : Fin 2)
    (mixed : Bool) {g j : Nat} {t : TState} (raw : Nat → Option ℝ) (weights : Nat → ℝ)
    (values : Nat → Value) (ht : At t 5815 [(634, .pred mixed)])
    (hRaw : ∀ i < 128, t.regs (1363 + i) = some (scoreValue (raw i)))
    (hHardware : ∀ i, ex2E true (scoreValue (raw i)) = .ok (fl (weights i)))
    (hSoftware : ∀ i, Assumptions.swExp2Lane (scoreValue (raw i)) = .ok (weights i))
    (hFrame : ∀ r ∈ biasedExpFrame, t.regs r = some (values r))
    (hStage : values 637 = .pred (stage.val = 1)) (hBase : values 2535 = b32 l.sharedBase)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp stage mixed raw weights values ht hRaw hHardware hSoftware hFrame hStage hBase hRun

/-- Both biased exponent paths execute the four P writes with the same column order. The
first write applies the modeled TMEM load wait, and the first three stores finish before
the CTA's main P notification. The FP32 mixed-layout weights remain live for the sum. -/
theorem biasedProbabilityStoresWithPath :
    ∃ u, X.get (g, j) = some ⟨6508, .tc .waitLd⟩ ∧
      X.get (g, j + 1) = some (repeatedStoreEvent l g stage .biased 0 weights) ∧
      X.get (g, j + 2) = some (repeatedStoreEvent l g stage .biased 1 weights) ∧
      X.get (g, j + 3) = some (repeatedStoreEvent l g stage .biased 2 weights) ∧
      X.get (g, j + 4) = some ⟨6527, .tc .waitSt⟩ ∧
      X.get (g, j + 5) = some ⟨6532, .arrive (signalLoc l g stage 4) 0 1 true .cta⟩ ∧
      X.get (g, j + 6) = some (repeatedStoreEvent l g stage .biased 3 weights) ∧
      At u 6542 [] ∧ RepeatedWeights .biased u weights ∧
      (∀ r ∈ biasedExpFrame, u.regs r = some (values r)) ∧
      (∀ r ∈ roundContinuationRegs, u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 7)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 7) u := by
  let args : ExponentArguments := ⟨raw, biasedOriginal l g stage values, t.regs⟩
  have hEval : ExponentEval args weights := ⟨hHardware, hSoftware⟩
  have hAddr (q : Fin 4) : args.original (probabilityReg .biased q) =
      b32 (probabilityAddress l g stage q) := by fin_cases q <;> rfl
  have hFrame' (r : Nat) (hr : r ∈ biasedExpFrame) : t.regs r = some (args.original r) :=
    (hFrame r hr).trans (congrArg some (biasedOriginalFrame l g stage values hr).symm)
  have hStage' : args.original 637 = .pred (stage.val = 1) := hStage
  have hBase' : args.original 2535 = b32 l.sharedBase := hBase
  obtain ⟨t0, s0, hs0, hAt0, hRegs0, hTail0,hLocal0⟩ :=
    biasedExpStartStore hp stage mixed hEval ht hRaw hFrame'
      (fun _ _ => rfl) hStage' hAddr hRun (.inl rfl)
  obtain ⟨hWaitLd, hStore0, hAfter0,hStorePath0⟩ :=
    biasedStoreAt hp stage mixed 0 hRegs0 hs0 hAt0 (hAddr 0) hTail0 (.inl rfl)
  obtain ⟨t1, s1, hs1, hAt1, hRegs1, hTail1,hLocal1⟩ :=
    nextBiasedStore mixed 0 hEval hs0 hAt0.next hRegs0 hAfter0 (.inl rfl)
  obtain ⟨_, hStore1, hAfter1,hStorePath1⟩ :=
    biasedStoreAt hp stage mixed 1 hRegs1 hs1 hAt1 (hAddr 1) hTail1 (.inl rfl)
  obtain ⟨t2, s2, hs2, hAt2, hRegs2, hTail2,hLocal2⟩ :=
    nextBiasedStore mixed 1 hEval hs1 hAt1.next hRegs1 hAfter1 (.inl rfl)
  obtain ⟨_, hStore2, hAfter2,hStorePath2⟩ :=
    biasedStoreAt hp stage mixed 2 hRegs2 hs2 hAt2 (hAddr 2) hTail2 (.inl rfl)
  obtain ⟨t3, hWaitSt, hArrive, hAt3, hRegs3, hTail3,hLocal3⟩ :=
    biasedMainArrival hp stage mixed (t := next t2) hRegs2 hAt2.next hs2 hStage' hBase'
      hAfter2 (.inl rfl)
  obtain ⟨t4, s4, hs4, hAt4, hRegs4, hTail4,hLocal4⟩ :=
    nextBiasedStore mixed 2 hEval hs2 hAt3 hRegs3 hTail3 (.inl rfl)
  obtain ⟨_, hStore3, hAfter3,hStorePath3⟩ :=
    biasedStoreAt hp stage mixed 3 hRegs4 hs4 hAt4 (hAddr 3) hTail4 (.inl rfl)
  obtain ⟨hWeights, hKeep⟩ := observedBiasedRegs mixed 3 hs4 hRegs4
  refine ⟨next t4, hWaitLd rfl, hStore0, hStore1, hStore2, hWaitSt, hArrive, hStore3,
    hAt4.next, ⟨hWeights.scalar, hWeights.packed⟩, fun r hr =>
      (hKeep r hr).trans (congrArg some (biasedOriginalFrame l g stage values hr)),
    fun r hr => hRegs4 _ _ (biasedStoreKeepsContinuation mixed hs4 hr), hAfter3,?_⟩

  change TraceReach kernel Assumptions.all l g t0
    (((X.tr g).drop j).take (j+2-j)) (next t0) at hStorePath0
  change TraceReach kernel Assumptions.all l g t1
    (((X.tr g).drop (j+2)).take (j+2+1-(j+2))) (next t1) at hStorePath1
  change TraceReach kernel Assumptions.all l g t2
    (((X.tr g).drop (j+3)).take (j+3+1-(j+3))) (next t2) at hStorePath2
  change TraceReach kernel Assumptions.all l g t4
    (((X.tr g).drop (j+6)).take (j+6+1-(j+6))) (next t4) at hStorePath3
  simp only [Nat.add_sub_cancel_left] at hStorePath0 hStorePath1 hStorePath2 hStorePath3
  have hFirst := preProbabilityLocal hLocal0 hStorePath0
  have hSecond := appendProbabilityPath (a := 2) (b := 1) hFirst
    (preProbabilityLocal hLocal1 hStorePath1)
  have hThird := appendProbabilityPath (a := 3) (b := 1) hSecond
    (preProbabilityLocal hLocal2 hStorePath2)
  have hSignalPath := appendProbabilityPath (a := 4) (b := 2) hThird hLocal3
  exact appendProbabilityPath (a := 6) (b := 1) hSignalPath
    (preProbabilityLocal hLocal4 hStorePath3)

end
/-- The address-independent event offset of a repeated probability quarter. -/
def Repeated.probabilityStoreOffset (mode : Repeated) (q : Fin 4) : Nat :=
  if q.val = 3 then (if mode = .biased then 6 else 5)
  else q.val + (if mode = .biased then 1 else 0)

private theorem probabilityStoreOffsetBound (mode : Repeated) (q : Fin 4) :
    q.val + (if mode = .biased then 1 else 0) ≤ mode.probabilityStoreOffset q := by
  cases mode <;> fin_cases q <;> decide

private theorem probabilityLateQuarters (q : Fin 4) (hZero : q ≠ 0) (hFirst : q ≠ 1) :
    q = 2 ∨ q = 3 := by
  fin_cases q <;> first | decide | contradiction

private theorem probabilityLateQuarterValue (q : Fin 4) (hZero : q ≠ 0) (hFirst : q ≠ 1) :
    2 ≤ q.val := by
  fin_cases q <;> first | decide | contradiction

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Replay only the portion of the plain exponent and store sequence needed by the
selected quarter. The observed thread can stop immediately after that store. -/
theorem unbiasedProbabilityStoreOfPrefix (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState}
    {ending : Option TState} (q : Fin 4) (raw : Nat → Option ℝ) (weights : Nat → ℝ)
    (values : Nat → Value) (ht : At t 7022 [])
    (hRaw : ∀ i < 128, t.regs (5520 + i) = some (scoreValue (raw i)))
    (hHardware : ∀ i, ex2E true (scoreValue (raw i)) = .ok (fl (weights i)))
    (hSoftware : ∀ i, Assumptions.swExp2Lane (scoreValue (raw i)) = .ok (weights i))
    (hFrame : ∀ r ∈ unbiasedExpFrame, t.regs r = some (values r))
    (hAddr : ∀ quarter, values (probabilityReg .unbiased quarter) =
      b32 (probabilityAddress l g stage quarter))
    (hSignal : values 5187 = b32 (l.sharedBase + 8 * stage.val))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+Repeated.unbiased.probabilityStoreOffset q < (X.tr g).length) :
    X.get (g,j+Repeated.unbiased.probabilityStoreOffset q) =
      some (unbiasedStoreEvent l g stage q weights) := by
  let args : ExponentArguments := ⟨raw, values, t.regs⟩
  have hEval : ExponentEval args weights := ⟨hHardware, hSoftware⟩
  have avail {i : Nat} (hi : i ≤ Repeated.unbiased.probabilityStoreOffset q) :
      ending = none ∨ j+i < (X.tr g).length :=
    probabilityAvailableEarlier hAvail (Nat.add_le_add_left hi j)
  have hAvail0 : ending = none ∨ j < (X.tr g).length := by simpa using (avail (Nat.zero_le _))
  obtain ⟨t0,s0,hs0,hAt0,hRegs0,hTail0,_⟩ :=
    unbiasedExpStart hEval ht hRaw hFrame (fun _ _ => rfl) hRun hAvail0
  obtain ⟨hStore0,hAfter0,_⟩ := unbiasedStoreAt hp stage 0 hRegs0 hs0 hAt0 (hAddr 0) hTail0 hAvail0
  by_cases hZero : q = 0
  · subst q
    exact hStore0
  have hPositive : 1 ≤ q.val :=
    Nat.pos_of_ne_zero (fun h => hZero (Fin.ext h))
  have hOffset : q.val ≤ Repeated.unbiased.probabilityStoreOffset q :=
    probabilityStoreOffsetBound .unbiased q
  have hOne := hPositive.trans hOffset
  obtain ⟨t1,s1,hs1,hAt1,hRegs1,hTail1,_⟩ :=
    nextUnbiasedStore 0 hEval hs0 hAt0.next hRegs0 hAfter0 (avail hOne)
  obtain ⟨hStore1,hAfter1,_⟩ :=
     unbiasedStoreAt hp stage 1 hRegs1 hs1 hAt1 (hAddr 1) hTail1 (avail hOne)
  by_cases hFirst : q = 1
  · subst q
    exact hStore1
  have hTwo := (probabilityLateQuarterValue q hZero hFirst).trans hOffset
  obtain ⟨t2,s2,hs2,hAt2,hRegs2,hTail2,_⟩ :=
    nextUnbiasedStore 1 hEval hs1 hAt1.next hRegs1 hAfter1 (avail hTwo)
  obtain ⟨hStore2,hAfter2,_⟩ :=
     unbiasedStoreAt hp stage 2 hRegs2 hs2 hAt2 (hAddr 2)
      hTail2 (avail hTwo)
  have hFinal := probabilityLateQuarters q hZero hFirst
  rcases hFinal with rfl | rfl
  · exact hStore2
  have hFour : ending = none ∨ (j+3)+1 < (X.tr g).length := avail (i := 4) (by decide)
  obtain ⟨t3,_,_,hAt3,hRegs3,hTail3,_⟩ :=
    unbiasedMainArrival hp stage (t := next t2) hRegs2 hAt2.next hs2 hSignal hAfter2 hFour
  have hFive : ending = none ∨ ((j+3)+2) < (X.tr g).length := avail (i := 5) (by decide)
  obtain ⟨_,_,hs4,hAt4,hRegs4,hTail4,_⟩ :=
    nextUnbiasedStore 2 hEval hs2 hAt3 hRegs3 hTail3 hFive
  exact (unbiasedStoreAt hp stage 3 hRegs4 hs4 hAt4 (hAddr 3) hTail4 hFive).1

/-- Both FP32 exponent paths in the biased round give the recorded quarter's BF16
words before any requirement on the remaining lane trace. -/
theorem biasedProbabilityStoreOfPrefix (hp : Pre p l m) (stage : Fin 2) (mixed : Bool) {g j : Nat}
    {t : TState} {ending : Option TState} (q : Fin 4) (raw : Nat → Option ℝ) (weights : Nat → ℝ)
    (values : Nat → Value) (ht : At t 5815 [(634,.pred mixed)])
    (hRaw : ∀ i < 128, t.regs (1363+i) = some (scoreValue (raw i)))
    (hHardware : ∀ i, ex2E true (scoreValue (raw i)) = .ok (fl (weights i)))
    (hSoftware : ∀ i, Assumptions.swExp2Lane (scoreValue (raw i)) = .ok (weights i))
    (hFrame : ∀ r ∈ biasedExpFrame, t.regs r = some (values r))
    (hStage : values 637 = .pred (stage.val = 1)) (hBase : values 2535 = b32 l.sharedBase)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+Repeated.biased.probabilityStoreOffset q < (X.tr g).length) :
    X.get (g,j+Repeated.biased.probabilityStoreOffset q) =
      some (repeatedStoreEvent l g stage .biased q weights) := by
  let args : ExponentArguments := ⟨raw, biasedOriginal l g stage values, t.regs⟩
  have hEval : ExponentEval args weights := ⟨hHardware, hSoftware⟩
  have hAddr (quarter : Fin 4) : args.original (probabilityReg .biased quarter) =
      b32 (probabilityAddress l g stage quarter) := by fin_cases quarter <;> rfl
  have hFrame' (r : Nat) (hr : r ∈ biasedExpFrame) : t.regs r = some (args.original r) :=
    (hFrame r hr).trans (congrArg some (biasedOriginalFrame l g stage values hr).symm)
  have hStage' : args.original 637 = .pred (stage.val = 1) := hStage
  have hBase' : args.original 2535 = b32 l.sharedBase := hBase
  have avail {i : Nat} (hi : i ≤ Repeated.biased.probabilityStoreOffset q) :
      ending = none ∨ j+i < (X.tr g).length :=
    probabilityAvailableEarlier hAvail (Nat.add_le_add_left hi j)
  have hAvail0 : ending = none ∨ j < (X.tr g).length := by simpa using (avail (Nat.zero_le _))
  have hOffset : q.val+1 ≤ Repeated.biased.probabilityStoreOffset q :=
    probabilityStoreOffsetBound .biased q
  have hOne := (Nat.succ_le_succ (Nat.zero_le q.val)).trans hOffset
  obtain ⟨t0,s0,hs0,hAt0,hRegs0,hTail0,_⟩ :=
    biasedExpStartStore hp stage mixed hEval ht hRaw hFrame' (fun _ _ => rfl)
      hStage' hAddr hRun hAvail0
  obtain ⟨_,hStore0,hAfter0,_⟩ :=
    biasedStoreAt hp stage mixed 0 hRegs0 hs0 hAt0 (hAddr 0) hTail0 (avail hOne)
  by_cases hZero : q = 0
  · subst q
    exact hStore0
  have hPositive : 1 ≤ q.val :=
    Nat.pos_of_ne_zero (fun h => hZero (Fin.ext h))
  have hTwo := (Nat.succ_le_succ hPositive).trans hOffset
  obtain ⟨t1,s1,hs1,hAt1,hRegs1,hTail1,_⟩ :=
    nextBiasedStore mixed 0 hEval hs0 hAt0.next hRegs0 hAfter0 (avail hTwo)
  obtain ⟨_,hStore1,hAfter1,_⟩ :=
    biasedStoreAt hp stage mixed 1 hRegs1 hs1 hAt1 (hAddr 1) hTail1 (avail hTwo)
  by_cases hFirst : q = 1
  · subst q
    exact hStore1
  have hThree := (Nat.succ_le_succ (probabilityLateQuarterValue q hZero hFirst)).trans hOffset
  obtain ⟨t2,s2,hs2,hAt2,hRegs2,hTail2,_⟩ :=
    nextBiasedStore mixed 1 hEval hs1 hAt1.next hRegs1 hAfter1 (avail hThree)
  obtain ⟨_,hStore2,hAfter2,_⟩ :=
    biasedStoreAt hp stage mixed 2 hRegs2 hs2 hAt2 (hAddr 2) hTail2 (avail hThree)
  have hFinal := probabilityLateQuarters q hZero hFirst
  rcases hFinal with rfl | rfl
  · exact hStore2
  have hFive : ending = none ∨ (j+4)+1 < (X.tr g).length := avail (i := 5) (by decide)
  obtain ⟨t3,_,_,hAt3,hRegs3,hTail3,_⟩ :=
    biasedMainArrival hp stage mixed (t := next t2) hRegs2 hAt2.next hs2 hStage' hBase'
      hAfter2 hFive
  have hSix : ending = none ∨ (j+4)+2 < (X.tr g).length := avail (i := 6) (by decide)
  obtain ⟨_,_,hs4,hAt4,hRegs4,hTail4,_⟩ :=
    nextBiasedStore mixed 2 hEval hs2 hAt3 hRegs3 hTail3 hSix
  exact (biasedStoreAt hp stage mixed 3 hRegs4 hs4 hAt4 (hAddr 3) hTail4 hSix).2.1

end PTX.Kernels.TmlFa4Fwd.Softmax
