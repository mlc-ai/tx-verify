-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmMax
public import Lemmas.Flow.Ex2Core
public import Lemmas.Flow.SetpCore

@[expose] public section

/-! # Floating steps of the score stage on extended reals

The local steps of the stage's floating instructions (`sub.f32`, `mul.f32`, `fma.rn.f32`,
`setp`, `selp.f32`, `ex2.approx.ftz.f32`) on operands that are values of extended reals (a number
or the pattern of `-inf`, `erealValue`), under the ideal-real reading of `Assumptions.idealArith`
and the exact `ex2` of `Assumptions.approx` (the Core table gives `ex2(-inf) = +0`).

`fiAt pc f` says the instruction at `pc` is the floating instruction `f`, and the step lemmas
take the instruction as written (`.float f`) with the registers it reads. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-- `sub.f32 d, a, b` (no rounding modifier). -/
abbrev subOp (d a b : Nat) : Op :=
  .float { op := .sub, ty := ty1 .f32, dsts := [some d], srcs := [.reg a, .reg b] }

/-- `sub.f32 d, a, b` of registers that read as extended reals `x`, `y` whose difference
`x + -y` exists. -/
theorem exec_subE {t : TState} {d a b : Nat} {va vb : Value} {x y r : EReal}
    (hI : IdealAt asms (.subRn .f32) L g t) (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hx : readEReal .f32 va = some (.ok x)) (hy : readEReal .f32 vb = some (.ok y))
    (hr : addEReal x (-y) = some r) :
    execLocalA asms L g t (subOp d a b) = .ok (PTX.next (setReg t d (erealValue .f32 r))) := by
  have hop : FloatForm.ofOp (subOp d a b) = some (.subRn .f32) := by
    simp [FloatForm.ofOp]
  have hex : execIdealFloat L g t (subOp d a b) =
      some (.ok (PTX.next (setReg t d (erealValue .f32 r)))) := by
    simp only [execIdealFloat, readERealOpnd_reg ha, readERealOpnd_reg hb, hx, hy, bindRead, hr,
      Option.map_some, pure, Except.pure]
  rw [hI _ hop _ hex]

/-- `mul.f32 d, a, b` (no rounding modifier). -/
abbrev mulOp (d a b : Nat) : Op :=
  .float { op := .mul, ty := ty1 .f32, dsts := [some d], srcs := [.reg a, .reg b] }

theorem exec_mulE {t : TState} {d a b : Nat} {va vb : Value} {x y r : EReal}
    (hI : IdealAt asms (.mul .f32) L g t) (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hx : readEReal .f32 va = some (.ok x)) (hy : readEReal .f32 vb = some (.ok y))
    (hr : mulEReal x y = some r) :
    execLocalA asms L g t (mulOp d a b) = .ok (PTX.next (setReg t d (erealValue .f32 r))) := by
  have hop : FloatForm.ofOp (mulOp d a b) = some (.mul .f32) := by simp [FloatForm.ofOp]
  have hex : execIdealFloat L g t (mulOp d a b) =
      some (.ok (PTX.next (setReg t d (erealValue .f32 r)))) := by
    simp only [execIdealFloat, readERealOpnd_reg ha, readERealOpnd_reg hb, hx, hy, bindRead, hr,
      Option.map_some, pure, Except.pure]
  rw [hI _ hop _ hex]

/-- `fma.rn.f32 d, a, b, c`. -/
abbrev fmaOp (d a b c : Nat) : Op :=
  .float { op := .fma, ty := ty1 .f32, rnd := some .rn, dsts := [some d],
           srcs := [.reg a, .reg b, .reg c] }

theorem exec_fmaEE {t : TState} {d a b c : Nat} {va vb vc : Value} {x y z r : EReal}
    (hI : IdealAt asms (.fma .f32) L g t) (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hc : t.regs c = some vc) (hx : readEReal .f32 va = some (.ok x))
    (hy : readEReal .f32 vb = some (.ok y)) (hz : readEReal .f32 vc = some (.ok z))
    (hr : (mulEReal x y).bind (addEReal · z) = some r) :
    execLocalA asms L g t (fmaOp d a b c) = .ok (PTX.next (setReg t d (erealValue .f32 r))) := by
  have hop : FloatForm.ofOp (fmaOp d a b c) = some (.fma .f32) := by simp [FloatForm.ofOp]
  have hex : execIdealFloat L g t (fmaOp d a b c) =
      some (.ok (PTX.next (setReg t d (erealValue .f32 r)))) := by
    simp only [execIdealFloat, readERealOpnd_reg ha, readERealOpnd_reg hb, readERealOpnd_reg hc,
      hx, hy, hz, bindRead, hr, Option.map_some, pure, Except.pure]
  rw [hI _ hop _ hex]

/-- `setp.cmp.f32 p, a, imm` with a constant that is not an infinity. -/
abbrev setpOp (cmp : Cmp) (p a imm : Nat) : Op :=
  .float { op := .setp (.ord cmp) none, ty := ty1 .f32, dsts := [some p],
           srcs := [.reg a, .f32imm imm] }

theorem exec_setpEI {t : TState} {cmp : Cmp} {p a imm : Nat} {va : Value} {x y : EReal}
    (hI : IdealAt asms (.setp .f32) L g t) (ha : t.regs a = some va)
    (hx : readEReal .f32 va = some (.ok x))
    (hy : readEReal .f32 (.bits 32 (BitVec.ofNat 64 imm)) = some (.ok y))
    (hinf : (imm == 0xFF800000 || imm == 0x7F800000) = false) :
    execLocalA asms L g t (setpOp cmp p a imm) =
      .ok (PTX.next (setReg t p (.pred (erealCompare cmp x y)))) := by
  have hop : FloatForm.ofOp (setpOp cmp p a imm) = some (.setp .f32) := by
    simp [FloatForm.ofOp, isInfConst, hinf]
  have hex : execIdealFloat L g t (setpOp cmp p a imm) =
      some (.ok (PTX.next (setReg t p (.pred (erealCompare cmp x y))))) := by
    have hra : readERealOpnd t .f32 (.reg a) = some (.ok x) := by
      rw [readERealOpnd_reg ha]; exact hx
    have hrb : readERealOpnd t .f32 (.f32imm imm) = some (.ok y) := hy
    simp only [execIdealFloat, hra, hrb, bindRead, pure, Except.pure]
  rw [hI _ hop _ hex]

/-- `setp.cmp.f32 p, a, imm` with an infinite constant (`0fFF800000`, `0f7F800000`). -/
theorem exec_setpEInf {t : TState} {cmp : Cmp} {p a imm : Nat} {va : Value} {x y : EReal}
    (hI : IdealAt asms (.setpInf .f32) L g t) (ha : t.regs a = some va)
    (hx : readEReal .f32 va = some (.ok x))
    (hy : readEReal .f32 (.bits 32 (BitVec.ofNat 64 imm)) = some (.ok y))
    (hinf : (imm == 0xFF800000 || imm == 0x7F800000) = true) :
    execLocalA asms L g t (setpOp cmp p a imm) =
      .ok (PTX.next (setReg t p (.pred (erealCompare cmp x y)))) := by
  have hop : FloatForm.ofOp (setpOp cmp p a imm) = some (.setpInf .f32) := by
    simp [FloatForm.ofOp, isInfConst, hinf]
  have hex : execIdealFloat L g t (setpOp cmp p a imm) =
      some (.ok (PTX.next (setReg t p (.pred (erealCompare cmp x y))))) := by
    have hra : readERealOpnd t .f32 (.reg a) = some (.ok x) := by
      rw [readERealOpnd_reg ha]; exact hx
    have hrb : readERealOpnd t .f32 (.f32imm imm) = some (.ok y) := hy
    simp only [execIdealFloat, hra, hrb, bindRead, pure, Except.pure]
  rw [hI _ hop _ hex]

/-- `selp.f32 d, a, b, p`: `a` where the predicate `p` holds, else `b`. -/
abbrev selpOp (d : Nat) (a b : Opnd) (p : Nat) : Op :=
  .int ⟨.selp, .float .f32, false, [some d], [a, b, .reg p]⟩

theorem exec_selp {t : TState} {d p : Nat} {a b : Opnd} {va vb : Value} {pick : Bool}
    (hS : Assumption.SegFreePc asms t.pc) (hp : t.regs p = some (.pred pick))
    (ha : readValue L g t 32 a = .ok va) (hb : readValue L g t 32 b = .ok vb)
    (hba : va.bytes = 4) (hbb : vb.bytes = 4) :
    execLocalA asms L g t (selpOp d a b p) =
      .ok (PTX.next (setReg t d (if pick then va else vb))) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  cases pick <;>
  simp [selpOp, execLocal, Op.rule, IntInstr.rule, execMove, DType.width, readReg, hp, ha, hb,
    hba, hbb, bind, Except.bind, pure, Except.pure]

/-- The operand read of a register. -/
theorem readValue_reg {t : TState} {r : Nat} {v : Value} (h : t.regs r = some v) :
    readValue L g t 32 (.reg r) = .ok v := by
  simp [readValue, readReg, h, pure, Except.pure]

/-- The operand read of a `0f` constant. -/
theorem readValue_imm {t : TState} {b : Nat} :
    readValue L g t 32 (.f32imm b) = .ok (.bits 32 (BitVec.ofNat 64 b)) := rfl

/-! ### `ex2.approx.ftz.f32` -/

/-- At a pc of the stage that is no software-`exp2` instance and no single-instruction reading's
site, `ex2.approx.f32` is the exact power of two on a finite operand and takes the Core rule
(the table: `ex2(-inf) = +0`) on another. -/
theorem approxAt_ex2 {t : TState} (h : Assumptions.emuSites.contains t.pc = false)
    (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600) (h3 : t.pc ≠ 807) :
    ApproxAt asms (.ex2 .f32) L g t ∧ ApproxDeclineAt asms (.ex2 .f32) L g t := by
  have key : ∀ op, Assumption.ApproxForm.ofOp op = some (.ex2 .f32) →
      execLocalA asms L g t op = match Assumption.execApproxExact t op with
        | some r => r
        | none => execLocal L g t op := by
    intro op hf
    rw [(segFree h).exec rfl]
    have h1' : Assumptions.idealArith.localRule L g t op = none :=
      Assumption.idealReal_localRule_none fun f' h' => by
        rw [Flow.floatForm_none_of_approx hf] at h'; cases h'
    have h3' : Assumptions.approx.localRule L g t op = Assumption.execApproxExact t op :=
      Assumption.approxExact_localRule_of hf (by simp)
    have h4 := asms_tail_none' (L := L) (g := g) (t := t) (op := op) h1 h2 h3 (fun c hc => by
      subst hc
      simp [Assumption.ApproxForm.ofOp] at hf)
    have h4a := h4 _ (show Assumptions.swExp2 kernel ∈ asms.drop 2 by simp [asms, Assumptions.all])
    have h4b := h4 _ (show Assumptions.lg2Exact ∈ asms.drop 2 by simp [asms, Assumptions.all])
    have h4c := h4 _ (show Assumptions.divFullExact ∈ asms.drop 2 by simp [asms, Assumptions.all])
    have h4d := h4 _ (show Assumptions.negExact ∈ asms.drop 2 by simp [asms, Assumptions.all])
    have h4e := h4 _ (show Assumptions.bf16Exact ∈ asms.drop 2 by simp [asms, Assumptions.all])
    simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1', h3', h4a, h4b, h4c,
      h4d, h4e]
    rcases hE : Assumption.execApproxExact t op with _ | r <;> rfl
  exact ⟨fun op hf e he => by rw [key op hf, he], fun op hf he => by rw [key op hf, he]⟩

/-- `ex2.approx.ftz.f32 d, a`. -/
abbrev ex2Op (d a : Nat) : Op := .float { ex2I true with dsts := [some d], srcs := [.reg a] }

/-- The power of two of an extended real that is not `+inf`. -/
theorem ex2E_ereal {x : EReal} (hx : x ≠ ⊤) :
    ex2E true (erealValue .f32 x) = .ok (.float .f32 (Softmax.pow2 x)) := by
  induction x using EReal.rec with
  | bot =>
    rw [erealValue_bot']
    unfold ex2E
    simp only [ex2Val]
    rfl
  | coe y =>
    rw [erealValue_coe, ex2E_fin (valFloat_float y)]
    simp [Softmax.pow2, EReal.coe_ne_bot, Real.rpow_eq_pow]
  | top => exact absurd rfl hx

/-- **`ex2.approx.ftz.f32` of a value of an extended real** (not `+inf`) at a pc of the stage:
the exact power of two, `0` for `-inf`. -/
theorem exec_ex2V {t : TState} {d a : Nat} {x : EReal} (hx : x ≠ ⊤)
    (h : Assumptions.emuSites.contains t.pc = false) (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600)
    (h3 : t.pc ≠ 807) (ha : t.regs a = some (erealValue .f32 x)) :
    execLocalA asms L g t (ex2Op d a) =
      .ok (PTX.next (setReg t d (.float .f32 (Softmax.pow2 x)))) := by
  obtain ⟨hA, hD⟩ := approxAt_ex2 (L := L) (g := g) h h1 h2 h3
  rw [exec_ex2E hA hD (OpndIs.reg ha), ex2E_ereal hx]
  rfl

/-! ### The software `exp2` instance -/

/-- The slot-register assignment of the instance at `pc`. -/
def emuAsg (pc : Nat) : List (Assumptions.EmuSlot × Nat) :=
  (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) []).getD []

/-- The registers an instance writes (the temporaries and the output). -/
def emuW (pc : Nat) : List Nat := Assumptions.emuWrites.map (Assumptions.emuReg (emuAsg pc))

/-- The instance at `pc` is one of the program's, with a floating first instruction. -/
def emuOk (pc : Nat) : Bool :=
  Assumptions.emuSites.contains pc &&
    (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) []).isSome &&
    (match kernel.code[pc]? with | some ⟨none, .float _⟩ => true | _ => false)

/-- The facts after an instance are the facts before with the output (`emuReg y`) the exact power
of two of the input (`emuReg x`), a value of the extended real `x`; the temporaries are dead. -/
theorem seg_emu {pc : Nat} {x : EReal} {liveS liveT : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} (hok : emuOk pc = true) (hx : x ≠ ⊤)
    (hsl : Assumptions.emuReg (emuAsg pc) .x ∈ liveS)
    (hv : valueEx base ex (Assumptions.emuReg (emuAsg pc) .x) = erealValue .f32 x)
    (hcov : ∀ r ∈ liveT, r = Assumptions.emuReg (emuAsg pc) .y ∨ (r ∉ emuW pc ∧ r ∈ liveS)) :
    Seg kernel asms L g 1 pc (factsFrom liveS (valueEx base ex)) (pc + 11)
      (factsFrom liveT (valueEx base ((Assumptions.emuReg (emuAsg pc) .y,
        .float .f32 (Softmax.pow2 x)) :: ex))) := by
  simp only [emuOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hs, hm⟩, hc⟩ := hok
  obtain ⟨asg, hasg⟩ := Option.isSome_iff_exists.mp hm
  have hea : emuAsg pc = asg := by simp [emuAsg, hasg]
  obtain ⟨f, hcf⟩ : ∃ f, kernel.code[pc]? = some ⟨none, .float f⟩ := by
    cases hh : kernel.code[pc]? with
    | none => simp [hh] at hc
    | some ins =>
      obtain ⟨gd, op⟩ := ins
      cases gd <;> cases op <;> simp [hh] at hc ⊢
  rw [hea] at hsl hv hcov ⊢
  have hw : emuW pc = Assumptions.emuWrites.map (Assumptions.emuReg asg) := by
    simp [emuW, hea]
  intro t h
  have hR := h.2.2.2.2
  have hxreg := holds_mem hR (mem_factsFrom (val := valueEx base ex) hsl)
  rw [hv] at hxreg
  have hpc : t.pc = pc := h.1
  have hex : Assumptions.execEmu asg t = some (.ok { t with
      regs := Function.update (Assumptions.emuWrites.foldl
        (fun rs s => Function.update rs (Assumptions.emuReg asg s) none) t.regs)
        (Assumptions.emuReg asg .y) (some (.float .f32 (Softmax.pow2 x))),
      pc := t.pc + Assumptions.emuBody.length, sub := 0, acc := [] }) := by
    simp only [Assumptions.execEmu, readERealOpnd_reg hxreg, readEReal_erealValue hx, bindRead, hx,
      ↓reduceIte, pure, Except.pure]
    rfl
  set t' : TState := { t with
      regs := Function.update (Assumptions.emuWrites.foldl
        (fun rs s => Function.update rs (Assumptions.emuReg asg s) none) t.regs)
        (Assumptions.emuReg asg .y) (some (.float .f32 (Softmax.pow2 x))),
      pc := t.pc + Assumptions.emuBody.length, sub := 0, acc := [] } with ht'
  have hrule : (Assumptions.swExp2 kernel).segmentRule L g t = some (.ok t') := by
    show (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
      (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
        (Assumptions.execEmu · t) else none) = _
    rw [if_pos ⟨by rw [hpc]; exact hs, h.2.1, by simp [h.2.2.1]⟩, hpc, hasg]
    exact hex
  have hrun : run kernel asms L g 1 t = some t' :=
    run_select (A₁ := [Assumptions.idealArith, Assumptions.approx])
      (A₂ := [Assumptions.lg2Exact, Assumptions.divFullExact, Assumptions.negExact,
        Assumptions.bf16Exact]) hcf rfl h hrule
  have hcov' : ∀ r ∈ liveT, r ∈ [(Assumptions.emuReg asg .y,
      Value.float .f32 (Softmax.pow2 x))].map Prod.fst ∨ (r ∉ emuW pc ∧ r ∈ liveS) := by
    intro r hr
    rcases hcov r hr with he | ⟨hn, hl⟩
    · exact Or.inl (by simp [he])
    · exact Or.inr ⟨hn, hl⟩
  refine ⟨t', hrun, ?_, rfl, rfl, h.2.2.2.1, ?_⟩
  · simp only [ht', hpc]; rfl
  · refine holds_ext (W := emuW pc) hR (fun r hr => ?_) (fun r hr => ?_) hcov'
    · rw [hw] at hr
      have hy : r ≠ Assumptions.emuReg asg .y := fun he => hr (List.mem_map.mpr
        ⟨.y, by simp [Assumptions.emuWrites], he.symm⟩)
      simp only [ht']
      rw [Function.update_of_ne hy]
      exact foldl_update_other (f := Assumptions.emuReg asg) (v := fun _ => none) _
        (fun s hs he => hr (List.mem_map.mpr ⟨s, hs, he⟩))
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
      subst hr
      simp [ht']

/-! ### Reading score words -/

theorem readEReal_sw {v : Value} (h : ScoreWord v) : readEReal .f32 v = some (.ok (eOf v)) := by
  have := readEReal_erealValue h.ne_top
  rwa [h.eval] at this

theorem cmaxW_lt_top {w : Nat → Value} (h : ∀ k < 64, ScoreWord (w k)) (m : Nat) :
    cmaxW w m < ⊤ := by
  unfold cmaxW
  refine Finset.sup_induction (p := fun x => x < ⊤) bot_lt_top (fun a ha b hb => ?_) ?_
  · exact max_lt ha hb
  · intro k hk
    exact lt_top_iff_ne_top.mpr (h k (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)).ne_top

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
