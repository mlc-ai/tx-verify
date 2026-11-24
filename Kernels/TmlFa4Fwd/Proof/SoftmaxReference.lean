-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreNumeric
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSignals
public import Kernels.TmlFa4Fwd.Flow.Code.Part088
public import Lemmas.Flow.SetpCore

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- The maximum, its finiteness predicate, and the effective finite reference. -/
structure ReferenceSite where
  pc : Nat
  maximum : Nat
  pred : Nat
  finite : Nat

def referenceSite (round : Round) : ReferenceSite :=
  match round with
  | .first => ⟨4395, 7256, 622, 3685⟩
  | .biased => ⟨5666, 4560, 635, 4561⟩
  | .unbiased => ⟨6877, 5509, 645, 5510⟩

def ReferenceSite.compareOp (s : ReferenceSite) : Op :=
  .float {setpI (.unord .ne) false with
    dsts := [some s.pred], srcs := [.reg s.maximum, .f32imm 0xFF800000]}

def ReferenceSite.selectInstr (s : ReferenceSite) : IntInstr :=
  ⟨.selp, .float .f32, false, [some s.finite], [.reg s.maximum, .f32imm 0, .reg s.pred]⟩

private theorem referenceCode (round : Round) :
    let s := referenceSite round
    kernel.code[s.pc]? = some ⟨none, s.compareOp⟩ ∧
      kernel.code[s.pc + 1]? = some ⟨none, .int s.selectInstr⟩ := by
  cases round
  · exact ⟨Flow.code_4395, Flow.code_4396⟩
  · exact ⟨Flow.code_5666, Flow.code_5667⟩
  · exact ⟨Flow.code_6877, Flow.code_6878⟩

private theorem referenceSegFree (round : Round) :
    (referenceSite round).pc ∉ Assumptions.swExp2Sites ∧
      (referenceSite round).pc + 1 ∉ Assumptions.swExp2Sites := by
  cases round <;> decide +kernel

def finiteRefValue : Option ℝ → Value
  | some x => .float .f32 x
  | none => .bits 32 0

theorem readFiniteRef (mx : Option ℝ) :
    readEReal .f32 (finiteRefValue mx) = some (.ok ((mx.getD 0 : ℝ) : EReal)) := by
  cases mx with
  | none =>
    have h := classify_bits (fmt := .f32) (n := 0) (x := .zero false)
      (by decide) (by decide)
    change classify .f32 (.bits 32 0) = .ok (.zero false) at h
    change readEReal.ofDatum (classify .f32 (.bits 32 0)) = _
    rw [h]
    rfl
  | some x => rfl

/-- A fully masked row keeps negative infinity as its stored maximum and uses a zero shift
reference. Every finite maximum is used directly. The two states differ only in the two
registers specified by the instructions, and continue the original trace. -/
theorem finiteReferenceLocal {l : Launch} {g : Nat} {t : TState}
    (round : Round) (mx : Option ℝ) (ht : At t (referenceSite round).pc [])
    (hm : t.regs (referenceSite round).maximum = some (scoreValue mx)) :
    let s := referenceSite round
    ∃ u, At u (s.pc + 2) [(s.finite, finiteRefValue mx), (s.maximum, scoreValue mx)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      ∀ r, r ∉ [s.finite, s.pred] → u.regs r = t.regs r := by
  let s := referenceSite round
  let t₁ := next (setReg t s.pred (.pred mx.isSome))
  let u := next (setReg t₁ s.finite (finiteRefValue mx))
  have hFresh : s.maximum ≠ s.pred ∧ s.maximum ≠ s.finite := by
    cases round <;> decide
  have hInf : readERealOpnd t .f32 (.f32imm 0xFF800000) = some (.ok ⊥) := readScoreValue none
  have hCmp : erealCompare .ne (scoreReal mx) ⊥ = mx.isSome := by
    cases mx with
    | none => simp [scoreReal, erealCompare]
    | some x => simp [scoreReal, erealCompare, EReal.coe_ne_bot]
  have hAt₁ : At t₁ (s.pc + 1) [] :=
    ⟨by change t.pc + 1 = _; rw [ht.1], ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
  have h₀ : run kernel Assumptions.all l g 1 t = some t₁ := by
    apply run_local (referenceCode round).1 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric]
    have hModel : IdealAt Assumptions.numeric (.setpInf .f32) l g t :=
      idealAt_head (by decide)
        (Assumptions.numeric_segSites.pc (ht.1 ▸ (referenceSegFree round).1)).tail
    apply hModel _ rfl (.ok t₁)
    have hRead := (readERealOpnd_reg (fmt := .f32) hm).trans (readScoreValue mx)
    change bindRead (readERealOpnd t .f32 (.reg s.maximum)) (fun x =>
      bindRead (readERealOpnd t .f32 (.f32imm 0xFF800000)) (fun y =>
        some (.ok (next (setReg t s.pred (.pred (erealCompare .ne x y))))))) = _
    rw [hRead, hInf]
    simp only [bindRead, hCmp, t₁]
  have h₁ : run kernel Assumptions.all l g 1 t₁ = some u := by
    apply run_local (referenceCode round).2 rfl hAt₁
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (hAt₁.1 ▸ (referenceSegFree round).2) rfl]
    change execLocal l g t₁ (.int s.selectInstr) = _
    rw [execLocal_selp (i := s.selectInstr) rfl]
    have hPred : t₁.regs s.pred = some (.pred mx.isSome) := Function.update_self ..
    have hM : t₁.regs s.maximum = some (scoreValue mx) := by
      simpa only [t₁, next, setReg, Function.update_of_ne hFresh.1] using hm
    have hWidth : FloatFmt.f32.bytes = 4 := rfl
    cases mx <;> simp [ReferenceSite.selectInstr, execMove, readValue, readReg, hPred, hM,
      u, finiteRefValue, scoreValue, bind, Except.bind, pure, Except.pure, DType.width,
      Value.bytes, readBits, hWidth]
  refine ⟨u, ⟨?_, ht.2.1, ht.2.2.1, ht.2.2.2.1, ?_⟩,
    run_rtg (run_comp h₀ h₁), ?_⟩
  · change t₁.pc + 1 = _
    rw [hAt₁.1]
  · change Holds u.regs [(s.finite, finiteRefValue mx), (s.maximum, scoreValue mx)]
    have hMax : t.regs s.maximum = some (scoreValue mx) := hm
    simp [Holds, u, t₁, next, setReg, Function.update_of_ne hFresh.1,
      Function.update_of_ne hFresh.2, hMax]
  · intro r hn
    change r ∉ [s.finite, s.pred] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp [u, t₁, next, setReg, Function.update_of_ne hn.1, Function.update_of_ne hn.2]

/-- The local replay continues a fully recorded lane trace. -/
theorem finiteReferenceInPrefix {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {ending : Option TState}
    (round : Round) (mx : Option ℝ) (ht : At t (referenceSite round).pc [])
    (hm : t.regs (referenceSite round).maximum = some (scoreValue mx))
    (hr : Run kernel Assumptions.all l g t es ending) (hne : es ≠ []) :
    let s := referenceSite round
    ∃ u, At u (s.pc + 2) [(s.finite, finiteRefValue mx), (s.maximum, scoreValue mx)] ∧
      Run kernel Assumptions.all l g u es ending ∧
      ∀ r, r ∉ [s.finite, s.pred] → u.regs r = t.regs r := by
  obtain ⟨u,hU,hLocal,hFrame⟩ := finiteReferenceLocal round mx ht hm
  exact ⟨u,hU,hr.after_local_nonempty hLocal hne,hFrame⟩

/-- The local replay continues a fully recorded lane trace. -/
theorem finiteReferenceTrace {l : Launch} {g : Nat} {t : TState} {es : List Event}
    (round : Round) (mx : Option ℝ) (ht : At t (referenceSite round).pc [])
    (hm : t.regs (referenceSite round).maximum = some (scoreValue mx))
    (hr : Run kernel Assumptions.all l g t es none) :
    let s := referenceSite round
    ∃ u, At u (s.pc + 2) [(s.finite, finiteRefValue mx), (s.maximum, scoreValue mx)] ∧
      Run kernel Assumptions.all l g u es none ∧
      ∀ r, r ∉ [s.finite, s.pred] → u.regs r = t.regs r := by
  obtain ⟨u,hU,hLocal,hFrame⟩ := finiteReferenceLocal round mx ht hm
  exact ⟨u,hU,hr.after_local hLocal,hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
