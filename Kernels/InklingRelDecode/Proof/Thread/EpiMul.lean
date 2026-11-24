-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiAsms

@[expose] public section

/-! # The packed multiplications of the epilogue

The epilogue multiplies each packed pair of loaded words by the pair `c` of the reciprocal with
`mul.f32x2 d, c, w`: no rounding modifier (the decoded `rnd` is `none`) and the pair `c` first.
`Lemmas/Flow/MulPairCore.lean` states the outcome and the run of such multiplications for
`mul.rn.f32x2 d, w, c`; this file restates them for the instruction the kernel has
(`mulI`, `mulCodeC`, `mulsC_run`). A run of multiplications writes each destination with the
outcome `mulOut c w` when no step faults; otherwise the thread is dead. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

theorem execLocal_mulI_core {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (.float { mulI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (coreFloat mulI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { mulI with dsts := [some d], srcs := [.reg a, .reg b] } =
      FloatInstr.lane mulI := rfl
  have h2 : List.range 2 = [0, 1] := rfl
  cases hxa : classify .f32 (splitValue 64 va).1 with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 (splitValue 64 vb).1 with
  | error e => core_float_reg
  | ok xb =>
  cases hl0 : FloatInstr.lane mulI [xa, xb] with
  | none => core_float_reg
  | some o =>
  cases hya : classify .f32 (splitValue 64 va).2 with
  | error e => core_float_reg
  | ok ya =>
  cases hyb : classify .f32 (splitValue 64 vb).2 with
  | error e => core_float_reg
  | ok yb =>
  cases hl1 : FloatInstr.lane mulI [ya, yb] with
  | none => core_float_reg
  | some o' => cases o <;> cases o' <;> core_float_reg

theorem exec_floatE_mulI_at {t : TState} (hA : IdealAt asms .mulF32x2 L g t)
    (hD : DeclineAt asms .mulF32x2 L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA asms L g t (.float { mulI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (floatE mulI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { mulI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      some .mulF32x2 := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t (.float { mulI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (idealVal mulI [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, readERealPair_reg_val (L := L) (g := g) ha,
      readERealPair_reg_val (L := L) (g := g) hb, bindRead_map]
    rcases pairRead va with _ | (e | ⟨x0, x1⟩)
    · rfl
    · rfl
    rcases pairRead vb with _ | (e | ⟨y0, y1⟩)
    · rfl
    · rfl
    simp only [bindRead]
    rcases mulEReal x0 y0 with _ | r0 <;> rcases mulEReal x1 y1 with _ | r1 <;> rfl
  unfold floatE
  cases hv : idealVal mulI [va, vb] with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_mulI_core ha hb]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-- Every product is a pair of four-byte values. -/
theorem floatE_mulI_pair4 (vs : List Value) : Pair4 (floatE mulI vs) := by
  intro v hv
  unfold floatE at hv
  split at hv
  · rename_i r hr
    subst hv
    rcases vs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [idealVal, throw, throwThe,
      MonadExceptOf.throw] at hr
    obtain ⟨⟨x0, x1⟩, -, hr⟩ := bindRead_ok hr
    obtain ⟨⟨y0, y1⟩, -, hr⟩ := bindRead_ok hr
    simp only at hr
    split at hr
    · simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
      exact ⟨_, _, hr.symm, erealValue_f32_bytes _, erealValue_f32_bytes _⟩
    · cases hr
  · exact coreFloat_pair4 rfl vs v hv

theorem mulOut_pair (c w : Value) :
    ∃ x y, mulOut c w = .pair x y ∧ x.bytes = 4 ∧ y.bytes = 4 :=
  okVal_pair (floatE_mulI_pair4 _)

/-! ### A run of multiplications by the pair `c` -/

/-- The multiplications `(d, s)` (`mul.f32x2 d, c, s`) from `pc` on. -/
def MulCodeC (K : Kernel) (c : Nat) : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | pc, m :: ms =>
    K.code[pc]? = some ⟨none, .float { mulI with dsts := [some m.1], srcs := [.reg c, .reg m.2] }⟩ ∧
      MulCodeC K c (pc + 1) ms

/-- `MulCodeC` decided on the code. -/
def mulCodeCB (K : Kernel) (c : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | pc, m :: ms =>
    (match K.code[pc]? with
      | some ⟨none, .float f⟩ =>
        f == { mulI with dsts := [some m.1], srcs := [.reg c, .reg m.2] }
      | _ => false) && mulCodeCB K c (pc + 1) ms

theorem MulCodeC.of_bool {K : Kernel} {c : Nat} :
    ∀ {pc : Nat} {ms : List (Nat × Nat)}, mulCodeCB K c pc ms = true → MulCodeC K c pc ms
  | _, [], _ => trivial
  | pc, m :: ms, h => by
    simp only [mulCodeCB, Bool.and_eq_true] at h
    refine ⟨?_, MulCodeC.of_bool h.2⟩
    have h1 := h.1
    split at h1
    · rename_i f hc
      rw [hc, beq_iff_eq.mp h1]
    · cases h1

/-- The state after the multiplications, from source values `v` and the pair `vc`. -/
def mulRunC (v : Nat → Value) (vc : Value) : TState → List (Nat × Nat) → TState
  | t, [] => t
  | t, m :: ms => mulRunC v vc (PTX.next (setReg t m.1 (mulOut vc (v m.2)))) ms

theorem mulRunC_skel (v : Nat → Value) (vc : Value) :
    ∀ (ms : List (Nat × Nat)) (t : TState),
    (mulRunC v vc t ms).pc = t.pc + ms.length ∧ (mulRunC v vc t ms).sub = t.sub ∧
      (mulRunC v vc t ms).acc = t.acc ∧ (mulRunC v vc t ms).fault = t.fault
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | m :: ms, t => by
    obtain ⟨h1, h2, h3, h4⟩ := mulRunC_skel v vc ms
      (PTX.next (setReg t m.1 (mulOut vc (v m.2))))
    refine ⟨?_, h2, h3, h4⟩
    rw [mulRunC, h1]
    simp only [PTX.next, setReg, List.length_cons]
    omega

theorem mulRunC_other (v : Nat → Value) (vc : Value) {r : Nat} :
    ∀ (ms : List (Nat × Nat)) (t : TState), (∀ m ∈ ms, m.1 ≠ r) →
      (mulRunC v vc t ms).regs r = t.regs r
  | [], _, _ => rfl
  | m :: ms, t, h => by
    rw [mulRunC, mulRunC_other v vc ms _ (fun q hq => h q (by simp [hq]))]
    simp [PTX.next, setReg, Function.update_of_ne (h m (by simp)).symm]

theorem mulRunC_val (v : Nat → Value) (vc : Value) {d s : Nat} :
    ∀ (ms : List (Nat × Nat)) (t : TState), (ms.map Prod.fst).Nodup → (d, s) ∈ ms →
      (mulRunC v vc t ms).regs d = some (mulOut vc (v s))
  | [], _, _, hm => by simp at hm
  | m :: ms, t, hnd, hm => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [mulRunC, mulRunC_other v vc ms _ (fun q hq he => hnd.1 ⟨q, hq, he⟩)]
      simp [PTX.next, setReg]
    · exact mulRunC_val v vc ms _ hnd.2 hm

/-- **A run of multiplications by `c`**: each writes its outcome when no step faults;
otherwise the thread is dead. -/
theorem mulsC_run (v : Nat → Value) {c : Nat} {vc : Value} :
    ∀ (ms : List (Nat × Nat)) (t : TState), MulCodeC kernel c t.pc ms →
    t.fault = none → t.regs c = some vc → (∀ m ∈ ms, t.regs m.2 = some (v m.2)) →
    (∀ m ∈ ms, m.1 ≠ c ∧ ∀ m' ∈ ms, m.1 ≠ m'.2) →
    (∀ i < ms.length, ∀ s : TState, s.pc = t.pc + i →
      IdealAt asms .mulF32x2 L g s ∧ DeclineAt asms .mulF32x2 L g s) →
    (mulsOkC v vc ms = true → run kernel asms L g ms.length t = some (mulRunC v vc t ms)) ∧
    (mulsOkC v vc ms = false → Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t)
  | [], t, _, _, _, _, _, _ => ⟨fun _ => rfl, fun h => by simp [mulsOkC] at h⟩
  | m :: ms, t, hc, hf, hcv, hv, hfr, hI => by
    obtain ⟨hA, hD⟩ := hI 0 (by simp) t (by simp)
    have hex := exec_floatE_mulI_at (L := L) (g := g) (d := m.1) hA hD hcv (hv m (by simp))
    set t1 := PTX.next (setReg t m.1 (mulOut vc (v m.2)))
    have hm := hfr m (by simp)
    have hcv1 : t1.regs c = some vc := by
      simp [t1, PTX.next, setReg, Function.update_of_ne hm.1.symm, hcv]
    have hreg : ∀ q ∈ ms, t1.regs q.2 = some (v q.2) := by
      intro q hq
      simp only [t1, PTX.next, setReg, Function.update_of_ne (hm.2 q (by simp [hq])).symm]
      exact hv q (by simp [hq])
    have ih := mulsC_run v ms t1 hc.2 hf hcv1 hreg
      (fun q hq => ⟨(hfr q (by simp [hq])).1,
        fun q' hq' => (hfr q (by simp [hq])).2 q' (by simp [hq'])⟩)
      (fun i hi s hs' => hI (i + 1) (by simp; omega) s
        (by rw [hs']; simp [t1, PTX.next, setReg]; omega))
    rcases hE : floatE mulI [vc, v m.2] with e | x
    · rw [hE] at hex
      refine ⟨fun h => by simp [mulsOkC, hE, Except.toBool] at h, fun _ => ?_⟩
      exact dead_of_error hc.1 rfl hf hex
    · rw [hE] at hex
      have hx : mulOut vc (v m.2) = x := by simp [mulOut, hE, okVal]
      have o1 : out kernel asms L g t = .tau t1 := by
        rw [tau_of_ok hc.1 rfl hf hex]; simp only [t1, hx]
      have he : mulsOkC v vc (m :: ms) = mulsOkC v vc ms := by
        simp [mulsOkC, hE, Except.toBool]
      refine ⟨fun h => ?_, fun h => Machine.dead_of_tau o1 (ih.2 (he ▸ h))⟩
      simp only [List.length_cons, run, tauStep, o1, Option.bind_some, mulRunC]
      exact ih.1 (he ▸ h)

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
