-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxExponent
public import Kernels.TmlFa4Fwd.Proof.SoftmaxConvert
public import Kernels.TmlFa4Fwd.Flow.Code.Part072
public import Lemmas.Flow.ContinuingEvent
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- The first round uses four 32-word hardware-exponent runs, one before each packed P group. -/
def firstHardwarePc (quarter : Fin 4) : Nat := 4594 + 56 * quarter.val

def firstHardwareInput (quarter : Fin 4) : Nat := 3687 + 32 * quarter.val

def firstHardwareOutput (quarter : Fin 4) : Nat := 1231 + 32 * quarter.val

private def hardwareWordOp (quarter : Fin 4) (word : Nat) : Op :=
  .float {ex2I true with
    dsts := [some (firstHardwareOutput quarter + word)]
    srcs := [.reg (firstHardwareInput quarter + word)]}

private def hardwareWordCheck (quarter : Fin 4) (word : Nat) : Bool :=
  match kernel.code[firstHardwarePc quarter + word]? with
  | some ⟨none, .float ⟨.ex2, ⟨.f32, 1⟩, [], none, none, .approx, true, false, false, false,
      false, false, false, [some d], [.reg s]⟩⟩ =>
    d == firstHardwareOutput quarter + word && s == firstHardwareInput quarter + word
  | _ => false

set_option maxRecDepth 100000 in
private theorem hardwareWordTable (quarter : Fin 4) :
    (List.range 32).all (hardwareWordCheck quarter) = true := by
  fin_cases quarter <;> kernel_rfl

private theorem hardwareWordCode (quarter : Fin 4) {j : Nat} (h : j < 32) :
    kernel.code[firstHardwarePc quarter + j]? = some ⟨none, hardwareWordOp quarter j⟩ := by
  have hh := List.all_eq_true.mp (hardwareWordTable quarter) j (List.mem_range.mpr h)
  unfold hardwareWordCheck at hh
  split at hh
  · rename_i d s hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    rw [hc, hh.1, hh.2]
    rfl
  · cases hh

private theorem hardwareOffSegments (quarter : Fin 4) {i : Nat} (hi : i < 32) :
    firstHardwarePc quarter + i ∉ Assumptions.swExp2Sites := by
  have hq := quarter.isLt
  simp only [firstHardwarePc, Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem firstHardwareInterval {l : Launch} {g : Nat} (quarter : Fin 4)
    (raw value : Nat → Value) (hEval : ∀ i < 32, ex2E true (raw i) = .ok (value i)) :
    ∀ (count offset : Nat) (t : TState), offset + count ≤ 32 →
      At t (firstHardwarePc quarter + offset) [] →
      (∀ i < 32, t.regs (firstHardwareInput quarter + i) = some (raw i)) →
      ∃ u, run kernel Assumptions.all l g count t = some u ∧
        At u (firstHardwarePc quarter + (offset + count)) [] ∧
        (∀ i, offset ≤ i → i < offset + count →
          u.regs (firstHardwareOutput quarter + i) = some (value i)) ∧
        ∀ r, r < firstHardwareOutput quarter + offset ∨
            firstHardwareOutput quarter + (offset + count) ≤ r → u.regs r = t.regs r := by
  intro count
  induction count with
  | zero =>
    intro offset t _ ht _
    exact ⟨t, rfl, by simpa only [Nat.add_zero] using ht,
      fun _ hlo hhi => (by omega : False).elim, fun _ _ => rfl⟩
  | succ count ih =>
    intro offset t hBound ht hRaw
    have hOffset : offset < 32 := by omega
    let dst := firstHardwareOutput quarter + offset
    let s := next (setReg t dst (value offset))
    have hOne : run kernel Assumptions.all l g 1 t = some s :=
      hardwareExponentRun ht (hardwareOffSegments quarter hOffset)
        (hardwareWordCode quarter hOffset) (hRaw offset hOffset) (hEval offset hOffset)
    have hState : At s (firstHardwarePc quarter + (offset + 1)) [] := by
      have hs := ht.set (r := dst) (v := value offset) (by simp)
      simpa only [Nat.add_assoc] using hs.mono (G := []) trivial
    have hArgs (i : Nat) (hi : i < 32) :
        s.regs (firstHardwareInput quarter + i) = some (raw i) := by
      have hne : firstHardwareInput quarter + i ≠ dst := by
        unfold dst firstHardwareInput firstHardwareOutput
        omega
      simpa only [s, next, setReg, Function.update_of_ne hne] using hRaw i hi
    obtain ⟨u, hu, hU, hVals, hKeep⟩ := ih (offset + 1) s (by omega) hState hArgs
    have hlen : offset + 1 + count = offset + (count + 1) := by omega
    refine ⟨u, by simpa only [Nat.add_comm 1 count] using run_comp hOne hu,
      by simpa only [hlen] using hU, ?_, ?_⟩
    · intro i hlo hhi
      by_cases h : i = offset
      · subst i
        have hDst : s.regs dst = some (value offset) := Function.update_self ..
        exact (hKeep dst (.inl (by unfold dst; omega))).trans hDst
      · exact hVals i (by omega) (by omega)
    · intro r hr
      have hR : r ≠ dst := by unfold dst; rcases hr with h | h <;> omega
      exact (hKeep r (by rcases hr with h | h; exact .inl (by omega); exact .inr (by omega))).trans
        (by simp only [s, next, setReg, Function.update_of_ne hR])

/-- All 32 shifted scores in a first-round quarter are exponentiated at their decoded
instructions. The next instruction is the quarter's first probability pack. -/
theorem firstHardwareBlockRun {l : Launch} {g : Nat} (quarter : Fin 4) {t : TState}
    {F : List (Nat × Value)} (raw value : Nat → Value)
    (ht : At t (firstHardwarePc quarter) F)
    (hRaw : ∀ i < 32, t.regs (firstHardwareInput quarter + i) = some (raw i))
    (hEval : ∀ i < 32, ex2E true (raw i) = .ok (value i)) :
    ∃ u, run kernel Assumptions.all l g 32 t = some u ∧
      At u (firstHardwarePc quarter + 32) [] ∧
      (∀ i < 32, u.regs (firstHardwareOutput quarter + i) = some (value i)) ∧
      ∀ r, r < firstHardwareOutput quarter ∨ firstHardwareOutput quarter + 32 ≤ r →
        u.regs r = t.regs r := by
  obtain ⟨u, hRun, hU, hVals, hKeep⟩ := firstHardwareInterval
    (l := l) (g := g) quarter raw value hEval 32 0 t (by decide)
    (by simpa only [Nat.add_zero] using ht.mono (G := []) trivial) hRaw
  exact ⟨u, hRun, hU, fun i hi => hVals i (Nat.zero_le _) hi,
    fun r hr => hKeep r (by simpa only [Nat.add_zero, Nat.zero_add] using hr)⟩

/-- The first exponent block immediately feeds the first actual BF16x2 conversion.
The first converted word names score lanes 2 and 3 in low-to-high order. -/
theorem firstExponentPack {l : Launch} {g i : Nat} {t : TState} {F : List (Nat × Value)}
    {X : Execution} (raw : Nat → Value) (exponents : Nat → ℝ)
    (ht : At t 4594 F) (hRaw : ∀ j < 32, t.regs (3687 + j) = some (raw j))
    (hEval : ∀ j < 32, ex2E true (raw j) = .ok (.float .f32 (exponents j)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ u, At u 4627 [(3815, .pair (.float .bf16 (exponents 2)) (.float .bf16 (exponents 3)))] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop i) none := by
  obtain ⟨v, hv, hV, hRegs, _⟩ :=
    firstHardwareBlockRun (l := l) (g := g) 0 raw (fun j => .float .f32 (exponents j))
      ht hRaw hEval
  have hRead {r : Nat} {x : ℝ} (hr : v.regs r = some (.float .f32 x)) :
      readFinite v .f32 (.reg r) = some (.ok x) := by
    simp [readFinite, readERealOpnd_reg hr, readEReal, bindRead, pure, Except.pure,
      EReal.coe_ne_top, EReal.coe_ne_bot]
  have hPack := probabilityConvertRun (l := l) (g := g) (pc := 4626) (dst := 3815)
    (a := 1234) (b := 1233) hV Flow.code_4626 (by decide)
    (hRead (hRegs 3 (by decide))) (hRead (hRegs 2 (by decide)))
  exact ⟨_, hV.set (by simp), hRun.after_local (run_rtg (run_comp hv hPack))⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
