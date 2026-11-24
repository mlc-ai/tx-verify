-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Flow.MemTmpl
public import Kernels.TmlFa4Fwd.Flow.Code.Part103
public import Kernels.TmlFa4Fwd.Flow.Code.Part118

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The two repeated score loops share the increment-and-test tail. -/
inductive ScoreLoop
  | biased
  | plain
  deriving DecidableEq

structure ScoreLoopSite where
  head : Nat
  increment : Nat
  word : Nat
  pred : Nat
  sentinel : Nat

def scoreLoopSite : ScoreLoop → ScoreLoopSite
  | .biased => ⟨5032, 6650, 7248, 642, 2 ^ 32 - 1⟩
  | .plain => ⟨6661, 7601, 7254, 651, 0⟩

/-- Positive modular distance to the next exit test, including a full turn from the sentinel. -/
def scoreLoopDistance (loop : ScoreLoop) (w : Nat) : Nat :=
  let sent := (scoreLoopSite loop).sentinel
  if w < sent then sent - w else 2 ^ 32 - w + sent

theorem scoreLoopDistance_pos (loop : ScoreLoop) {w : Nat} (hw : w < 2 ^ 32) :
    0 < scoreLoopDistance loop w ∧ scoreLoopDistance loop w ≤ 2 ^ 32 := by
  cases loop with
  | biased =>
    change 0 < (if w < 4294967295 then 4294967295 - w else 4294967296 - w + 4294967295) ∧
      (if w < 4294967295 then 4294967295 - w else 4294967296 - w + 4294967295) ≤ 4294967296
    by_cases h : w < 4294967295
    · rw [ite_eq_left h]
      omega
    · rw [ite_eq_right h]
      omega
  | plain =>
    simp only [scoreLoopDistance, scoreLoopSite, Nat.not_lt_zero, ite_false, Nat.add_zero]
    omega

theorem scoreLoopDistance_step (loop : ScoreLoop) {w : Nat} (hw : w < 2 ^ 32)
    (hn : (w + 1) % 2 ^ 32 ≠ (scoreLoopSite loop).sentinel) :
    scoreLoopDistance loop ((w + 1) % 2 ^ 32) + 1 = scoreLoopDistance loop w := by
  by_cases hWrap : w + 1 < 2 ^ 32
  · rw [Nat.mod_eq_of_lt hWrap] at hn ⊢
    cases loop with
    | biased =>
      change w + 1 ≠ 4294967295 at hn
      change (if w + 1 < 4294967295 then 4294967295 - (w + 1)
        else 4294967296 - (w + 1) + 4294967295) + 1 =
        if w < 4294967295 then 4294967295 - w else 4294967296 - w + 4294967295
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      omega
    | plain =>
      simp only [scoreLoopDistance, scoreLoopSite, Nat.not_lt_zero, ite_false, Nat.add_zero]
      omega
  · have hWrapEq : w + 1 = 2 ^ 32 := by omega
    rw [hWrapEq, Nat.mod_self] at hn ⊢
    cases loop with
    | biased =>
      have h : w = 4294967295 := by omega
      subst w
      decide
    | plain => exact (hn rfl).elim

private theorem scoreIncrementBits {w : Nat} (hw : w < 2 ^ 32) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 w) + truncBits 32 1#64) =
      BitVec.ofNat 64 ((w + 1) % 2 ^ 32) := by
  rw [truncBits_ofNat hw (by decide), show truncBits 32 1#64 = 1#64 from rfl,
    ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show w + 1 < 2 ^ 64 by omega)]

private theorem wordRun {l : Launch} {g : Nat} {s u : TState} {i : Instr}
    (hf : s.fault = none) (hc : kernel.code[s.pc]? = some i) (hgd : i.guard = none)
    (hOff : s.pc ∉ Assumptions.swExp2Sites) (hCore : Assumptions.coreOp i.op = true)
    (hl : i.op.isLocal = true) (he : execLocal l g s i.op = .ok u) :
    run kernel Assumptions.all l g 1 s = some u := by
  have hx : execLocalA Assumptions.all l g s i.op = .ok u := by
    rwa [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff hCore,
      execLocalA_nil]
  simp only [run, tauStep, out_tau hf hc (by rw [hgd]; rfl) hl hx]
  rfl

/-- A completed score-window traversal performs its actual increment and sentinel test,
regardless of sub-step metadata left by any earlier instruction. -/
theorem scoreLoopTestActualFrame (loop : ScoreLoop) {l : Launch} {g w : Nat} {s : TState}
    (hw : w < 2 ^ 32) (hF : s.fault = none)
    (hP : s.pc = (scoreLoopSite loop).increment)
    (hR : s.regs (scoreLoopSite loop).word = some (b32 w)) :
    let site := scoreLoopSite loop
    let w' := (w + 1) % 2 ^ 32
    ∃ u, run kernel Assumptions.all l g 2 s = some u ∧ u.pc = site.increment + 2 ∧
      u.sub = s.sub ∧ u.fault = none ∧ u.regs site.word = some (b32 w') ∧
      u.regs site.pred = some (.pred (decide (w' ≠ site.sentinel))) ∧
      ∀ r, r ≠ site.word → r ≠ site.pred → u.regs r = s.regs r := by
  dsimp only
  let site := scoreLoopSite loop
  let w' := (w + 1) % 2 ^ 32
  let t := next (setReg s site.word (b32 w'))
  let u := next (setReg t site.pred (.pred (decide (w' ≠ site.sentinel))))
  have hT : t.regs site.word = some (b32 w') := Function.update_self _ _ _
  have hTp : t.pc = site.increment + 1 := by simpa only [t, next, setReg] using congrArg (· + 1) hP
  have hTf : t.fault = none := hF
  have hStep : run kernel Assumptions.all l g 1 s = some t := by
    cases loop <;> simp only [scoreLoopSite] at hP hR
    · refine wordRun hF (hP.symm ▸ Flow.code_6650) rfl (by rw [hP]; decide) rfl rfl ?_
      rw [execLocal_int rfl]
      simp only [execInt, DType.width, readBits, readValue, readReg, hR, bind, Except.bind,
        pure, Except.pure]
      exact congrArg (fun b => Except.ok (next (setReg s 7248 (.bits 32 b))))
        (scoreIncrementBits hw)
    · refine wordRun hF (hP.symm ▸ Flow.code_7601) rfl (by rw [hP]; decide) rfl rfl ?_
      rw [execLocal_int rfl]
      simp only [execInt, DType.width, readBits, readValue, readReg, hR, bind, Except.bind,
        pure, Except.pure]
      exact congrArg (fun b => Except.ok (next (setReg s 7254 (.bits 32 b))))
        (scoreIncrementBits hw)
  have hTest : run kernel Assumptions.all l g 1 t = some u := by
    have hNext := Nat.mod_lt (w + 1) (show 0 < 2 ^ 32 by decide)
    have h64 : (w + 1) % 2 ^ 32 < 2 ^ 64 := hNext.trans (by decide)
    cases loop <;> simp only [site, scoreLoopSite] at hTp hT
    · refine wordRun hTf (by rw [hTp]; exact Flow.code_6651) rfl (by rw [hTp]; decide) rfl rfl ?_
      rw [execLocal_int rfl]
      simp only [execInt, DType.width, readBits, readReg, hT, bind, Except.bind,
        pure, Except.pure, compare, DType.kind?, Option.getD_some, b32, w',
        truncBits_ofNat hNext (by decide), toNat_ofNat_lt h64, ne_eq, Int.natCast_inj]
      rfl
    · refine wordRun hTf (by rw [hTp]; exact Flow.code_7602) rfl (by rw [hTp]; decide) rfl rfl ?_
      rw [execLocal_int rfl]
      simp only [execInt, DType.width, readBits, readReg, hT, bind, Except.bind,
        pure, Except.pure, compare, DType.kind?, Option.getD_some, b32, w',
        truncBits_ofNat hNext (by decide), toNat_ofNat_lt h64, ne_eq, Int.natCast_inj]
      rfl
  have hNe : site.word ≠ site.pred := by cases loop <;> decide
  have hUp : u.pc = site.increment + 2 := by
    simp only [u, next, setReg, hTp, Nat.add_assoc]
  exact ⟨u, run_comp hStep hTest, hUp, rfl, hF,
    (Function.update_of_ne hNe _ _).trans hT, Function.update_self _ _ _,
    fun r hWord hPred => (Function.update_of_ne hPred _ _).trans
      (Function.update_of_ne hWord _ _)⟩

theorem scoreLoopTestActual (loop : ScoreLoop) {l : Launch} {g w : Nat} {s : TState}
    (hw : w < 2 ^ 32) (hF : s.fault = none)
    (hP : s.pc = (scoreLoopSite loop).increment)
    (hR : s.regs (scoreLoopSite loop).word = some (b32 w)) :
    let site := scoreLoopSite loop
    let w' := (w + 1) % 2 ^ 32
    ∃ u, run kernel Assumptions.all l g 2 s = some u ∧ u.pc = site.increment + 2 ∧
      u.sub = s.sub ∧ u.fault = none ∧ u.regs site.word = some (b32 w') ∧
      u.regs site.pred = some (.pred (decide (w' ≠ site.sentinel))) := by
  obtain ⟨u, hRun, hPc, hSub, hHealthy, hWord, hPred, _⟩ :=
    scoreLoopTestActualFrame (l := l) (g := g) loop hw hF hP hR
  exact ⟨u, hRun, hPc, hSub, hHealthy, hWord, hPred⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
