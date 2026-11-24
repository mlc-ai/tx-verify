-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.MemoryWindows
public import Kernels.FlashKdaFwd.Algorithm
public import Lemmas.Flow.Step.RuleStep
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Activation
open PTX PTX.Assumption PTX.Flow

def multiplier : ℚ := -12102203 / 8388608

noncomputable def strength (x : ℝ) := 1 / ((2 : ℝ) ^ (x * (multiplier : ℝ)) + 1)

noncomputable def arithmetic : Assumption := idealReal "flash-kda-arithmetic"
  { float := [.mul .f32, .add .f32, .subRn .f32, .fma .f32]
    warpMma := [⟨.float .bf16, .float .bf16, .float .f32, .float .f32, none⟩] }
  "Scalar arithmetic and the products accumulated by the tensor cores use real numbers."

noncomputable def approximate : Assumption :=
  approxExact "flash-kda-functions" [.ex2 .f32, .rcp .f32]
    "The base-two exponential and reciprocal use their exact real values."

def scalar (op : FOp) (mode : FMode) (d : Nat) (xs : List Opnd) : Instr :=
  ⟨none, .float {op, mode, ty := ⟨.f32, 1⟩, ftz := true, dsts := [some d], srcs := xs}⟩

def code (src product power sum dst : Nat) : List Instr := [
  scalar .mul .ieee product [.reg src, .f32imm 0xBFB8AA3B],
  scalar .ex2 .approx power [.reg product],
  scalar .add .ieee sum [.reg power, .f32imm 0x3F800000],
  scalar .rcp .approx dst [.reg sum]]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 60000 in
theorem sites : Transfers.slice 2316 4 = some (code 1950 1564 1563 1951 1952) ∧
    Transfers.slice 2322 4 = some (code 1954 1566 1565 1955 1956) := ⟨rfl,rfl⟩

noncomputable section

private theorem multiplier_read (t : TState) :
    readERealOpnd t .f32 (.f32imm 0xBFB8AA3B) = some (.ok ((multiplier : ℝ) : EReal)) :=
  readEReal_bits32 0xBFB8AA3B multiplier rfl (by decide) (by decide +kernel)

private theorem one_read (t : TState) :
    readERealOpnd t .f32 (.f32imm 0x3F800000) = some (.ok ((1 : ℝ) : EReal)) := by
  rw [readERealOpnd_f32imm]
  simpa using (readEReal_bits32 0x3F800000 1 rfl (by decide) (by decide +kernel))

def put (t : TState) (d : Nat) (x : ℝ) := PTX.next (setReg t d (.float .f32 x))

private theorem read_put (t : TState) (d : Nat) (x : ℝ) :
    readERealOpnd (put t d x) .f32 (.reg d) = some (.ok (x : EReal)) := by
  rw [readERealOpnd_reg (v := .float .f32 x) (by simp [put, PTX.next, setReg])]
  exact readEReal_float_self _ _

private theorem product_step (L : Launch) (g : Nat) (t : TState) (src d : Nat) (x : ℝ)
    (h : readERealOpnd t .f32 (.reg src) = some (.ok (x : EReal))) :
    execLocalA [arithmetic, approximate] L g t
        (scalar .mul .ieee d [.reg src, .f32imm 0xBFB8AA3B]).op =
      .ok (put t d (x * (multiplier : ℝ))) := by
  change execLocalRule _ _ _ _ _ = _
  apply execLocalRule_cons_some
  change execIdealFloat L g t (scalar .mul .ieee d [.reg src, .f32imm 0xBFB8AA3B]).op = _
  simp only [scalar, execIdealFloat, h, multiplier_read, bindRead_some_ok, mulEReal_coe,
    Option.map_some, erealValue_coe]
  rfl

private theorem plus_step (L : Launch) (g : Nat) (t : TState) (src d : Nat) (x : ℝ)
    (h : readERealOpnd t .f32 (.reg src) = some (.ok (x : EReal))) :
    execLocalA [arithmetic, approximate] L g t
        (scalar .add .ieee d [.reg src, .f32imm 0x3F800000]).op = .ok (put t d (x+1)) := by
  change execLocalRule _ _ _ _ _ = _
  apply execLocalRule_cons_some
  change execIdealFloat L g t (scalar .add .ieee d [.reg src, .f32imm 0x3F800000]).op = _
  simp only [scalar, execIdealFloat, h, one_read, bindRead_some_ok, addEReal_coe,
    Option.map_some, erealValue_coe]
  rfl

private theorem exp_step (L : Launch) (g : Nat) (t : TState) (src d : Nat) (x : ℝ)
    (h : readERealOpnd t .f32 (.reg src) = some (.ok (x : EReal))) :
    execLocalA [arithmetic, approximate] L g t
      (scalar .ex2 .approx d [.reg src]).op = .ok (put t d ((2:ℝ)^x)) := by
  change execLocalRule _ _ _ _ _ = _
  apply execLocalRule_cons_none (by rfl)
  apply execLocalRule_cons_some
  change execApproxExact t (scalar .ex2 .approx d [.reg src]).op = _
  simp [scalar, execApproxExact, readFinite, h, bindRead, put, pure, Except.pure]

private theorem reciprocal_step (L : Launch) (g : Nat) (t : TState) (src d : Nat) (x : ℝ)
    (h : readERealOpnd t .f32 (.reg src) = some (.ok (x : EReal))) (hx : x ≠ 0) :
    execLocalA [arithmetic, approximate] L g t
      (scalar .rcp .approx d [.reg src]).op = .ok (put t d (1/x)) := by
  change execLocalRule _ _ _ _ _ = _
  apply execLocalRule_cons_none (by rfl)
  apply execLocalRule_cons_some
  change execApproxExact t (scalar .rcp .approx d [.reg src]).op = _
  simp [scalar, execApproxExact, readFinite, h, hx, bindRead, put, pure, Except.pure]

theorem evaluate (L : Launch) (g : Nat) (t : TState) (src product power sum dst : Nat) (x : ℝ)
    (h : readERealOpnd t .f32 (.reg src) = some (.ok (x : EReal))) :
    let a := put t product (x * (multiplier : ℝ))
    let b := put a power ((2:ℝ)^(x * (multiplier : ℝ)))
    let c := put b sum ((2:ℝ)^(x * (multiplier : ℝ)) + 1)
    (code src product power sum dst).foldlM (m := Exec)
      (fun s ins => execLocalA [arithmetic, approximate] L g s ins.op) t =
      .ok (put c dst (strength x)) := by
  dsimp only
  have hp : (2:ℝ) ^ (x * (multiplier : ℝ)) + 1 ≠ 0 := by positivity
  simp only [code, List.foldlM_cons, product_step _ _ _ _ _ _ h, bind, Except.bind,
    exp_step _ _ _ _ _ _ (read_put ..), plus_step _ _ _ _ _ _ (read_put ..),
    reciprocal_step _ _ _ _ _ _ (read_put ..) hp, List.foldlM_nil]
  rfl

theorem differs_at_one : strength 1 < Algorithm.sigmoid 1 := by
  have h : -1 < Real.log 2 * (multiplier : ℝ) := by
    norm_num [multiplier] at *
    linarith [Real.log_two_lt_d9]
  unfold strength Algorithm.sigmoid
  rw [one_mul, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  apply one_div_lt_one_div_of_lt (by positivity)
  linarith [Real.exp_lt_exp.mpr h]

end
end FlashKda.Packed.Activation
