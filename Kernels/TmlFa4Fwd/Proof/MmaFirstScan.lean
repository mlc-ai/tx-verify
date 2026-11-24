-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFirstTiles
public import Kernels.TmlFa4Fwd.Flow.Code.Part030

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def scanPc (stage : Fin 5) : Nat := 1960 + 4 * stage.val

def scanSrc : Fin 5 → Nat
  | 0 => 7196
  | 1 => 2465
  | 2 => 2468
  | 3 => 2471
  | 4 => 2474

def scanDst (stage : Fin 5) : Nat := 2463 + 3 * stage.val

def scanResult (stage : Fin 5) : Nat :=
  if stage.val = 4 then 7197 else 2465 + 3 * stage.val

private def scanWarpInstr (stage : Fin 5) : WarpInstr :=
  { kind := .shfl .up, ty := some (.int .b 32), dsts := [some (scanDst stage)],
    srcs := [.reg (scanSrc stage), .imm ((2 ^ stage.val : Nat) : Int), .imm 0],
    mask := some (.imm (-1)) }

private theorem scanWarpFields : ∀ stage : Fin 5,
    (kernel.code[scanPc stage]?).bind (fun i => match i.op with
      | .warp w => some (i.guard, w)
      | _ => none) = some (none, scanWarpInstr stage) := by decide +kernel

theorem scanCode (stage : Fin 5) :
    kernel.code[scanPc stage]? = some ⟨none, .warp
      { kind := .shfl .up
        ty := some (.int .b 32)
        dsts := [some (scanDst stage)]
        srcs := [.reg (scanSrc stage), .imm ((2 ^ stage.val : Nat) : Int), .imm 0]
        mask := some (.imm (-1)) }⟩ := by
  have h := scanWarpFields stage
  cases hc : kernel.code[scanPc stage]? with
  | none => simp [hc] at h
  | some i =>
    rcases i with ⟨guard, op⟩
    cases op <;> simp only [hc, Option.bind_some, reduceCtorEq] at h
    case warp w =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rfl

/-- Each of the first pass's five scan rounds shuffles the previous partial sum by the exact
doubling offset. -/
theorem scanTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (stage : Fin 5) (sum : Nat)
    (hpc : t.pc = scanPc stage) (hf : t.fault = none)
    (hv : t.regs (scanSrc stage) = some (b32 sum)) :
    out kernel Assumptions.all l g t = .ev (.shfl .up (b32 sum) (2 ^ stage.val) 0
      (fun value _ => next (setReg t (scanDst stage) value))) := by
  have hb : l.block % 32 = 0 := by rw [hp.block]
  have hc := scanCode stage
  rw [← hpc] at hc
  have hr : 1904 ≤ scanPc stage ∧ scanPc stage < 2768 := by fin_cases stage <;> decide
  rw [out_eq_core (by rw [hpc]; exact hr.1) (by rw [hpc]; exact hr.2), out_event hf hc rfl rfl]
  change Out.ev (shflTmpl l g t .up (scanDst stage) none (.reg (scanSrc stage))
    (.imm ((2 ^ stage.val : Nat) : Int)) (.imm 0) (.imm (-1))) = _
  have hWidth : 2 ^ stage.val < 2 ^ 32 := by
    have hs := stage.isLt
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hBits : readBits l g t 32 (.imm ((2 ^ stage.val : Nat) : Int)) =
      .ok (BitVec.ofNat 64 (2 ^ stage.val)) := by
    simp only [readBits, BitVec.ofInt_natCast, truncBits_ofNat hWidth (by decide),
      pure, Except.pure]
  have hm : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hz : readBits l g t 32 (.imm 0) = .ok 0 := rfl
  simp only [shflTmpl, readValue, readReg, hv, hb, hBits, hm, hz, pure, Except.pure,
    toNat_ofNat_lt (show 2 ^ stage.val < 2 ^ 64 by omega)]
  rfl

private def scanGuard (stage : Fin 5) (lane : Nat) : Bool :=
  if stage.val = 0 then decide (lane = 0) else decide (2 ^ stage.val ≤ lane)

private theorem scanCompare (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) :
    Seg kernel [] l g 1 (scanPc stage + 1)
      [(1180, b32 lane), (scanSrc stage, b32 left), (scanDst stage, b32 recv)]
      (scanPc stage + 2)
      [(341 + stage.val, .pred (scanGuard stage lane)),
       (scanSrc stage, b32 left), (scanDst stage, b32 recv)] := by
  have hLane : lane < 2 ^ 32 := by omega
  have hLane64 : lane < 2 ^ 64 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have h1 : (↑(truncBits 32 (BitVec.ofInt 64 1)).toNat : Int) = 1 := rfl
  have h3 : (↑(truncBits 32 (BitVec.ofInt 64 3)).toNat : Int) = 3 := rfl
  have h7 : (↑(truncBits 32 (BitVec.ofInt 64 7)).toNat : Int) = 7 := rfl
  have h15 : (↑(truncBits 32 (BitVec.ofInt 64 15)).toNat : Int) = 15 := rfl
  fin_cases stage <;>
    intro t ht <;>
    seg_fp ht using
      simp only [scanGuard, Nat.reduceEqDiff, ↓reduceIte, compare, Option.getD_some,
        truncBits_ofNat hLane (by decide), toNat_ofNat_lt hLane64,
        Value.pred.injEq, decide_eq_decide, hz, h1, h3, h7, h15]
      all_goals omega

private theorem scanSelect (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (scanPc stage + 2)
      [(341 + stage.val, .pred (scanGuard stage lane)),
       (scanSrc stage, b32 left), (scanDst stage, b32 recv)]
      (scanPc stage + 4)
      [(scanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  have hLeft : left < 2 ^ 32 := by omega
  have hRecv : recv < 2 ^ 32 := by omega
  by_cases h : 2 ^ stage.val ≤ lane
  · have hp : scanGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [scanGuard, hst, show lane ≠ 0 by omega]
      · simp [scanGuard, h, hst]
    fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;>
      seg_fp ht using norm_bits [ite_eq_left h]
  · have hp : scanGuard stage lane = decide (stage.val = 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [scanGuard, hst, show lane = 0 by omega]
      · simp [scanGuard, h, hst]
    fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;>
      seg_fp ht using norm_bits [ite_eq_right h]

/-- The three local instructions after an up-shuffle implement its guarded addition. -/
theorem scanCombine (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 3 (scanPc stage + 1)
      [(1180, b32 lane), (scanSrc stage, b32 left), (scanDst stage, b32 recv)]
      (scanPc stage + 4)
      [(scanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] :=
  (scanCompare stage l g hl).comp (scanSelect stage l g hl hsum)

/-- The shuffle source given by PTX and the decoded local addition implement one round of the
inclusive prefix scan. -/
theorem scanFold (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hl : lane < 32)
    (hsum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 3 (scanPc stage + 1)
      [(1180, b32 lane), (scanSrc stage, b32 (prefixWindow xs (2 ^ stage.val) lane)),
       (scanDst stage,
         b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (scanPc stage + 4)
      [(scanResult stage, b32 (prefixWindow xs (2 * 2 ^ stage.val) lane))] := by
  rw [prefixWindow_double]
  have h := scanCombine stage l g hl hsum
  rw [firstScanSource] at h ⊢
  by_cases hcut : 2 ^ stage.val ≤ lane <;> simpa only [hcut, ↓reduceIte] using h

end
end PTX.Kernels.TmlFa4Fwd.Mma
