-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFallbackEntry
public import Lemmas.Arith.WarpPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

def fallbackRoundPc (round : Nat) : Nat := 2022 + 3 * round

def fallbackRoundReg (round : Nat) : Nat :=
  if round = 0 then 7196 else if round = 5 then 7197 else 2483 + 3 * round

def fallbackShuffleDst (stage : Fin 5) : Nat := 2484 + 3 * stage.val

def fallbackRoundGuard (stage : Fin 5) (lane : Nat) : Bool :=
  if stage.val = 0 then decide (lane = 0) else decide (2 ^ stage.val ≤ lane)

def fallbackScanPredicates (lane : Nat) : List (Nat × Value) :=
  [(355, .pred (decide (16 ≤ lane))), (356, .pred (decide (8 ≤ lane))),
    (357, .pred (decide (4 ≤ lane))), (358, .pred (decide (2 ≤ lane))),
    (359, .pred (decide (lane = 0)))]

@[simp] theorem fallbackRoundGuardFact (stage : Fin 5) (lane : Nat) :
    (359 - stage.val, .pred (fallbackRoundGuard stage lane)) ∈ fallbackScanPredicates lane := by
  fin_cases stage <;> simp [fallbackRoundGuard, fallbackScanPredicates]

/-- The fallback scan computes its five lane predicates once before the up exchanges. -/
theorem initializeFallbackPredicates (l : Launch) (g : Nat) {lane : Nat} (hLane : lane < 32) :
    Seg kernel [] l g 5 2017 [(1180, b32 lane)] 2022 (fallbackScanPredicates lane) := by
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  have h0 : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have h1 : (↑(truncBits 32 (BitVec.ofInt 64 1)).toNat : Int) = 1 := rfl
  have h3 : (↑(truncBits 32 (BitVec.ofInt 64 3)).toNat : Int) = 3 := rfl
  have h7 : (↑(truncBits 32 (BitVec.ofInt 64 7)).toNat : Int) = 7 := rfl
  have h15 : (↑(truncBits 32 (BitVec.ofInt 64 15)).toNat : Int) = 15 := rfl
  intro t ht
  dsimp only [fallbackScanPredicates]
  seg_fp ht using
    simp only [compare, Option.getD_some, truncBits_ofNat h32 (by decide),
      toNat_ofNat_lt h64, h0, h1, h3, h7, h15, Value.pred.injEq, decide_eq_decide]
    all_goals omega

private def fallbackWarpInstr (stage : Fin 5) : WarpInstr :=
  { kind := .shfl .up, ty := some (.int .b 32), dsts := [some (fallbackShuffleDst stage)],
    srcs := [.reg (fallbackRoundReg stage.val), .imm ((2 ^ stage.val : Nat) : Int), .imm 0],
    mask := some (.imm (-1)) }

private theorem fallbackWarpFields : ∀ stage : Fin 5,
    (kernel.code[fallbackRoundPc stage.val]?).bind (fun i => match i.op with
      | .warp w => some (i.guard, w)
      | _ => none) = some (none, fallbackWarpInstr stage) := by decide +kernel

private theorem fallbackShuffleCode (stage : Fin 5) :
    kernel.code[fallbackRoundPc stage.val]? = some ⟨none, .warp (fallbackWarpInstr stage)⟩ := by
  have h := fallbackWarpFields stage
  cases hc : kernel.code[fallbackRoundPc stage.val]? with
  | none => simp [hc] at h
  | some i =>
    rcases i with ⟨guard, op⟩
    cases op <;> simp only [hc, Option.bind_some, reduceCtorEq] at h
    case warp w =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rfl

/-- The fallback scan exchanges the preceding partial sum at the decoded doubling offset. -/
theorem fallbackUpTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (stage : Fin 5) (sum : Nat)
    (ht : At t (fallbackRoundPc stage.val) [(fallbackRoundReg stage.val, b32 sum)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .up (b32 sum) (2 ^ stage.val) 0
      (fun value _ => next (setReg t (fallbackShuffleDst stage) value))) := by
  have hStage := stage.isLt
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hc := fallbackShuffleCode stage
  rw [← ht.1] at hc
  rw [out_eq_core (by rw [ht.1]; unfold fallbackRoundPc; omega)
    (by rw [ht.1]; unfold fallbackRoundPc; omega), out_event ht.2.2.2.1 hc rfl rfl]
  change Out.ev (shflTmpl l g t .up (fallbackShuffleDst stage) none
    (.reg (fallbackRoundReg stage.val)) (.imm ((2 ^ stage.val : Nat) : Int))
    (.imm 0) (.imm (-1))) = _
  have hWidth : 2 ^ stage.val < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hBits : readBits l g t 32 (.imm ((2 ^ stage.val : Nat) : Int)) =
      .ok (BitVec.ofNat 64 (2 ^ stage.val)) := by
    simp only [readBits, BitVec.ofInt_natCast, truncBits_ofNat hWidth (by decide),
      pure, Except.pure]
  have hm : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hz : readBits l g t 32 (.imm 0) = .ok 0 := rfl
  have hInt : readBits l g t 32 (.imm ((2 : Int) ^ stage.val)) =
      .ok (BitVec.ofNat 64 (2 ^ stage.val)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hBits
  simp [shflTmpl, readValue, readReg, ht.2.2.2.2.1, hBlock, hInt, hm, hz, pure, Except.pure,
    toNat_ofNat_lt (show 2 ^ stage.val < 2 ^ 64 by omega)]
  rfl

private theorem fallbackCombine (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hLane : lane < 32) (hSum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (fallbackRoundPc stage.val + 1)
      [(359 - stage.val, .pred (fallbackRoundGuard stage lane)),
        (fallbackRoundReg stage.val, b32 left), (fallbackShuffleDst stage, b32 recv)]
      (fallbackRoundPc (stage.val + 1))
      [(fallbackRoundReg (stage.val + 1),
        b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  have hLeft : left < 2 ^ 32 := by omega
  have hRecv : recv < 2 ^ 32 := by omega
  by_cases h : 2 ^ stage.val ≤ lane
  · have hGuard : fallbackRoundGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hZero : stage.val = 0
      · rw [hZero, Nat.pow_zero] at h
        simp [fallbackRoundGuard, hZero, show lane ≠ 0 by omega]
      · simp [fallbackRoundGuard, h, hZero]
    fin_cases stage <;> intro t ht <;> simp only [hGuard] at ht <;>
      seg_fp ht using norm_bits [ite_eq_left h]
  · have hGuard : fallbackRoundGuard stage lane = decide (stage.val = 0) := by
      by_cases hZero : stage.val = 0
      · rw [hZero, Nat.pow_zero] at h
        simp [fallbackRoundGuard, hZero, show lane = 0 by omega]
      · simp [fallbackRoundGuard, h, hZero]
    fin_cases stage <;> intro t ht <;> simp only [hGuard] at ht <;>
      seg_fp ht using norm_bits [ite_eq_right h]

/-- Each fallback up exchange and its two local instructions double the prefix window. -/
theorem fallbackRoundFold (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hLane : lane < 32)
    (hSum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 2 (fallbackRoundPc stage.val + 1)
      [(359 - stage.val, .pred (fallbackRoundGuard stage lane)),
        (fallbackRoundReg stage.val, b32 (prefixWindow xs (2 ^ stage.val) lane)),
        (fallbackShuffleDst stage,
          b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (fallbackRoundPc (stage.val + 1))
      [(fallbackRoundReg (stage.val + 1), b32 (prefixWindow xs (2 * 2 ^ stage.val) lane))] := by
  rw [prefixWindow_double]
  have h := fallbackCombine stage l g hLane hSum
  rw [firstScanSource] at h ⊢
  by_cases hCut : 2 ^ stage.val ≤ lane <;> simpa only [hCut, ↓reduceIte] using h

end PTX.Kernels.TmlFa4Fwd.Mma
