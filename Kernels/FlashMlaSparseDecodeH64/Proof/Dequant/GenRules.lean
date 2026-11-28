-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.OutLit
public import Lemmas.Flow.FloatOutcome
public import Lemmas.Flow.CoreNumeric

@[expose] public section

/-! # The dequantizer's readings for generated runs

The lemmas `Tools/out_gen.py` names in the dequantizer's run declarations
(`Gen/Out/dequant_*.json`).
The three numeric instructions of a chunk are the role's own readings (`XItem.fn`), each an outcome
function on the values of its sources: `cvt.rn.bf16x2.ue8m0x2` (`ue8E`: the kernel's reading of
the pattern `0` as `2^-127`, else Core's conversion), `cvt.rn.bf16x2.e4m3x2` (`e4E`: Core's exact
widening) and `mul.bf16x2` (`mulE`: the exact product of two bf16 pairs, else Core's IEEE rule).
`rule_e4`, `rule_ue8` and `rule_mul` give their readings at a pc of the role (each the `rule` of
its `fn` declaration); `rule_pack` the moves. Core's conversion and product are the library's
(`Lemmas/Flow/CoreNumeric.lean`). No assumption takes a segment anywhere (`noSegments`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section
variable {L : Launch} {g : Nat}

/-- No assumption takes a segment at `pc`. -/
theorem dqSegFree (pc : Nat) : Assumption.SegFreePc Assumptions.all pc :=
  noSegments.segFreePc

/-! ### Outcome functions on values -/

/-- `readBits` of a register holding `v`. -/
def bitsV (w : Nat) (v : Value) : Exec (BitVec 64) :=
  match v with
  | .bits _ x => pure (truncBits w x)
  | .ptr .. | .policy => throw .noRule
  | v => match v.bitPattern with
    | some n => pure (truncBits w (BitVec.ofNat 64 n))
    | none => throw .typeMismatch

theorem readBits_reg {t : TState} {r w : Nat} {v : Value} (h : t.regs r = some v) :
    readBits L g t w (.reg r) = bitsV w v := by
  simp only [readBits, readReg, h, bind, Except.bind, pure, Except.pure, bitsV]
  cases v <;> rfl

/-- What `cvt.rn.bf16x2.e4m3x2` writes: Core's exact widening. -/
def e4E : List Value → Exec Value
  | [v] => coreCvtPair8 .e4m3 v
  | _ => throw .noRule

/-- What `cvt.rn.bf16x2.ue8m0x2` writes: a pair with a byte `0` (and no `0xff`) by the kernel's
reading `2^-127`, else Core's conversion. -/
def ue8E : List Value → Exec Value
  | [v] => match bitsV 16 v with
    | .ok n =>
      if (n.toNat % 256 = 0 ∨ n.toNat / 256 % 256 = 0) ∧
          ¬ (n.toNat % 256 = 255 ∨ n.toNat / 256 % 256 = 255) then
        .ok (Assumptions.bf16Pair (ue8m0Val (n.toNat % 256)) (ue8m0Val (n.toNat / 256 % 256)))
      else coreCvtPair8 .ue8m0 v
    | .error _ => coreCvtPair8 .ue8m0 v
  | _ => throw .noRule

/-- The two bf16 numbers of a packed register value, as `pairValue` reads them. -/
def pairV (v : Value) : Option (ℝ × ℝ) :=
  match v with
  | .pair lo hi => do
    let x ← (valFloat .bf16 lo).toOption
    let y ← (valFloat .bf16 hi).toOption
    pure (x, y)
  | _ => none

theorem pairValue_reg {t : TState} {r : Nat} {v : Value} (h : t.regs r = some v) :
    Assumptions.pairValue L g t (.reg r) = pairV v := by
  simp only [Assumptions.pairValue, readValue, readReg, h, pure, Except.pure, pairV]
  cases v <;> rfl

/-- What `mul.bf16x2` writes: the exact product of two bf16 pairs, else Core's rule. -/
def mulE : List Value → Exec Value
  | [va, vb] => match pairV va, pairV vb with
    | some (x0, x1), some (y0, y1) => .ok (Assumptions.bf16Pair (x0 * y0) (x1 * y1))
    | _, _ => coreFloat (mulBf16x2I 0 0 0) [va, vb]
  | _ => throw .noRule

/-! ### The instructions of a generated run -/

/-- `cvt.rn.bf16x2.e4m3x2 d, a`. -/
def e4Op (d : Nat) (s : List Nat) : Op := .cvt (cvtPair8I .e4m3 (s.getD 0 0) d)

/-- `cvt.rn.bf16x2.ue8m0x2 d, a`. -/
def ue8Op (d : Nat) (s : List Nat) : Op := .cvt (cvtPair8I .ue8m0 (s.getD 0 0) d)

/-- `mul.bf16x2 d, a, b`. -/
def mulOp (d : Nat) (s : List Nat) : Op := .float (mulBf16x2I (s.getD 0 0) (s.getD 1 0) d)

/-- **The reading of `cvt.rn.bf16x2.e4m3x2`** at a pc of the role. -/
theorem rule_e4 {d a : Nat} (pc : Nat) (hp : 2696 ≤ pc) :
    ∀ t : TState, t.pc = pc → (XItem.fn (e4Op d [a]) d [a] e4E).Rule Assumptions.all L g t := by
  intro t ht W hW
  have h := hW a (by simp)
  rw [execLocalA_dequant (ht ▸ hp) rfl rfl rfl rfl]
  exact execLocal_cvtPair8 (.inl rfl) h

/-- **The reading of `cvt.rn.bf16x2.ue8m0x2`** at a pc of the role. -/
theorem rule_ue8 {d a : Nat} (pc : Nat) (hp : 2696 ≤ pc) :
    ∀ t : TState, t.pc = pc → (XItem.fn (ue8Op d [a]) d [a] ue8E).Rule Assumptions.all L g t := by
  intro t ht W hW
  have h := hW a (by simp)
  rw [execLocalA_dequant (ht ▸ hp) rfl rfl rfl rfl]
  change ((Assumptions.cvtUe8m0.localRule _ _ t (ue8Op d [a])).getD
    (execLocal _ _ t (.cvt (cvtPair8I .ue8m0 a d)))) = _
  rw [execLocal_cvtPair8 (.inr rfl) h]
  simp only [Assumptions.cvtUe8m0, ue8Op, cvtPair8I, List.getD_cons_zero, readBits_reg h,
    List.map_cons, List.map_nil, ue8E]
  rcases bitsV 16 (W a) with e | n
  · rfl
  · simp only
    split_ifs <;> first | rfl | (exfalso; tauto)

/-- **The reading of `mul.bf16x2`** at a pc of the role. -/
theorem rule_mul {d a b : Nat} (pc : Nat) (hp : 2696 ≤ pc) :
    ∀ t : TState, t.pc = pc →
      (XItem.fn (mulOp d [a, b]) d [a, b] mulE).Rule Assumptions.all L g t := by
  intro t ht W hW
  have ha := hW a (by simp)
  have hb := hW b (by simp)
  rw [execLocalA_dequant (ht ▸ hp) rfl rfl rfl rfl]
  change ((Assumptions.mulBf16x2.localRule _ _ t (.float (mulBf16x2I a b d))).getD
    ((Assumptions.cvtUe8m0.localRule _ _ t (.float (mulBf16x2I a b d))).getD
      (execLocal _ _ t (.float (mulBf16x2I a b d))))) = _
  rw [execLocal_mulBf16x2 ha hb]
  simp only [Assumptions.mulBf16x2, mulBf16x2I_fields, pairValue_reg ha, pairValue_reg hb,
    List.map_cons, List.map_nil, mulE]
  rcases pairV (W a) with _ | ⟨x0, x1⟩
  · rfl
  rcases pairV (W b) with _ | ⟨y0, y1⟩
  · rfl
  · rfl

/-- **No assumption reads a move** at a pc of the role. -/
theorem rule_pack {d a b : Nat} (pc : Nat) (hp : 2696 ≤ pc) :
    ∀ s : TState, s.pc = pc → (XItem.base (.pack d a b)).Rule Assumptions.all L g s := by
  intro t ht a' ha'
  have hs : 2696 ≤ t.pc := ht ▸ hp
  have hpa : t.pc ∉ paramAdds := by simp [paramAdds]; omega
  have hpf : t.pc ∉ prefetchTensorMapSites := by
    simp [prefetchTensorMapSites]; omega
  have hsb : t.pc ∉ Assumptions.sharedBitsSites := by
    simp [Assumptions.sharedBitsSites]; omega
  have hd : Assumptions.deadPackWords t.pc = none :=
    Assumptions.deadPackWords.eq_3 _ (by omega) (by omega)
  have hsc : Assumptions.sharedBitsSites.contains t.pc = false := by simpa using hsb
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (simp [Assumptions.paramPointers, hpa, hpf]; done)
    | (simp only [Assumptions.sharedBits, hsc, Bool.false_eq_true, ↓reduceIte, OItem.op,
        Assumptions.deadPackRule_of_none hd, Option.orElse, Assumptions.peerPackRule_move])

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
