-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.GenRules

@[expose] public section

/-! # The values of one dequantized chunk

The generated run of a chunk (`Gen/Runs*.lean`) states its values as terms in the outcome
functions `ue8E`, `e4E`, `mulE` of the start values. On a scale byte `s < 255` broadcast into both
halves and a halfword of the raw word `w` whose bytes are finite e4m3 patterns, a product is the
dequantized pair `dequantPair w s k` (`pair_val`), and the 128-bit join of the four pairs is
`dequantChunk w s` (`join_chunk`), the eight bf16 values `e4m3Val (byteAt w i) * ue8m0Val s`
(`Numeric.Dequant`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section

/-- A state at a pc of the role with the registers `regs`. -/
def probe (regs : Nat → Option Value) : TState := { pc := 2740, regs := regs }

theorem probe_pc (R : Nat → Option Value) : 2696 ≤ (probe R).pc := by
  show 2696 ≤ 2740; decide

theorem regs_next_setReg (t : TState) (d : Nat) (v : Value) :
    (PTX.next (setReg t d v)).regs d = some v := by
  simp [PTX.next, setReg]

/-- An outcome function's value from a step of its instruction at a pc of the role. -/
theorem fn_val {op : Op} {f : List Value → Exec Value} {srcs : List Nat} {L : Launch}
    {g d : Nat} {t : TState}
    (h : ∀ s : TState, s.pc = t.pc → (XItem.fn op d srcs f).Rule Assumptions.all L g s)
    {W : Nat → Value} (hW : ∀ r ∈ srcs, t.regs r = some (W r)) {X : Value}
    (hx : execLocalA Assumptions.all L g t op = .ok (PTX.next (setReg t d X))) :
    f (srcs.map W) = .ok X := by
  rw [h t rfl W hW] at hx
  cases hf : f (srcs.map W) with
  | error e => rw [hf] at hx; cases hx
  | ok v =>
    rw [hf] at hx
    have he := congrArg (fun s : TState => s.regs d) (Except.ok.inj hx)
    simp only [regs_next_setReg, Option.some.injEq] at he
    rw [he]

theorem e4E_val (L : Launch) {a b : Nat} (ha : a < 256) (hb : b < 256) (ha1 : a ≠ 127)
    (ha2 : a ≠ 255) (hb1 : b ≠ 127) (hb2 : b ≠ 255) :
    e4E [bits16 (a + 256 * b)] = .ok (.pair (e4m3Widened a) (e4m3Widened b)) := by
  let t := probe fun r => if r = 0 then some (bits16 (a + 256 * b)) else none
  have hr : t.regs 0 = some (bits16 (a + 256 * b)) := rfl
  exact fn_val (op := e4Op 1 [0]) (L := L) (g := 0) (t := t) (rule_e4 _ (probe_pc _))
    (W := fun _ => bits16 (a + 256 * b)) (fun r hr' => by simp at hr'; subst hr'; rfl)
    (execLocalA_e4m3 (probe_pc _) hr ha hb ha1 ha2 hb1 hb2)

theorem ue8E_val (L : Launch) {s : Nat} (hs : s < 255) :
    ue8E [bits16 (s + 256 * s)] = .ok (Assumptions.bf16Pair (ue8m0Val s) (ue8m0Val s)) := by
  let t := probe fun r => if r = 0 then some (bits16 (s + 256 * s)) else none
  have hr : t.regs 0 = some (bits16 (s + 256 * s)) := rfl
  exact fn_val (op := ue8Op 1 [0]) (L := L) (g := 0) (t := t) (rule_ue8 _ (probe_pc _))
    (W := fun _ => bits16 (s + 256 * s)) (fun r hr' => by simp at hr'; subst hr'; rfl)
    (execLocalA_ue8m0 (probe_pc _) hr hs)

theorem mulE_val (L : Launch) (x y s : Nat) :
    mulE [.pair (e4m3Widened x) (e4m3Widened y),
        Assumptions.bf16Pair (ue8m0Val s) (ue8m0Val s)] =
      .ok (Assumptions.bf16Pair (e4m3Val x * ue8m0Val s) (e4m3Val y * ue8m0Val s)) := by
  let W : Nat → Value := fun r => if r = 0 then .pair (e4m3Widened x) (e4m3Widened y)
    else Assumptions.bf16Pair (ue8m0Val s) (ue8m0Val s)
  let t := probe fun r => some (W r)
  have hx := execLocalA_pairMul (L := L) (g := 0) (t := t) (a := 0) (b := 1) (dst := 2)
    (x := x) (y := y) (scale := s) (probe_pc _) rfl rfl
  exact fn_val (op := mulOp 2 [0, 1]) (L := L) (g := 0) (t := t) (rule_mul _ (probe_pc _))
    (W := W)
    (fun r _ => rfl) hx

/-- No byte of the raw word is an e4m3 NaN pattern. -/
def RawOk (w : Nat) : Prop := ∀ i < 8, byteAt w i ≠ 127 ∧ byteAt w i ≠ 255

theorem e4E_byte (L : Launch) {w : Nat} (hw : RawOk w) (k : Nat) (hk : k < 4) :
    e4E [bits16 (byteAt w (2 * k) + 256 * byteAt w (2 * k + 1))] =
      .ok (.pair (e4m3Widened (byteAt w (2 * k))) (e4m3Widened (byteAt w (2 * k + 1)))) :=
  e4E_val L (byteAt_lt _ _) (byteAt_lt _ _) (hw _ (by omega)).1 (hw _ (by omega)).2
    (hw _ (by omega)).1 (hw _ (by omega)).2

theorem pair_val (L : Launch) {w s : Nat} (hw : RawOk w) (hs : s < 255) (k : Nat) (hk : k < 4) :
    okVal (.bits 32 0) (mulE [okVal (.bits 32 0)
      (e4E [bits16 (byteAt w (2 * k) + 256 * byteAt w (2 * k + 1))]),
      okVal (.bits 32 0) (ue8E [bits16 (s + 256 * s)])]) = dequantPair w s k := by
  rw [e4E_byte L hw k hk, ue8E_val L hs]
  simp only [okVal]
  rw [mulE_val L]
  rfl

theorem bf16Pair_bytes (x y : ℝ) : (Assumptions.bf16Pair x y).bytes = 4 := rfl

/-- **The stored chunk**: the 128-bit join of the two packed words is `dequantChunk w s`. -/
theorem join_chunk (w s : Nat) :
    joinValue (joinValue (dequantPair w s 0) (dequantPair w s 1))
      (joinValue (dequantPair w s 2) (dequantPair w s 3)) = dequantChunk w s := rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
