-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Activation
public import Lemmas.Flow.TcTmpl
import all Init.Data.ToString.Extra
import all Init.Data.Repr
import Mathlib.Tactic.Ring

@[expose] public section
namespace FlashKda.Packed.Bfloat
open PTX

private theorem scaled (m : Nat) (e : Int) :
    ((m*65536 : Nat) : ℚ) * (2 : ℚ)^(e-16) = (m : ℚ)*2^e := by
  calc
    _ = (m : ℚ) * ((2 : ℚ)^(e-16) * (2 : ℚ)^(16 : Int)) := by
      push_cast
      ring
    _ = _ := by rw [← zpow_add₀ (by decide : (2 : ℚ) ≠ 0)]; simp

private theorem magnitude (n : Nat) :
    FloatFmt.f32.magnitude (n*65536) = FloatFmt.bf16.magnitude n := by
  change Layout.magnitude 8 23 (n*65536) = Layout.magnitude 8 7 n
  unfold Layout.magnitude
  norm_num only [Nat.reducePow]
  rw [show n*65536/8388608 = n/128 by omega,
      show n*65536%8388608 = n%128*65536 by omega]
  split
  · convert scaled (n%128) (1 - Layout.bias 8 - 7) using 2
    congr 1
  · rw [show 8388608 + n%128*65536 = (128+n%128)*65536 by omega]
    convert scaled (128+n%128) ((n/128 : Nat) - Layout.bias 8 - 7) using 2
    congr 1
    omega

set_option maxRecDepth 8192 in
theorem shifted_value (n : Nat) : FloatFmt.f32.decode (n*65536) = FloatFmt.bf16.decode n := by
  rw [FloatFmt.decode_eq, FloatFmt.decode_eq]
  have fields : n*65536%2147483648 = n%32768*65536 := by omega
  have exponent : n%32768*65536/8388608 = n%32768/128 := by omega
  have sign : n*65536/2147483648 = n/32768 :=
    Nat.mul_div_mul_right n 32768 (by decide : 0 < 65536)
  simp only [FloatFmt.expBits, FloatFmt.mantBits, FloatFmt.layout, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, fields, exponent, sign, magnitude]
  by_cases e : n%32768/128 = 255 <;> by_cases neg : n/32768%2 = 0 <;> simp [e, neg]

def shift (dst src : Nat) : Op := .int {
  op := .shl, ty := .int .b 32, dsts := [some dst], srcs := [.reg src, .imm 16] }

theorem shift_exec (L : Launch) (g d r : Nat) (t : TState) (n : Fin 65536)
    (h : t.regs r = some (Proof.b32 n.val)) :
    execLocalA [Activation.arithmetic, Activation.approximate] L g t (shift d r) =
      .ok (next (setReg t d (Proof.b32 (n.val*65536)))) := by
  change (do
    let x ← readBits L g t 32 (.reg r)
    let s ← readBits L g t 32 (.imm 16)
    pure (next (setReg t d (.bits 32 (if s.toNat ≥ 32 then 0 else truncBits 32 (x <<< s.toNat))))))
      = _
  have small := n.isLt
  rw [Proof.readBits_b32 h (by omega)]
  change Except.ok (next (setReg t d (.bits 32 (truncBits 32 (BitVec.ofNat 64 n.val <<< 16))))) = _
  congr 4
  simp [truncBits, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : n.val*65536 < 4294967296)]

def narrow (d r : Nat) : CvtInstr :=
  { dst := .float .bf16, src := .float .f32, rnd := some .rn, d, srcs := [.reg r] }

noncomputable def exactNarrow : Assumption where
  name := "flash-kda-real-bfloat-conversion"
  statement := "For finite FP32 operands the scalar conversion to BF16 preserves the real value."
  localRule _ _ t op := match op with
    | .cvt c => do
      let [.reg r] := c.srcs | none
      if c ≠ narrow c.d r then none else
        Assumption.bindRead (Assumption.readFinite t .f32 (.reg r)) fun x =>
          some (.ok (next (setReg t c.d (.float .bf16 x))))
    | _ => none

theorem narrow_exec (L : Launch) (g d r : Nat) (t : TState) (x : ℝ)
    (h : Assumption.readFinite t .f32 (.reg r) = some (.ok x)) :
    execLocalA [exactNarrow, Activation.arithmetic, Activation.approximate] L g t
      (.cvt (narrow d r)) = .ok (next (setReg t d (.float .bf16 x))) := by
  change execLocalRule _ _ _ _ _ = _
  apply Flow.execLocalRule_cons_some
  simp [exactNarrow, narrow, h, Assumption.bindRead]

def gateLoad (d a off : Nat) : Instr := ⟨none, .mem {
  kind := .load, space := some (.shared .cta), sem := .weak, scope := none, elem := .int .b 16,
  vec := 1, ext := .zero 32, addr := ⟨.reg a 32, off⟩, dsts := [some d], srcs := [] }⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 60000 in
theorem sites :
    Transfers.slice 2314 6 = some ([gateLoad 1949 1948 36864, ⟨none, shift 1950 1949⟩] ++
      Activation.code 1950 1564 1563 1951 1952) ∧
    Transfers.slice 2320 6 = some ([gateLoad 1953 1948 36880, ⟨none, shift 1954 1953⟩] ++
      Activation.code 1954 1566 1565 1955 1956) ∧
    Transfers.slice 474 1 = some [⟨none, .cvt (narrow 98 564)⟩] := ⟨rfl,rfl,rfl⟩

theorem zero_extended_load (t : TState) (d : Nat) (bs : List (Option Byte)) (n : Fin 65536)
    (fresh : t.acc = []) (start : t.sub = 0)
    (data : rebuild 3 bs = .ok (.bits 16 (BitVec.ofNat 64 n.val))) :
    (afterAccessLoad t (.zero 32) 16 [d] bs).regs d = some (Proof.b32 n.val) := by
  simp [afterAccessLoad, fresh, start, data, extendLoaded, Value.bitPattern, MemExt.extendBits,
    truncBits, setRegs, setReg, Proof.b32, bind, Except.bind, pure, Except.pure]
  rw [Nat.mod_eq_of_lt n.isLt]

theorem gate_from_pattern (L : Launch) (g src wide product power sum dst : Nat)
    (t : TState) (n : Fin 65536) (q : ℚ) (finite : FloatFmt.bf16.decode n.val = some q)
    (h : t.regs src = some (Proof.b32 n.val)) :
    ∃ out, ((⟨none, shift wide src⟩ : Instr) :: Activation.code wide product power sum dst).foldlM
      (m := Exec) (fun st i => execLocalA [Activation.arithmetic, Activation.approximate]
        L g st i.op) t = .ok out ∧
        out.regs dst = some (.float .f32 (Activation.strength (q : ℝ))) := by
  let st := next (setReg t wide (Proof.b32 (n.val*65536)))
  have value := Flow.readEReal_bits32 (n.val*65536) q rfl
    (by have := n.isLt; omega) ((shifted_value n.val).trans finite)
  have reg : st.regs wide = some (Proof.b32 (n.val*65536)) := by simp [st, next, setReg]
  have hread := (Flow.readERealOpnd_reg (fmt := .f32) reg).trans value
  have gate := Activation.evaluate L g st wide product power sum dst (q : ℝ) hread
  simp only [List.foldlM_cons, shift_exec L g wide src t n h, bind, Except.bind]
  refine ⟨_, gate, ?_⟩
  simp [Activation.put, next, setReg]

end FlashKda.Packed.Bfloat
