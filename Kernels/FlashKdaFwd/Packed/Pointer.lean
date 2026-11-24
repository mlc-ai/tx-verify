-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Activation
public import Kernels.FlashKdaFwd.Packed.StateSwizzle
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Pointer
open PTX

def shift (dst src : Nat) : Instr := ⟨none, .int {
  op := .shr, ty := .int .u 64, dsts := [some dst], srcs := [.reg src, .imm 3] }⟩

def mask (dst src : Nat) : Instr := ⟨none, .int {
  op := .and, ty := .int .b 64, dsts := [some dst], srcs := [.reg src, .imm 16] }⟩

def combine (dst maskReg src : Nat) : Instr := ⟨none, .int {
  op := .xor, ty := .int .b 64, dsts := [some dst], srcs := [.reg maskReg, .reg src] }⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 8000000 in
theorem site : Transfers.slice 470 3 =
    some [shift 2311 2310, mask 2312 2311, combine 2313 2312 2310] := by rfl

theorem core_shift (L : Launch) (g d r issuer owner : Nat) (t : TState) (off : BitVec 64)
    (h : t.regs r = some (.ptr 64 true (.shared issuer owner) off)) :
    execLocalA [Activation.arithmetic, Activation.approximate] L g t (shift d r).op =
      .error .noRule := by
  change (do
    let x ← readBits L g t 64 (.reg r)
    let s ← readBits L g t 32 (.imm 3)
    pure (next (setReg t d (.bits 64 (if s.toNat ≥ 64 then 0 else x >>> s.toNat))))) = _
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]

def rule (base : Nat → Nat → Nat) (t : TState) : Op → Option (Exec TState)
  | .int ⟨.shr, .int .u 64, false, [some d], [.reg r, .imm 3]⟩ => do
    let .ptr 64 true (.shared issuer owner) off ← t.regs r | none
    let b := base issuer owner
    if b+off.toNat ≥ 2^64 then return .error .badValue
    return .ok (next (setReg t d (.bits 64 (BitVec.ofNat 64 (b+off.toNat) >>> 3))))
  | .int ⟨.xor, .int .b 64, false, [some d], [.reg m, .reg r]⟩ => do
    let .bits 64 bits ← t.regs m | none
    let .ptr 64 true (.shared issuer owner) off ← t.regs r | none
    if bits ≠ 0 ∧ bits ≠ 16 then none else
      let b := base issuer owner
      if b+off.toNat ≥ 2^64 then return .error .badValue
      let y := (BitVec.ofNat 64 (b+off.toNat) ^^^ bits).toNat
      if y < b then return .error .badValue
      return .ok (next (setReg t d (.ptr 64 true (.shared issuer owner) (BitVec.ofNat 64 (y-b)))))
  | _ => none

def representation (base : Nat → Nat → Nat) : Assumption where
  name := "flash-kda-shared-address"
  statement := "The generic address of a shared byte is its window base plus its byte offset. " ++
    "A right shift reads this number. XOR with zero or sixteen retains the shared window " ++
    "when the result is within it. The kernel uses a 256-byte-aligned window base."
  localRule _ _ t op := rule base t op

def put (t : TState) (r : Nat) (v : Value) := next (setReg t r v)

def windowWord (b : Nat) (off : BitVec 64) := BitVec.ofNat 64 (b+off.toNat)

theorem shift_exec (base : Nat → Nat → Nat) (L : Launch) (g d r issuer owner : Nat)
    (t : TState) (off : BitVec 64) (h : t.regs r = some (.ptr 64 true (.shared issuer owner) off))
    (fits : base issuer owner + off.toNat < 2^64) :
    execLocalA [representation base, Activation.arithmetic, Activation.approximate] L g t
      (shift d r).op = .ok (put t d (.bits 64 (windowWord (base issuer owner) off >>> 3))) := by
  change execLocalRule _ _ _ _ _ = _
  apply PTX.Flow.execLocalRule_cons_some
  simp [representation, rule, shift, h, put, windowWord]
  exact fits

private theorem trunc (v : BitVec 64) : truncBits 64 v = v := by
  unfold truncBits
  rw [Nat.mod_eq_of_lt v.isLt, BitVec.ofNat_toNat]
  simp

theorem mask_exec (base : Nat → Nat → Nat) (L : Launch) (g d r : Nat) (t : TState)
    (x : BitVec 64) (h : t.regs r = some (.bits 64 x)) :
    execLocalA [representation base, Activation.arithmetic, Activation.approximate] L g t
      (mask d r).op = .ok (put t d (.bits 64 (x &&& 16))) := by
  change (do
    let a ← readBits L g t 64 (.reg r)
    let b ← readBits L g t 64 (.imm 16)
    pure (next (setReg t d (.bits 64 (a &&& b))))) = _
  simp [readBits, readReg, h, trunc, put, bind, Except.bind, pure, Except.pure]

private theorem mask_values (x : BitVec 64) :
    (x &&& 16) = 0 ∨ (x &&& 16) = 16 := by
  change x &&& BitVec.twoPow 64 4 = 0 ∨ x &&& BitVec.twoPow 64 4 = 16
  rw [BitVec.and_twoPow]
  split <;> decide

theorem combine_exec (base : Nat → Nat → Nat) (L : Launch) (g d m r issuer owner : Nat)
    (t : TState) (off : BitVec 64) (h : t.regs r = some (.ptr 64 true (.shared issuer owner) off))
    (aligned : base issuer owner % 256 = 0) (fits : base issuer owner + off.toNat < 2^64)
    (hm : t.regs m = some (.bits 64 ((windowWord (base issuer owner) off >>> 3) &&& 16))) :
    execLocalA [representation base, Activation.arithmetic, Activation.approximate] L g t
      (combine d m r).op =
        .ok (put t d (.ptr 64 true (.shared issuer owner) (StateMap.swizzleWord off))) := by
  change execLocalRule _ _ _ _ _ = _
  apply PTX.Flow.execLocalRule_cons_some
  have valid := mask_values (windowWord (base issuer owner) off >>> 3)
  have bounded := StateMap.swizzle_window (base issuer owner) off.toNat aligned fits
  simp only [BitVec.ofNat_toNat] at bounded
  have addr : ((windowWord (base issuer owner) off) ^^^
      ((windowWord (base issuer owner) off >>> 3) &&& 16)).toNat =
      base issuer owner + (StateMap.swizzleWord off).toNat := bounded
  generalize eqn : (windowWord (base issuer owner) off >>> 3) &&& 16 = bits at valid hm addr
  have allowed : ¬(bits ≠ 0 ∧ bits ≠ 16) := fun h => valid.elim h.1 h.2
  change rule base t (combine d m r).op = _
  simp only [rule, combine, h, hm]
  change (if bits ≠ 0 ∧ bits ≠ 16 then none else
    if 2^64 ≤ base issuer owner + off.toNat then some (Except.error Fault.badValue)
    else if (windowWord (base issuer owner) off ^^^ bits).toNat < base issuer owner
    then some (Except.error Fault.badValue) else some (Except.ok (put t d
      (.ptr 64 true (.shared issuer owner)
      (BitVec.ofNat 64 ((windowWord (base issuer owner) off ^^^ bits).toNat-base issuer owner))))))
      = _
  rw [ite_eq_right allowed, ite_eq_right (Nat.not_le_of_lt fits), addr, ite_eq_right (by omega),
    Nat.add_sub_cancel_left]
  simp

theorem execute_site (base : Nat → Nat → Nat) (L : Launch) (g issuer owner : Nat)
    (t : TState) (off : BitVec 64)
    (h : t.regs 2310 = some (.ptr 64 true (.shared issuer owner) off))
    (aligned : base issuer owner % 256 = 0) (fits : base issuer owner + off.toNat < 2^64) :
    let word := windowWord (base issuer owner) off >>> 3
    let shifted := put t 2311 (.bits 64 word)
    let masked := put shifted 2312 (.bits 64 (word &&& 16))
    [shift 2311 2310, mask 2312 2311, combine 2313 2312 2310].foldlM (m := Exec)
      (fun st i => execLocalA [representation base, Activation.arithmetic, Activation.approximate]
        L g st i.op) t =
      .ok (put masked 2313 (.ptr 64 true (.shared issuer owner) (StateMap.swizzleWord off))) := by
  let word := windowWord (base issuer owner) off >>> 3
  let a := put t 2311 (.bits 64 word)
  let b := put a 2312 (.bits 64 (word &&& 16))
  have ha : a.regs 2311 = some (.bits 64 word) := by simp [a, put, next, setReg]
  have hb : b.regs 2312 = some (.bits 64 (word &&& 16)) := by simp [b, put, next, setReg]
  have keep : b.regs 2310 = some (.ptr 64 true (.shared issuer owner) off) := by
    simpa [a, b, put, next, setReg] using h
  have hm := mask_exec base L g 2312 2311 a word ha
  have hc := combine_exec base L g 2313 2312 2310 issuer owner b off keep aligned fits hb
  dsimp only [b, a, word] at hm hc
  dsimp only
  simp only [List.foldlM_cons, shift_exec base L g 2311 2310 issuer owner t off h fits, bind,
    Except.bind, hm, hc, List.foldlM_nil]
  rfl

end FlashKda.Packed.Pointer
