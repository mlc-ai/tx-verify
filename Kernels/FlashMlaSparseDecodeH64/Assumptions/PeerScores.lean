-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions

open PTX

noncomputable section

/-- One integer instruction in the shared-memory peer-score pack. -/
inductive PeerPack where
  | extend (dst src : Nat)
  | upper (dst src : Nat)
  | merge (dst low high : Nat) (highFirst : Bool)
  deriving DecidableEq

/-- The eight groups of four consecutive scores. The subsequent pack and store are Core moves. -/
def peerPack (site : Nat) : Option PeerPack :=
  if 394 ≤ site ∧ site < 474 then
    let group := (site - 394) / 10
    let score := 2886 + 4 * group
    let tmp := 3177 + 8 * group
    match (site - 394) % 10 with
    | 0 => some (.extend tmp (score + 3))
    | 1 => some (.upper (tmp + 1) tmp)
    | 2 => some (.extend (tmp + 2) (score + 2))
    | 3 => some (.extend (tmp + 3) (score + 1))
    | 4 => some (.upper (tmp + 4) (tmp + 3))
    | 5 => some (.extend (tmp + 5) score)
    | 6 => some (.merge (tmp + 6) (tmp + 5) (tmp + 4) true)
    | 7 => some (.merge (tmp + 7) (tmp + 2) (tmp + 1) false)
    | _ => none
  else none

theorem peerPack_none_of_outside {site : Nat} (h : site < 394 ∨ 474 ≤ site) :
    peerPack site = none := by
  unfold peerPack
  exact ite_eq_right (by omega)

/-- The integer operation of the copy as emitted in the frozen program. -/
def PeerPack.op : PeerPack → Op
  | .extend dst src => .cvt
      { dst := .int .u 64, src := .int .u 32, d := dst, srcs := [.reg src] }
  | .upper dst src =>
      .int ⟨.shl, .int .b 64, false, [some dst], [.reg src, .imm 32]⟩
  | .merge dst low high highFirst =>
      .int ⟨.or, .int .b 64, false, [some dst],
        if highFirst then [.reg high, .reg low] else [.reg low, .reg high]⟩

/-- The four-byte data that can be transported by the ideal peer-score pack. -/
def scoreHalf : Value → Prop
  | .float .f32 _ => True
  | .bits 32 bits => bits.toNat < 2 ^ 32
  | _ => False

instance (v : Value) : Decidable (scoreHalf v) := by
  unfold scoreHalf
  split <;> infer_instance

theorem scoreHalf_bytes {v : Value} (h : scoreHalf v) : v.bytes = 4 := by
  unfold scoreHalf at h
  split at h <;> first | rfl | contradiction

/-- The packed payload has the same bits as the low word OR the shifted high word. -/
theorem peerPair_bits {lo hi : Value} {a b : Nat} (hlo : scoreHalf lo)
    (ha : lo.bitPattern = some a) (hb : hi.bitPattern = some b) (ha32 : a < 2 ^ 32) :
    (Value.pair lo hi).bitPattern = some (a ||| (b <<< 32)) := by
  rw [Value.bitPattern, ha, hb, scoreHalf_bytes hlo, Nat.shiftLeft_eq]
  change some (a % 2 ^ 32 + 2 ^ 32 * b) = some (a ||| b * 2 ^ 32)
  rw [Nat.mod_eq_of_lt ha32, Nat.mul_comm b, Nat.add_comm a, Nat.or_comm a]
  exact congrArg some (Nat.two_pow_add_eq_or_of_lt ha32 b)

/-- The zero word used to make and merge the two 64-bit halves. -/
def peerPackZero : Value := .bits 32 0

/-- Interpret the pack as a copy of the halves of the ideal scores, preserving their payloads. -/
def PeerPack.run (t : TState) : PeerPack → Option TState
  | .extend dst src => do
    let v ← t.regs src
    if scoreHalf v then some (next (setReg t dst (.pair v peerPackZero))) else none
  | .upper dst src => do
    let .pair v zero ← t.regs src | none
    if zero = peerPackZero ∧ scoreHalf v then
      some (next (setReg t dst (.pair peerPackZero v)))
    else none
  | .merge dst low high _ => do
    let .pair lo zeroLo ← t.regs low | none
    let .pair zeroHi hi ← t.regs high | none
    if zeroLo = peerPackZero ∧ zeroHi = peerPackZero ∧ scoreHalf lo ∧ scoreHalf hi then
      some (next (setReg t dst (.pair lo hi)))
    else none

/-- Only the audited peer pack's matching integer operations may preserve score payloads. -/
def peerPackRule (t : TState) (op : Op) : Option (Exec TState) :=
  match op with
  | .cvt c =>
    match c with
    | { dst := .int .u 64, src := .int .u 32, ext := .same, sat := false,
        d := d, srcs := [.reg a], .. } =>
      match peerPack t.pc with
      | some (step@(.extend dst src)) =>
        if dst = d ∧ src = a then (step.run t).map Except.ok else none
      | _ => none
    | _ => none
  | .int ⟨.shl, .int .b 64, false, [some d], [.reg a, .imm 32]⟩ =>
    match peerPack t.pc with
    | some (step@(.upper dst src)) =>
      if dst = d ∧ src = a then (step.run t).map Except.ok else none
    | _ => none
  | .int ⟨.or, .int .b 64, false, [some d], [.reg a, .reg b]⟩ =>
    match peerPack t.pc with
    | some (step@(.merge dst low high highFirst)) =>
      if dst = d ∧ (if highFirst then (high, low) else (low, high)) = (a, b) then
        (step.run t).map Except.ok
      else none
    | _ => none
  | _ => none

theorem peerPackRule_of_none {t : TState} {op : Op} (h : peerPack t.pc = none) :
    peerPackRule t op = none := by
  unfold peerPackRule
  split
  · split <;> simp [h]
  all_goals simp [h]

@[simp] theorem peerPackRule_move (t : TState) (m : MoveInstr) :
    peerPackRule t (.move m) = none := rfl

@[simp] theorem peerPackRule_bra (t : TState) (target : Nat) (uni : Bool) :
    peerPackRule t (.bra target uni) = none := rfl

@[simp] theorem peerPackRule_mem (t : TState) (a : MemAccess) :
    peerPackRule t (.mem a) = none := rfl

@[simp] theorem peerPackRule_addr (t : TState) (a : AddrInstr) :
    peerPackRule t (.addr a) = none := rfl

/-- Every selected instruction uses the exact transport callback determined by its decoded site. -/
theorem peerPackRule_of_step {t : TState} {step : PeerPack} (h : peerPack t.pc = some step) :
    peerPackRule t step.op = (step.run t).map Except.ok := by
  cases step with
  | extend dst src => simp [PeerPack.op, peerPackRule, h]
  | upper dst src => simp [PeerPack.op, peerPackRule, h]
  | merge dst low high highFirst => cases highFirst <;> simp [PeerPack.op, peerPackRule, h]

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
