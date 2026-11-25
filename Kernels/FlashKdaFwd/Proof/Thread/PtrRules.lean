-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.Rules

@[expose] public section

/-! # How the kernel's assumptions read the arithmetic on generic shared pointers

The kernel addresses its FP32 state buffer through generic pointers: `cvta.shared.u64` makes a
generic pointer of the shared window's base (four instructions), `add.s64` moves it by a word
or a constant, and the swizzle `shr.u64 x, p, 3`, `and.b64 y, x, 16`, `xor.b64 q, y, p` (266
triples, read by the assumption `sharedBits`) gives the pointer a generic `ld.b32` or `st.b32`
uses. A pointer register is an opaque slot of the thread machine, and each of these
instructions is a run item (`XItem.fn`) with an outcome function on any values of its sources,
as in `Rules.lean`:

| form | outcome on the values of the sources | rule lemma |
| --- | --- | --- |
| `cvta.shared.u64 d, a` | `cvtaSharedE L g [va]` | `rule_cvtaShared` |
| `add.s64 d, a, k` | `add64KE k [va]` | `rule_add64K` |
| `add.s64 d, a, b` | `add64E [va, vb]` | `rule_add64` |
| `shr.u64 d, a, 3` | `swShrE [va]` | `rule_swShr` |
| `and.b64 d, a, k` | `and64E k [va]` | `rule_and64` |
| `xor.b64 d, m, a` | `swXorE [vm, va]` | `rule_swXor` |

An outcome is a fault exactly where the instruction faults, and then the thread is dead: a
pointer moved out of `[0, 2^32)` (`offsetPointer`), a `cvta.shared.u64` of a thread that is not
launched or of an address of `2^32` or more, an integer read of a pointer that `sharedBits`
does not select. The second part of the file evaluates the outcomes on a generic pointer into
the thread's own shared window (`…_ptr`, `swizzle_eval`), which is what the layers above
compute addresses with. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread.Rules
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.FlashKdaFwd

noncomputable section

variable {L : Launch} {g : Nat}

/-- The local step of an operation that only `sharedBits` may select: its rule where it
applies, the Core rule otherwise. -/
theorem exec_at_shared {t : TState} {op : Op}
    (h1 : Assumptions.idealArith.localRule L g t op = none)
    (h2 : Assumptions.approx.localRule L g t op = none)
    (h3 : Assumptions.narrow.localRule L g t op = none) :
    execLocalA Assumptions.all L g t op =
      match Assumptions.sharedBitsRule t op with
      | some r => r
      | none => execLocal L g t op := by
  rw [noSegments.exec]
  have hI : inert.findSome? (fun a => a.localRule L g t op) = none :=
    List.findSome?_eq_none_iff.mpr fun a ha => inert_none a ha L g t op
  have h4 : Assumptions.sharedBits.localRule L g t op = Assumptions.sharedBitsRule t op := rfl
  simp only [execLocalRule, all_eq, List.findSome?_cons, h1, h2, h3, h4, hI]
  cases Assumptions.sharedBitsRule t op <;> rfl

/-- A value is a generic pointer into a shared window, or it is not. -/
theorem genShared_cases (v : Value) :
    (∃ o c off, v = .ptr 64 true (.shared o c) off) ∨
      ∀ o c off, v ≠ .ptr 64 true (.shared o c) off := by
  by_cases h : ∃ o c off, v = .ptr 64 true (.shared o c) off
  · exact .inl h
  · exact .inr fun o c off e => h ⟨o, c, off, e⟩

/-! ### `and.b64 d, a, k` -/

/-- `and.b64 d, a, k`. -/
def and64Op (k : Int) (d : Nat) (s : List Nat) : Op :=
  .int ⟨.and, .int .b 64, false, [some d], [.reg (s.getD 0 0), .imm k]⟩

/-- The outcome of `and.b64 d, a, k` on the value of `a`: the bit pattern masked; a pointer and
a value without a bit pattern fault. -/
def and64V (k : Int) (va : Value) : Exec Value :=
  (readBitsOf 64 va).map fun (x : BitVec 64) => .bits 64 (x &&& truncBits 64 (BitVec.ofInt 64 k))

def and64E (k : Int) : List Value → Exec Value
  | [va] => and64V k va
  | _ => .error .typeMismatch

theorem rule_and64 {k : Int} {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (and64Op k d [a]) d [a] (and64E k)).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  have ha := hW a (by simp)
  show execLocalA Assumptions.all L g t
      (.int ⟨.and, .int .b 64, false, [some d], [.reg a, .imm k]⟩) = _
  rw [exec_core (all_none rfl rfl rfl rfl), execLocal_int (by rfl)]
  simp only [execInt, DType.width, readBits_reg_bitsOf ha, and64E, and64V, List.map_cons,
    List.map_nil]
  rcases readBitsOf 64 (W a) with e | x
  · rfl
  · simp [readBits, bind, Except.bind, pure, Except.pure, Except.map]

/-! ### `shr.u64 d, a, 3` -/

/-- `shr.u64 d, a, 3`. -/
def swShrOp (d : Nat) (s : List Nat) : Op :=
  .int ⟨.shr, .int .u 64, false, [some d], [.reg (s.getD 0 0), .imm 3]⟩

/-- The Core rule of `shr.u64 d, a, 3` on the value of `a` (an integer read: a pointer
faults). -/
def coreShr3 (va : Value) : Exec Value :=
  (readBitsOf 64 va).map fun (x : BitVec 64) => .bits 64
    (if 64 ≤ (truncBits 32 (BitVec.ofInt 64 3)).toNat then 0
      else x >>> (truncBits 32 (BitVec.ofInt 64 3)).toNat)

/-- The outcome of `shr.u64 d, a, 3` on the value of `a`: `sharedBits` reads a generic shared
pointer as its offset, shifted; every other value goes to the Core rule. -/
def swShrV (va : Value) : Exec Value :=
  match va with
  | .ptr 64 true (.shared _ _) off => .ok (.bits 64 (off >>> 3))
  | v => coreShr3 v

def swShrE : List Value → Exec Value
  | [va] => swShrV va
  | _ => .error .typeMismatch

theorem swShrV_other {v : Value} (hn : ∀ o c off, v ≠ .ptr 64 true (.shared o c) off) :
    swShrV v = coreShr3 v := by
  unfold swShrV
  split
  · exact absurd rfl (hn _ _ _)
  · rfl

theorem execInt_shr3 {t : TState} {d a : Nat} {v : Value} (h : t.regs a = some v) :
    execInt L g t ⟨.shr, .int .u 64, false, [some d], [.reg a, .imm 3]⟩ =
      (coreShr3 v).map fun x => PTX.next (setReg t d x) := by
  simp only [execInt, DType.width, DType.kind?, readBits_reg_bitsOf h, coreShr3]
  rcases readBitsOf 64 v with e | x
  · rfl
  · simp [readBits, bind, Except.bind, pure, Except.pure, Except.map]

theorem rule_swShr {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (swShrOp d [a]) d [a] swShrE).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  have ha := hW a (by simp)
  show execLocalA Assumptions.all L g t
      (.int ⟨.shr, .int .u 64, false, [some d], [.reg a, .imm 3]⟩) = (swShrV (W a)).map _
  rw [exec_at_shared rfl rfl rfl]
  rcases genShared_cases (W a) with ⟨o, c, off, hv⟩ | hn
  · rw [hv] at ha ⊢
    simp [Assumptions.sharedBitsRule, Assumptions.swizzleShift, ha, swShrV, Except.map, pure,
      Except.pure]
  · have hr : Assumptions.sharedBitsRule t
        (.int ⟨.shr, .int .u 64, false, [some d], [.reg a, .imm 3]⟩) = none := by
      simp only [Assumptions.sharedBitsRule, Assumptions.swizzleShift, ha]
      split
      · rename_i h
        exact absurd (Option.some.inj h) (hn _ _ _)
      · rfl
    rw [hr, swShrV_other hn, execLocal_int (by rfl)]
    exact execInt_shr3 ha

/-! ### `xor.b64 d, m, a` -/

/-- `xor.b64 d, m, a`. -/
def swXorOp (d : Nat) (s : List Nat) : Op :=
  .int ⟨.xor, .int .b 64, false, [some d], [.reg (s.getD 0 0), .reg (s.getD 1 0)]⟩

/-- The Core rule of `xor.b64` on the values of its sources (integer reads). -/
def coreXor (vm va : Value) : Exec Value := do
  let x ← readBitsOf 64 vm
  let y ← readBitsOf 64 va
  pure (.bits 64 (x ^^^ y))

/-- The outcome of `xor.b64 d, m, a`: `sharedBits` flips the bits `0` or `16` of the offset of
a generic shared pointer `a`; everything else goes to the Core rule (where a pointer faults). -/
def swXorV (vm va : Value) : Exec Value :=
  match vm, va with
  | .bits 64 bits, .ptr 64 true (.shared o c) off =>
    if bits = 0 ∨ bits = 16 then .ok (.ptr 64 true (.shared o c) (off ^^^ bits))
    else coreXor vm va
  | _, _ => coreXor vm va

def swXorE : List Value → Exec Value
  | [vm, va] => swXorV vm va
  | _ => .error .typeMismatch

theorem execInt_xor64 {t : TState} {d m a : Nat} {vm va : Value} (hm : t.regs m = some vm)
    (ha : t.regs a = some va) :
    execInt L g t ⟨.xor, .int .b 64, false, [some d], [.reg m, .reg a]⟩ =
      (coreXor vm va).map fun x => PTX.next (setReg t d x) := by
  simp only [execInt, DType.width, readBits_reg_bitsOf hm, readBits_reg_bitsOf ha, coreXor]
  rcases readBitsOf 64 vm with e | x
  · rfl
  rcases readBitsOf 64 va with e | y
  · rfl
  · simp [bind, Except.bind, pure, Except.pure, Except.map]

theorem rule_swXor {d m a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (swXorOp d [m, a]) d [m, a] swXorE).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  have hm := hW m (by simp)
  have ha := hW a (by simp)
  show execLocalA Assumptions.all L g t
      (.int ⟨.xor, .int .b 64, false, [some d], [.reg m, .reg a]⟩) = (swXorV (W m) (W a)).map _
  rw [exec_at_shared rfl rfl rfl]
  have hcore : execLocal L g t (.int ⟨.xor, .int .b 64, false, [some d], [.reg m, .reg a]⟩) =
      (coreXor (W m) (W a)).map fun x => PTX.next (setReg t d x) := by
    rw [execLocal_int (by rfl)]
    exact execInt_xor64 hm ha
  by_cases h : ∃ bits o c off, W m = .bits 64 bits ∧ W a = .ptr 64 true (.shared o c) off
  · obtain ⟨bits, o, c, off, h1, h2⟩ := h
    rw [h1] at hm
    rw [h2] at ha
    rw [h1, h2] at hcore ⊢
    by_cases hb : bits = 0 ∨ bits = 16
    · have e : (bits = 0 ∨ bits = 16) = True := eq_true hb
      simp only [Assumptions.sharedBitsRule, Assumptions.swizzleShift, Assumptions.swizzleXor, hm,
        ha, swXorV, e, ite_true, Except.map, pure, Except.pure]
    · have e : (bits = 0 ∨ bits = 16) = False := eq_false hb
      have hr : Assumptions.sharedBitsRule t
          (.int ⟨.xor, .int .b 64, false, [some d], [.reg m, .reg a]⟩) = none := by
        simp only [Assumptions.sharedBitsRule, Assumptions.swizzleShift, Assumptions.swizzleXor,
          hm, ha, e, ite_false]
      have hv : swXorV (.bits 64 bits) (.ptr 64 true (.shared o c) off) =
          coreXor (.bits 64 bits) (.ptr 64 true (.shared o c) off) := by
        simp only [swXorV, e, ite_false]
      rw [hr, hv, hcore]
  · have hr : Assumptions.sharedBitsRule t
        (.int ⟨.xor, .int .b 64, false, [some d], [.reg m, .reg a]⟩) = none := by
      simp only [Assumptions.sharedBitsRule, Assumptions.swizzleShift, Assumptions.swizzleXor,
        hm, ha]
      split
      · rename_i h1 h2
        exact absurd ⟨_, _, _, _, Option.some.inj h1, Option.some.inj h2⟩ h
      · rfl
    have hv : swXorV (W m) (W a) = coreXor (W m) (W a) := by
      unfold swXorV
      split
      · exact absurd ⟨_, _, _, _, by assumption, by assumption⟩ h
      · rfl
    rw [hr, hv, hcore]

/-! ### `add.s64 d, a, b` and `add.s64 d, a, k` -/

/-- The outcome of a 64-bit `add` on the values of its operands (Core's rule: no assumption
selects it): a pointer into a shared window, the local frame or the constant space moves by the
other operand's word and stays within `[0, 2^32)`, else the thread faults (`offsetPointer`);
two words add; every other pointer and a value without a bit pattern fault. -/
def add64V (va vb : Value) : Exec Value :=
  match va, vb with
  | .ptr _ _ (.shared ..) _, .bits _ _ | .ptr _ _ (.local _) _, .bits _ _
  | .ptr _ _ .const _, .bits _ _ =>
    readBitsOf 64 vb >>= fun delta => offsetPointer 64 va (toSigned 64 delta)
  | .bits _ _, .ptr _ _ (.shared ..) _ | .bits _ _, .ptr _ _ (.local _) _
  | .bits _ _, .ptr _ _ .const _ =>
    readBitsOf 64 va >>= fun delta => offsetPointer 64 vb (toSigned 64 delta)
  | _, _ => do
    let x ← readBitsOf 64 va
    let y ← readBitsOf 64 vb
    pure (.bits 64 (truncBits 64 (x + y)))

set_option maxHeartbeats 1600000 in
theorem execInt_add64 {t : TState} {d a b : Nat} {va vb : Value} (ha : t.regs a = some va)
    (hb : t.regs b = some vb) :
    execInt L g t ⟨.add, .int .s 64, false, [some d], [.reg a, .reg b]⟩ =
      (add64V va vb).map fun x => PTX.next (setReg t d x) := by
  have h1 : ∀ va vb : Value,
      (readBitsOf 64 vb >>= fun delta => offsetPointer 64 va (toSigned 64 delta) >>= fun v =>
        (pure (PTX.next (setReg t d v)) : Exec TState)) =
      (readBitsOf 64 vb >>= fun delta => offsetPointer 64 va (toSigned 64 delta)).map
        fun x => PTX.next (setReg t d x) := by
    intro va vb
    rcases readBitsOf 64 vb with e | y
    · rfl
    · show (offsetPointer 64 va (toSigned 64 y) >>= _) = Except.map _ (offsetPointer 64 va _)
      rcases offsetPointer 64 va (toSigned 64 y) with e | v <;> rfl
  have h3 : ∀ va vb : Value,
      (readBitsOf 64 va >>= fun x => readBitsOf 64 vb >>= fun y =>
        (pure (PTX.next (setReg t d (.bits 64 (truncBits 64 (x + y))))) : Exec TState)) =
      (readBitsOf 64 va >>= fun x => readBitsOf 64 vb >>= fun y =>
        (pure (.bits 64 (truncBits 64 (x + y))) : Exec Value)).map
        fun x => PTX.next (setReg t d x) := by
    intro va vb
    rcases readBitsOf 64 va with e | x
    · rfl
    · show (readBitsOf 64 vb >>= _) = Except.map _ (readBitsOf 64 vb >>= _)
      rcases readBitsOf 64 vb with e | y <;> rfl
  simp only [execInt, DType.width, readValue, readReg, ha, hb, readBits_reg_bitsOf ha,
    readBits_reg_bitsOf hb, add64V]
  cases va <;> cases vb <;> (try cases ‹PtrTarget›) <;> (try cases ‹PtrTarget›) <;>
    (simp only [pure_bind]; first | exact h1 _ _ | exact h3 _ _)

set_option linter.unusedTactic false in
theorem execInt_add64K {t : TState} {d a : Nat} {k : Int} {va : Value}
    (ha : t.regs a = some va) :
    execInt L g t ⟨.add, .int .s 64, false, [some d], [.reg a, .imm k]⟩ =
      (add64V va (.bits 64 (BitVec.ofInt 64 k))).map fun x => PTX.next (setReg t d x) := by
  have hi : readBits L g t 64 (.imm k) = .ok (truncBits 64 (BitVec.ofInt 64 k)) := rfl
  simp only [execInt, DType.width, readValue, readReg, ha, readBits_reg_bitsOf ha, hi, add64V]
  cases va <;> (try cases ‹PtrTarget›) <;> simp only [pure_bind] <;>
    first
    | rfl
    | (simp only [bind, Except.bind, pure, Except.pure, readBitsOf]
       generalize offsetPointer 64 _ _ = E
       rcases E with e | v <;> rfl)
    | (simp only [bind, Except.bind, pure, Except.pure]
       generalize readBitsOf 64 _ = E
       rcases E with e | x <;> rfl)

/-- `add.s64 d, a, b`. -/
def add64Op (d : Nat) (s : List Nat) : Op :=
  .int ⟨.add, .int .s 64, false, [some d], [.reg (s.getD 0 0), .reg (s.getD 1 0)]⟩

def add64E : List Value → Exec Value
  | [va, vb] => add64V va vb
  | _ => .error .typeMismatch

theorem rule_add64 {d a b : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (add64Op d [a, b]) d [a, b] add64E).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  show execLocalA Assumptions.all L g t
      (.int ⟨.add, .int .s 64, false, [some d], [.reg a, .reg b]⟩) = (add64V (W a) (W b)).map _
  rw [exec_core (all_none rfl rfl rfl rfl), execLocal_int (by rfl)]
  exact execInt_add64 (hW a (by simp)) (hW b (by simp))

/-- `add.s64 d, a, k`. -/
def add64KOp (k : Int) (d : Nat) (s : List Nat) : Op :=
  .int ⟨.add, .int .s 64, false, [some d], [.reg (s.getD 0 0), .imm k]⟩

def add64KE (k : Int) : List Value → Exec Value
  | [va] => add64V va (.bits 64 (BitVec.ofInt 64 k))
  | _ => .error .typeMismatch

theorem rule_add64K {k : Int} {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (add64KOp k d [a]) d [a] (add64KE k)).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  show execLocalA Assumptions.all L g t
      (.int ⟨.add, .int .s 64, false, [some d], [.reg a, .imm k]⟩) = _
  rw [exec_core (all_none rfl rfl rfl rfl), execLocal_int (by rfl)]
  exact execInt_add64K (hW a (by simp))

/-! ### `cvta.shared.u64 d, a` -/

/-- `cvta.shared.u64 d, a`. -/
def cvtaSharedOp (d : Nat) (s : List Nat) : Op :=
  .addr (.cvta false (.shared .cta) 64 d (.reg (s.getD 0 0)))

/-- A state whose registers all hold `v`: Core's shared-address rule reads its operand's value
only, so it is stated on this state. -/
def regsAll (v : Value) : TState := { regs := fun _ => some v }

/-- The outcome of `cvta.shared.u64 d, a` on the value of `a`, for thread `g` of launch `L`: the
generic pointer to the shared address the value names in the thread's own window
(`readSharedAddress`: the thread is launched, its CTA is in the grid, the address is below
`2^32`), else the fault. -/
def cvtaSharedV (L : Launch) (g : Nat) (v : Value) : Exec Value :=
  (readSharedAddress L g (regsAll v) 64 false false (.reg 0)).map fun loc =>
    .ptr 64 true (.shared (g / L.block) loc.cta) (BitVec.ofNat 64 loc.addr)

def cvtaSharedE (L : Launch) (g : Nat) : List Value → Exec Value
  | [va] => cvtaSharedV L g va
  | _ => .error .typeMismatch

theorem rule_cvtaShared {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (cvtaSharedOp d [a]) d [a] (cvtaSharedE L g)).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  have ha := hW a (by simp)
  show execLocalA Assumptions.all L g t (.addr (.cvta false (.shared .cta) 64 d (.reg a))) =
    (cvtaSharedV L g (W a)).map _
  rw [exec_core (all_none rfl rfl rfl rfl), execLocal_cvta (by rfl), execCvta_shared]
  have h : readSharedAddress L g t 64 false false (.reg a) =
      readSharedAddress L g (regsAll (W a)) 64 false false (.reg 0) := by
    simp only [readSharedAddress, readValue, readReg, ha, regsAll]
  show (readSharedAddress L g t 64 false false (.reg a) >>= fun loc =>
      (pure (PTX.next (setReg t d (.ptr 64 true (.shared (g / L.block) loc.cta)
        (BitVec.ofNat 64 loc.addr)))) : Exec TState)) = _
  rw [h, cvtaSharedV]
  rcases readSharedAddress L g (regsAll (W a)) 64 false false (.reg 0) with e | loc <;> rfl

/-! ### The outcomes on a generic pointer into the thread's own shared window

What the layers above compute addresses with. Every lemma is about the outcome functions only:
the rule lemmas above hold at every program counter (the rule of `sharedBits` selects by form,
not by site), so no site condition is needed here. -/

/-- A 64-bit word is its own 64-bit truncation. -/
theorem truncBits_64 (y : BitVec 64) : truncBits 64 y = y := by
  simp [truncBits, Nat.mod_eq_of_lt y.isLt]

theorem and16_nat (n : Nat) : n &&& 16 = 0 ∨ n &&& 16 = 16 := by
  have h16 : ∀ i, Nat.testBit 16 i = decide (4 = i) := fun i => by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.testBit_two_pow]
  cases hb : n.testBit 4
  · left
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : 4 = i
    · subst hi; simp [Nat.testBit_and, hb]
    · simp [Nat.testBit_and, h16, hi]
  · right
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : 4 = i
    · subst hi; simp [Nat.testBit_and, hb, h16]
    · simp [Nat.testBit_and, h16, hi]

/-- The swizzle mask is 0 or 16. -/
theorem and16_cases (y : BitVec 64) : y &&& 16#64 = 0#64 ∨ y &&& 16#64 = 16#64 := by
  have h : (y &&& 16#64).toNat = y.toNat &&& 16 := BitVec.toNat_and y 16#64
  rcases and16_nat y.toNat with h0 | h0
  · left; apply BitVec.eq_of_toNat_eq; rw [h, h0]; rfl
  · right; apply BitVec.eq_of_toNat_eq; rw [h, h0]; rfl

/-- **`cvta.shared.u64` of a word, for a launched thread**: the generic pointer to that address
of the thread's own shared window. -/
theorem cvtaSharedV_bits {w : Nat} {x : BitVec 64} (hg : g < L.threads)
    (hc : g / L.block < L.grid) (hx : (truncBits 64 x).toNat < 2 ^ 32) :
    cvtaSharedV L g (.bits w x) =
      .ok (.ptr 64 true (.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (truncBits 64 x).toNat)) := by
  have hx' : (truncBits 64 x).toNat < 4294967296 := hx
  simp [cvtaSharedV, readSharedAddress, readValue, readReg, regsAll, hg, hc, hx', bind,
    Except.bind, pure, Except.pure, Except.map]

/-- **The dead side of `cvta.shared.u64`**: a thread that is not launched, or whose CTA is
outside the grid, faults. -/
theorem cvtaSharedV_dead {w : Nat} {x : BitVec 64} (h : ¬ (g < L.threads ∧ g / L.block < L.grid)) :
    cvtaSharedV L g (.bits w x) = .error .badValue := by
  simp [cvtaSharedV, readSharedAddress, readValue, readReg, regsAll, h, bind, Except.bind,
    pure, Except.pure, Except.map, throw, throwThe, MonadExceptOf.throw]

/-- **A generic shared pointer plus a word**, under the two range conditions: the pointer moved
by the word (read as a signed 64-bit number). For `add.s64 d, a, k` the word is
`BitVec.ofInt 64 k`. -/
theorem add64V_ptr {o c : Nat} {off delta : BitVec 64} {w : Nat} (h0 : off.toNat < 2 ^ 32)
    (h1 : 0 ≤ (off.toNat : Int) + toSigned 64 (truncBits 64 delta))
    (h2 : (off.toNat : Int) + toSigned 64 (truncBits 64 delta) < 2 ^ 32) :
    add64V (.ptr 64 true (.shared o c) off) (.bits w delta) =
      .ok (.ptr 64 true (.shared o c)
        (BitVec.ofInt 64 ((off.toNat : Int) + toSigned 64 (truncBits 64 delta)))) := by
  have eN : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have eZ : (2 : Int) ^ 32 = 4294967296 := by norm_num
  rw [eN] at h0
  rw [eZ] at h2
  simp [add64V, readBitsOf, offsetPointer, h0, h1, h2, bind, Except.bind, pure, Except.pure]

/-- **The dead side of a pointer addition**: outside the range conditions the thread faults. -/
theorem add64V_ptr_dead {o c : Nat} {off delta : BitVec 64} {w : Nat}
    (h : ¬ (off.toNat < 2 ^ 32 ∧ 0 ≤ (off.toNat : Int) + toSigned 64 (truncBits 64 delta) ∧
      (off.toNat : Int) + toSigned 64 (truncBits 64 delta) < 2 ^ 32)) :
    add64V (.ptr 64 true (.shared o c) off) (.bits w delta) = .error .noRule := by
  have eN : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have eZ : (2 : Int) ^ 32 = 4294967296 := by norm_num
  rw [eN, eZ] at h
  simp only [add64V, readBitsOf, offsetPointer, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw]
  simp
  exact fun a b => not_lt.mp fun hc => h ⟨a, b, hc⟩

/-- **The whole swizzle** `shr.u64 x, p, 3; and.b64 y, x, 16; xor.b64 q, y, p` on a generic
shared pointer `p` of offset `off`: the three outcomes are values, and `q` is the pointer with
offset `off ^^^ ((off >>> 3) &&& 16)`. No side condition: the mask is always 0 or 16. -/
theorem swizzle_eval (o c : Nat) (off : BitVec 64) :
    swShrV (.ptr 64 true (.shared o c) off) = .ok (.bits 64 (off >>> 3)) ∧
    and64V 16 (.bits 64 (off >>> 3)) = .ok (.bits 64 ((off >>> 3) &&& 16#64)) ∧
    swXorV (.bits 64 ((off >>> 3) &&& 16#64)) (.ptr 64 true (.shared o c) off) =
      .ok (.ptr 64 true (.shared o c) (off ^^^ ((off >>> 3) &&& 16#64))) := by
  refine ⟨rfl, ?_, ?_⟩
  · have e : truncBits 64 (BitVec.ofInt 64 16) = 16#64 := by decide
    simp only [and64V, readBitsOf, pure, Except.pure, Except.map, truncBits_64, e]
  · have e : ((off >>> 3) &&& 16#64 = 0 ∨ (off >>> 3) &&& 16#64 = 16) = True :=
      eq_true (and16_cases _)
    simp only [swXorV, e, ite_true]

/-- **The dead side of the swizzle**: the shift and the `xor` of a pointer that is no generic
shared pointer are integer reads of a pointer, which fault (`noRule`). -/
theorem swShrV_ptr_dead {w : Nat} {gen : Bool} {sp : PtrTarget} {off : BitVec 64}
    (hn : ∀ o c off', Value.ptr w gen sp off ≠ .ptr 64 true (.shared o c) off') :
    swShrV (.ptr w gen sp off) = .error .noRule := by
  rw [swShrV_other hn]
  rfl

/-! ### The shift in the form of a run declaration

`Tools/out_gen.py` writes a form whose last source is a constant as `.fn (op k d [srcs]) d
[srcs] (f k)`; the shift's constant is always 3 and is part of `swShrOp`, so these names take
and ignore it. A declaration whose `shr.u64` has another constant fails at the instruction
check of its piece (`XItem.codeB_of … rfl`). -/

abbrev swShrOpK (_k : Int) (d : Nat) (s : List Nat) : Op := swShrOp d s

abbrev swShrEK (_k : Int) : List Value → Exec Value := swShrE

theorem rule_swShrK {k : Int} {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (swShrOpK k d [a]) d [a] (swShrEK k)).Rule
      Assumptions.all L g s :=
  rule_swShr pc

/-! ### `cvta.shared.u64` as a piece of its own

The run library checks a run's instructions with `OItem.instrB` (`Lemmas/Flow/OutRun.lean`),
which knows floating-point, move, integer and conversion instructions only: an address
instruction cannot be an item of a generated run (`XItem.codeB_of … rfl` fails on it). So a
`cvta.shared.u64` is a piece of one instruction, from the code equation itself. Its outcome
names the launch and the thread, which the definitions of a generated run do not take
either. -/

/-- **One `fn` item as a piece, from the code equation**: under its condition (the outcome is
no fault) one local step writes the outcome; otherwise the thread is dead. For an instruction
`OItem.instrB` does not recognize. -/
theorem fn_piece {K : Kernel} {A : List Assumption} {pc d : Nat} {srcs : List Nat} {op : Op}
    {f : List Value → Exec Value} (hcode : K.code[pc]? = some ⟨none, op⟩)
    (hloc : op.isLocal = true)
    (hR : ∀ s : TState, s.pc = pc → (XItem.fn op d srcs f).Rule A L g s) (V : Nat → Value) :
    SegD K A L g 1 pc (factsFrom srcs V) (pc + 1)
      [(d, okVal (.bits 32 0) (f (srcs.map V)))] (∃ v, f (srcs.map V) = .ok v) := by
  intro t h
  have he := hR t h.1 V fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hc : K.code[t.pc]? = some ⟨none, op⟩ := by rw [h.1]; exact hcode
  refine ⟨fun ⟨v, hv⟩ => ?_, fun hn => ?_⟩
  · rw [hv] at he
    refine ⟨PTX.next (setReg t d v), ?_, ?_, h.2.1, h.2.2.1, h.2.2.2.1, ?_, trivial⟩
    · simp only [run, tauStep, tau_of_ok hc hloc h.2.2.2.1 he]
      rfl
    · simp [PTX.next, setReg, h.1]
    · simp [PTX.next, setReg, hv, okVal]
  · cases hE : f (srcs.map V) with
    | ok v => exact absurd ⟨v, hE⟩ hn
    | error e =>
      rw [hE] at he
      exact dead_of_error hc hloc h.2.2.2.1 he

/-- The value `cvta.shared.u64` writes, from the values `V` (its fallback is never read: the
piece continues under `cvtaCond` only). -/
abbrev cvtaVal (L : Launch) (g : Nat) (V : Nat → Value) (a : Nat) : Value :=
  okVal (.bits 32 0) (cvtaSharedE L g [V a])

/-- The condition of a `cvta.shared.u64` of register `a`: the conversion is no fault. -/
abbrev cvtaCond (L : Launch) (g : Nat) (V : Nat → Value) (a : Nat) : Prop :=
  ∃ v, cvtaSharedE L g [V a] = .ok v

/-- **`cvta.shared.u64 d, a` at `pc` as a piece**: from the value of `a` to the value of `d`,
under `cvtaCond`; otherwise the thread is dead. -/
theorem cvta_piece {K : Kernel} {pc d a : Nat}
    (hcode : K.code[pc]? = some ⟨none, cvtaSharedOp d [a]⟩) (L : Launch) (g : Nat)
    (V : Nat → Value) :
    SegD K Assumptions.all L g 1 pc [(a, V a)] (pc + 1) [(d, cvtaVal L g V a)]
      (cvtaCond L g V a) :=
  fn_piece (srcs := [a]) hcode rfl (rule_cvtaShared pc) V

end
end PTX.Kernels.FlashKdaFwd.Proof.Thread.Rules
