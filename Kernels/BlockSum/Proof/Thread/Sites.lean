-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Flow.Code
public import Kernels.BlockSum.Flow.Sites
public import Kernels.BlockSum.Assumptions
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts

@[expose] public section

/-! # A thread of `block_sum` as abstract states

Every thread loads its input `A[g]`, stores it to its own shared cell, and arrives at the
CTA barrier. Thread 0 of each CTA then reads the 256 shared cells, accumulating their sum,
and writes it to `B[c]`; every other thread exits. An abstract state is the next event with
the loaded input `v`, the loop index `i`, the accumulator register `acc` and the real sum `s`
it holds. A read whose bytes the code cannot use (no value, a value of another width, or no
`f32` reading in the sum) makes the thread fault, and the machine stops (`none`). -/

namespace PTX.Kernels.BlockSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event sites of a thread. -/
inductive Site where
  /-- The load of the input `A[g]`. -/
  | input
  /-- The store of the input to the thread's shared cell. -/
  | share
  /-- The CTA barrier. -/
  | bar
  /-- A read of a shared cell in the reduction loop. -/
  | sum
  /-- The store of the sum to `B[c]`. -/
  | out
  | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .input => Flow.load_0 | .share => Flow.store_0 | .bar => Flow.bar_0
  | .sum => Flow.load_1 | .out => Flow.store_1 | .exit => Flow.exit_0

structure D where
  site : Site
  /-- The loaded input. -/
  v : Value := PTX.Proof.b32 0
  /-- The loop index: the shared cells read so far. -/
  i : Nat := 0
  /-- The accumulator register. -/
  acc : Value := PTX.Proof.b32 0
  /-- The sum the accumulator holds, as the ideal rule reads it. -/
  s : EReal := 0

/-- The registers of an abstract state, by id, with the predicates of the two branches. -/
def values (A B : Nat) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  [(21, PTX.Proof.b64 (A + 4 * g)), (17, PTX.Proof.b64 B), (5, PTX.Proof.b32 (g % 256)),
   (4, PTX.Proof.b32 (g / 256)), (11, PTX.Proof.b32 (L.sharedBase + 4 * (g % 256))), (8, d.v),
   (15, d.acc), (14, PTX.Proof.b32 d.i), (13, PTX.Proof.b32 (L.sharedBase + 4 * d.i)),
   (24, PTX.Proof.b64 (B + 4 * (g / 256))), (1, .pred (decide (g % 256 ≠ 0))),
   (2, .pred (decide (d.i ≠ 256)))]

def valueOf (A B : Nat) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values A B L g d).lookup r).getD (PTX.Proof.b32 0)

def factsAt (A B : Nat) (L : Launch) (g pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf A B L g d)

abbrev facts (A B : Nat) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  factsAt A B L g d.site.pc d

/-- A finite number as a value of format `f32` reads back as itself. -/
theorem readEReal_erealValue_coe (x : ℝ) :
    Assumption.readEReal .f32 (Assumption.erealValue .f32 (x : EReal)) = some (.ok (x : EReal)) :=
  by
  have h : Assumption.erealValue .f32 (x : EReal) = .float .f32 x := by
    unfold Assumption.erealValue
    rw [ite_eq_right (EReal.coe_ne_top x), ite_eq_right (EReal.coe_ne_bot x)]
    simp
  rw [h]
  simp [Assumption.readEReal, pure, Except.pure]

/-- `+∞` as the bits of that infinity reads back as `⊤`. -/
theorem readEReal_erealValue_top :
    Assumption.readEReal .f32 (Assumption.erealValue .f32 ⊤) = some (.ok ⊤) := by
  have h : Assumption.erealValue .f32 ⊤ =
      .bits 32 (BitVec.ofNat 64 (FloatFmt.f32.layout.infPattern false)) := by
    unfold Assumption.erealValue
    rw [ite_eq_left rfl]
    rfl
  rw [h]
  have hd : FloatFmt.f32.layout.decode (FloatFmt.f32.layout.infPattern false) =
      some (.inf false) :=
    FloatFmt.decode_infPattern .f32 (by decide) false
  have hc : classify .f32 (.bits 32 (BitVec.ofNat 64
      (FloatFmt.f32.layout.infPattern false))) = .ok (.inf false) := by
    simpa [FloatFmt.bytes] using
      classify_bits (fmt := .f32) (n := FloatFmt.f32.layout.infPattern false) (x := .inf false)
        (by decide) hd
  simp only [Assumption.readEReal]
  rw [hc]
  rfl

/-- `-∞` as the bits of that infinity reads back as `⊥`. -/
theorem readEReal_erealValue_bot :
    Assumption.readEReal .f32 (Assumption.erealValue .f32 ⊥) = some (.ok ⊥) := by
  have h : Assumption.erealValue .f32 ⊥ =
      .bits 32 (BitVec.ofNat 64 (FloatFmt.f32.layout.infPattern true)) := by
    unfold Assumption.erealValue
    rw [ite_eq_right (by simp), ite_eq_left rfl]
    rfl
  rw [h]
  have hd : FloatFmt.f32.layout.decode (FloatFmt.f32.layout.infPattern true) = some (.inf true) :=
    FloatFmt.decode_infPattern .f32 (by decide) true
  have hc : classify .f32 (.bits 32 (BitVec.ofNat 64
      (FloatFmt.f32.layout.infPattern true))) = .ok (.inf true) := by
    simpa [FloatFmt.bytes] using
      classify_bits (fmt := .f32) (n := FloatFmt.f32.layout.infPattern true) (x := .inf true)
        (by decide) hd
  simp only [Assumption.readEReal]
  rw [hc]
  rfl

/-- **The value of an extended real reads back as that extended real**: the accumulator an ideal
step writes is one the next ideal step reads. -/
theorem readEReal_erealValue (x : EReal) :
    Assumption.readEReal .f32 (Assumption.erealValue .f32 x) = some (.ok x) := by
  rcases x with _ | _ | x
  · exact readEReal_erealValue_bot
  · exact readEReal_erealValue_top
  · exact readEReal_erealValue_coe x

structure Inv (d : D) : Prop where
  share : d.site = .share → d.v.bytes = 4
  sum : d.site = .sum → d.i < 256 ∧ Assumption.readEReal .f32 d.acc = some (.ok d.s)
  out : d.site = .out → d.acc = Assumption.erealValue .f32 d.s ∧ d.i = 256

/-- The extended-real reading of the bytes of a 4-byte read, if the ideal rule takes the add.
The rule reads a payload as its number and an infinity as `⊤` or `⊥`, and declines an add with a
NaN operand: a word with no `f32` reading stops the thread, while an infinite one keeps the sum
infinite and the loop goes on. -/
def readVal (bs : List (Option Byte)) : Option EReal :=
  match rebuild 3 bs with
  | .ok v => match Assumption.readEReal .f32 v with
    | some (.ok y) => some y
    | _ => none
  | .error _ => none

/-- The number of bytes of a value of an extended real. -/
theorem erealValue_bytes (r : EReal) : (Assumption.erealValue .f32 r).bytes = 4 := by
  unfold Assumption.erealValue
  repeat' split
  all_goals rfl

/-- The accumulator register the ideal add of the sum `r` writes. -/
def accOf (r : EReal) : Value := Assumption.erealValue .f32 r

def next (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .input =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => if v.bytes = 4 then some (some { d with site := .share, v := v }) else none
      | .error _ => none
    | _ => none
  | .share => some (some { d with site := .bar })
  | .bar =>
    if g % 256 = 0 then some (some { d with site := .sum, i := 0, acc := PTX.Proof.b32 0, s := 0 })
    else some (some { d with site := .exit })
  | .sum =>
    match e.kind with
    | .rd _ bs => match readVal bs with
      | some y => match Assumption.addEReal d.s y with
        | some r =>
          if d.i + 1 < 256 then
            some (some { d with i := d.i + 1, s := r, acc := accOf r })
          else
            some (some { d with site := .out, i := d.i + 1, s := r, acc := accOf r })
        | none => none
      | none => none
    | _ => none
  | .out => some (some { d with site := .exit })
  | .exit => none

local notation "Prod" => [Assumptions.idealAdd]

/-- Thread `g` as a site machine. -/
def code (A B : Nat) (L : Launch) (g : Nat) : Flow.Code kernel Prod L g where
  D := D
  init := { site := .input }
  pc := fun d => d.site.pc
  facts := facts A B L g
  inv := Inv
  next := next g

end
end PTX.Kernels.BlockSum.Proof
