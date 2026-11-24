-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegDead
public import Lemmas.Flow.MaxCore

@[expose] public section

/-! # Runs that read raw words

A proof tool, for a straight-line run of local instructions some of whose operands are raw
words a load returned, so that evaluation cannot decide whether the instructions accept them.
The run is a list of items (`RItem`), each one instruction of a few forms: `and.b32` and
integer `setp` with an immediate, the unpack `mov.b64 {lo, hi}, a`, `selp.f32` and `max.f32`
(under the ideal reading). Each item has a function of the register values `V` before it:

* the values it writes (`vals`), as the instruction computes them when it accepts its operands;
* a requirement (`req`, decided): the integer operands are integers, the selector is a
  predicate and the selected operand a register or a `0f` constant;
* a condition (`cond`): the unpacked pair has eight bytes and its halves four each, the
  selected value has four bytes, the `max.f32` outcome (`maxE`: the ideal maximum in the
  extended reals, or the Core rule's where a NaN operand makes the ideal rule decline) is no
  fault. Without it the instruction fails.

`rRun` takes the whole run (`rCond`: each item's condition on the values before it): local
steps write each register the run writes with its value after the run (`rFinal`); without
`rCond` the thread is dead. `SegD.reads` is the run as a piece. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- One instruction of a read run. -/
inductive RItem where
  /-- `and.b32 d, a, k`. -/
  | andImm (d a : Nat) (k : Int)
  /-- `setp.cmp.ty32 p, a, k`. -/
  | setpImm (cmp : Cmp) (ty : IType) (p a : Nat) (k : Int)
  /-- `mov.b64 {lo, hi}, a`. -/
  | unpack (lo hi a : Nat)
  /-- `selp.f32 d, a, b, p`. -/
  | selp (d : Nat) (a b : Opnd) (p : Nat)
  /-- `max.f32 d, a, b` or `max.f32 d, a, b, c`. -/
  | fmax (d a b : Nat) (c : Option Nat)

/-- The register an operand names, if any. -/
def opndRegs : Opnd → List Nat
  | .reg r => [r]
  | _ => []

/-- The bits of an integer value (`0` for any other). -/
def bitsOf : Value → BitVec 64
  | .bits _ x => x
  | _ => 0

/-- Whether a value is an integer. -/
def isBits : Value → Bool
  | .bits _ _ => true
  | _ => false

/-- The truth of a predicate value (`false` for any other). -/
def predOf : Value → Bool
  | .pred b => b
  | _ => false

/-- Whether a value is a predicate. -/
def isPred : Value → Bool
  | .pred _ => true
  | _ => false

/-- Whether an operand is a register or a `0f` constant. -/
def isRegOrF32 : Opnd → Bool
  | .reg _ | .f32imm _ => true
  | _ => false

/-- The value of a register or `0f` operand. -/
def opndVal (V : Nat → Value) : Opnd → Value
  | .reg r => V r
  | .f32imm b => .bits 32 (BitVec.ofNat 64 b)
  | _ => .pred false

namespace RItem

/-- The instruction. -/
def op : RItem → Op
  | andImm d a k => .int ⟨.and, .int .b 32, false, [some d], [.reg a, .imm k]⟩
  | setpImm cmp ty p a k =>
    .int ⟨.setp cmp none, .int ty 32, false, [some p], [.reg a, .imm k]⟩
  | unpack lo hi a => .move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩
  | selp d a b p => .int ⟨.selp, .float .f32, false, [some d], [a, b, .reg p]⟩
  | fmax d a b c => maxOp d (a :: b :: c.toList)

/-- Whether the item is a `max.f32`, whose local rule the ideal-real assumption gives. -/
def isMax : RItem → Bool
  | fmax .. => true
  | _ => false

/-- The source values of a `max.f32` item. -/
def maxSrcs (V : Nat → Value) (a b : Nat) (c : Option Nat) : List Value :=
  V a :: V b :: c.toList.map V

/-- The registers the item reads. -/
def reads : RItem → List Nat
  | andImm _ a _ => [a]
  | setpImm _ _ _ a _ => [a]
  | unpack _ _ a => [a]
  | selp _ a b p => p :: (opndRegs a ++ opndRegs b)
  | fmax _ a b c => a :: b :: c.toList

/-- The registers the item writes. -/
def writes : RItem → List Nat
  | andImm d _ _ => [d]
  | setpImm _ _ p _ _ => [p]
  | unpack lo hi _ => [lo, hi]
  | selp d _ _ _ => [d]
  | fmax d _ _ _ => [d]

/-- The values the item writes, in the order it writes them. -/
def vals (V : Nat → Value) : RItem → List (Nat × Value)
  | andImm d a k =>
    [(d, .bits 32 (truncBits 32 (bitsOf (V a)) &&& truncBits 32 (BitVec.ofInt 64 k)))]
  | setpImm cmp ty p a k =>
    [(p, .pred (compare cmp ty 32 (truncBits 32 (bitsOf (V a)))
      (truncBits 32 (BitVec.ofInt 64 k))))]
  | unpack lo hi a => [(lo, (splitValue 64 (V a)).1), (hi, (splitValue 64 (V a)).2)]
  | selp d a b p => [(d, opndVal V (if predOf (V p) then a else b))]
  | fmax d a b c => [(d, okVal (.bits 32 0) (maxE (maxSrcs V a b c)))]

/-- The requirement, decided. -/
def req (V : Nat → Value) : RItem → Bool
  | andImm _ a _ => isBits (V a)
  | setpImm cmp ty p a k => isBits (V a) &&
      (IntInstr.rule ⟨.setp cmp none, .int ty 32, false, [some p], [.reg a, .imm k]⟩ ==
        some .threadInt)
  | unpack .. => true
  | selp _ a b p => isPred (V p) && isRegOrF32 (if predOf (V p) then a else b)
  | fmax .. => true

/-- The condition under which the instruction accepts its operands. -/
def cond (V : Nat → Value) : RItem → Prop
  | andImm .. => True
  | setpImm .. => True
  | unpack _ _ a => (V a).bytes = 8 ∧ (splitValue 64 (V a)).1.bytes = 4 ∧
      (splitValue 64 (V a)).2.bytes = 4
  | selp _ a b p => (opndVal V (if predOf (V p) then a else b)).bytes = 4
  | fmax _ a b c => ∃ v, maxE (maxSrcs V a b c) = .ok v

/-- The values after the item. -/
def upd (V : Nat → Value) (it : RItem) : Nat → Value :=
  (it.vals V).foldl (fun (V : Nat → Value) (p : Nat × Value) => Function.update V p.1 p.2) V

/-- The state after the item. -/
def post (V : Nat → Value) (it : RItem) (t : TState) : TState :=
  PTX.next ((it.vals V).foldl (fun t p => setReg t p.1 p.2) t)

/-- The item's instruction is at `pc`. -/
def codeB (K : Kernel) (pc : Nat) : RItem → Bool
  | andImm d a k => match K.code[pc]? with
    | some ⟨none, .int ⟨.and, .int .b 32, false, [some d'], [.reg a', .imm k']⟩⟩ =>
      d == d' && a == a' && k == k'
    | _ => false
  | setpImm cmp ty p a k => match K.code[pc]? with
    | some ⟨none, .int ⟨.setp cmp' none, .int ty' 32, false, [some p'],
        [.reg a', .imm k']⟩⟩ =>
      cmp == cmp' && ty == ty' && p == p' && a == a' && k == k'
    | _ => false
  | unpack lo hi a => match K.code[pc]? with
    | some ⟨none, .move ⟨.unpack, .int .b 64, [some lo', some hi'], [.reg a']⟩⟩ =>
      lo == lo' && hi == hi' && a == a'
    | _ => false
  | selp d a b p => match K.code[pc]? with
    | some ⟨none, .int ⟨.selp, .float .f32, false, [some d'], [a', b', .reg p']⟩⟩ =>
      d == d' && a == a' && b == b' && p == p'
    | _ => false
  | fmax d a b none => match K.code[pc]? with
    | some ⟨none, (.float {
        op := .max, ty := FTy.mk .f32 1, srcTys := [], cmpTy := none, rnd := none,
        mode := .ieee, ftz := false, sat := false, relu := false, oob := false, nanMod := false,
        xorsign := false, absMod := false, dsts := [some d'], srcs := [.reg a', .reg b'] })⟩ =>
      d == d' && a == a' && b == b'
    | _ => false
  | fmax d a b (some c) => match K.code[pc]? with
    | some ⟨none, (.float {
        op := .max, ty := FTy.mk .f32 1, srcTys := [], cmpTy := none, rnd := none,
        mode := .ieee, ftz := false, sat := false, relu := false, oob := false, nanMod := false,
        xorsign := false, absMod := false, dsts := [some d'],
        srcs := [.reg a', .reg b', .reg c'] })⟩ =>
      d == d' && a == a' && b == b' && c == c'
    | _ => false

theorem code_of {K : Kernel} {pc : Nat} {it : RItem} (h : it.codeB K pc = true) :
    K.code[pc]? = some ⟨none, it.op⟩ := by
  cases it with
  | fmax d a b c =>
    cases c <;> simp only [codeB] at h <;> split at h <;>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    · obtain ⟨⟨h1, h2⟩, h3⟩ := h; subst h1 h2 h3; rename_i hc; exact hc
    · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h; subst h1 h2 h3 h4; rename_i hc; exact hc
  | _ =>
    simp only [codeB] at h
    split at h <;> simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    all_goals first
      | (obtain ⟨⟨h1, h2⟩, h3⟩ := h; subst h1 h2 h3; rename_i hc; exact hc)
      | (obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h; subst h1 h2 h3 h4 h5; rename_i hc; exact hc)
      | (obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h; subst h1 h2 h3 h4; rename_i hc; exact hc)

theorem op_isLocal (it : RItem) (hv : it.op.varyingSregs = []) : it.op.isLocal = true := by
  cases it with
  | fmax d a b c => rfl
  | andImm d a k => simp only [op] at hv ⊢; simp [Op.isLocal, hv]
  | setpImm cmp ty p a k => simp only [op] at hv ⊢; simp [Op.isLocal, hv]
  | unpack lo hi a => simp only [op] at hv ⊢; simp [Op.isLocal, hv]
  | selp d a b p => simp only [op] at hv ⊢; simp [Op.isLocal, hv]

/-- Only a `max.f32` item is a floating form of the ideal-real assumption. -/
theorem floatForm_none (it : RItem) (h : it.isMax = false) : FloatForm.ofOp it.op = none := by
  cases it <;> simp_all [isMax, op, FloatForm.ofOp]

/-- No item is an approximate form. -/
theorem approxForm_none (it : RItem) : ApproxForm.ofOp it.op = none := by
  cases it <;> simp [op, ApproxForm.ofOp]

end RItem

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem foldl_setReg_regs (t : TState) : ∀ (l : List (Nat × Value)),
    (l.foldl (fun t p => setReg t p.1 p.2) t).regs =

        l.foldl (fun (R : Nat → Option Value) (p : Nat × Value) =>
          Function.update R p.1 (some p.2)) t.regs
  | [] => rfl
  | p :: l => by
    simp only [List.foldl_cons]
    rw [foldl_setReg_regs (setReg t p.1 p.2) l]
    rfl

theorem foldl_setReg_skel (t : TState) : ∀ (l : List (Nat × Value)),
    (l.foldl (fun t p => setReg t p.1 p.2) t).pc = t.pc ∧
      (l.foldl (fun t p => setReg t p.1 p.2) t).sub = t.sub ∧
      (l.foldl (fun t p => setReg t p.1 p.2) t).acc = t.acc ∧
      (l.foldl (fun t p => setReg t p.1 p.2) t).fault = t.fault
  | [] => ⟨rfl, rfl, rfl, rfl⟩
  | p :: l => by
    simp only [List.foldl_cons]
    exact foldl_setReg_skel (setReg t p.1 p.2) l

theorem foldl_update_some {R : Nat → Option Value} {V : Nat → Value} {r : Nat} :
    ∀ (l : List (Nat × Value)), R r = some (V r) →

        (l.foldl (fun (R : Nat → Option Value) (p : Nat × Value) =>
          Function.update R p.1 (some p.2)) R) r =
        some ((l.foldl (fun (V : Nat → Value) (p : Nat × Value) => Function.update V p.1 p.2) V) r)
  | [], h => h
  | p :: l, h => by
    simp only [List.foldl_cons]
    refine foldl_update_some l ?_
    by_cases hr : r = p.1
    · subst hr; simp
    · simp [Function.update_of_ne hr, h]

theorem foldl_update_mem {R : Nat → Option Value} {V : Nat → Value} {r : Nat} :
    ∀ (l : List (Nat × Value)), r ∈ l.map Prod.fst →

        (l.foldl (fun (R : Nat → Option Value) (p : Nat × Value) =>
          Function.update R p.1 (some p.2)) R) r =
        some ((l.foldl (fun (V : Nat → Value) (p : Nat × Value) => Function.update V p.1 p.2) V) r)
  | [], h => by simp at h
  | p :: l, h => by
    simp only [List.foldl_cons]
    by_cases hl : r ∈ l.map Prod.fst
    · exact foldl_update_mem l hl
    · have hr : r = p.1 := by simpa [hl] using h
      subst hr
      refine foldl_update_some l ?_
      simp

theorem foldl_update_other {R : Nat → Option Value} {r : Nat} :
    ∀ (l : List (Nat × Value)), r ∉ l.map Prod.fst →
      (l.foldl (fun (R : Nat → Option Value) (p : Nat × Value) =>
        Function.update R p.1 (some p.2)) R) r = R r
  | [], _ => rfl
  | p :: l, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [foldl_update_other l h.2, Function.update_of_ne h.1]

theorem RItem.vals_keys (V : Nat → Value) (it : RItem) :
    (it.vals V).map Prod.fst = it.writes := by
  cases it <;> rfl

/-- A register or `0f` operand reads as its value. -/
theorem readValue_sel {V : Nat → Value} {t : TState} {o : Opnd} (hk : isRegOrF32 o = true)
    (hr : ∀ r, o = .reg r → t.regs r = some (V r)) :
    readValue L g t 32 o = .ok (opndVal V o) := by
  cases o <;> simp only [isRegOrF32, Bool.false_eq_true] at hk
  · rename_i r
    simp [readValue, readReg, opndVal, hr r rfl, pure, Except.pure]
  · simp [readValue, readBits, opndVal, bind, Except.bind, pure, Except.pure]

/-- **One item**: under its condition the instruction steps to `post`; otherwise it fails. A
`max.f32` takes the ideal rule, or the Core rule where the ideal rule declines (`hI`, `hD`); every
other item the Core rule (`hL`). -/
theorem RItem.exec (it : RItem) {V : Nat → Value} {t : TState}
    (hS : SegFreePc A t.pc) (hI : IdealAt A (.max .f32) L g t)
    (hD : DeclineAt A (.max .f32) L g t)
    (hr : ∀ r ∈ it.reads, t.regs r = some (V r)) (hq : it.req V = true)
    (hL : it.isMax = false → ∀ a ∈ A, a.localRule L g t it.op = none) :
    (it.cond V → execLocalA A L g t it.op = .ok (it.post V t)) ∧
      (¬ it.cond V → ∃ f, execLocalA A L g t it.op = .error f) := by
  cases it with
  | andImm d a k =>
    have ha := hr a (by simp [reads])
    simp only [req] at hq
    generalize hv : V a = va at ha hq
    cases va <;> simp only [isBits, Bool.false_eq_true] at hq
    replace hL := hL rfl
    refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
    simp only [op] at hL ⊢
    simp [post, vals, hv, hS.exec rfl, execLocalRule_of_none hL,
      execLocal_int (i := ⟨.and, .int .b 32, false, [some d], [.reg a, .imm k]⟩) rfl, execInt,
      DType.width, readBits, readReg, ha, bitsOf, bind, Except.bind, pure, Except.pure]
  | setpImm cmp ty p a k =>
    have ha := hr a (by simp [reads])
    simp only [req, Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨hq, hrule⟩ := hq
    generalize hv : V a = va at ha hq
    cases va <;> simp only [isBits, Bool.false_eq_true] at hq
    replace hL := hL rfl
    refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
    simp only [op] at hL ⊢
    simp [post, vals, hv, hS.exec rfl, execLocalRule_of_none hL, execLocal_int hrule, execInt,
      DType.width, DType.kind?, readBits, readReg, ha, bitsOf, bind, Except.bind, pure, Except.pure]
  | unpack lo hi a =>
    have ha := hr a (by simp [reads])
    have he : execLocalA A L g t (unpack lo hi a).op =
        (if (V a).bytes = 8 then
          (if (splitValue 64 (V a)).1.bytes = 4 ∧ (splitValue 64 (V a)).2.bytes = 4 then
            .ok (PTX.next (setReg (setReg t lo (splitValue 64 (V a)).1) hi
              (splitValue 64 (V a)).2))
          else .error .typeMismatch)
        else .error .typeMismatch) := by
      replace hL := hL rfl
      simp only [op] at hL ⊢
      simp only [hS.exec rfl, execLocalRule_of_none hL,
        execLocal_move (m := ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩) rfl, execMove,
        DType.width, readValue, readReg, ha]
      by_cases h8 : (V a).bytes = 8 <;>
        by_cases h4 : (splitValue 64 (V a)).1.bytes = 4 ∧ (splitValue 64 (V a)).2.bytes = 4 <;>
        simp [h8, h4, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨h8, h4⟩ := h
      rw [he]
      simp [h8, h4, post, vals]
    · simp only [cond] at h
      rw [he]
      by_cases h8 : (V a).bytes = 8
      · simp only [h8, ↓reduceIte, ite_eq_right (fun h4 => h ⟨h8, h4⟩)]
        exact ⟨_, rfl⟩
      · simp only [h8, ↓reduceIte]
        exact ⟨_, rfl⟩
  | selp d a b p =>
    simp only [req, Bool.and_eq_true] at hq
    obtain ⟨hp, hk⟩ := hq
    have hpr := hr p (by simp [reads])
    generalize hv : V p = vp at hpr hp hk
    cases vp <;> simp only [isPred, Bool.false_eq_true] at hp
    rename_i pick
    simp only [predOf] at hk
    -- the selected operand
    have hsel : readValue L g t 32 (if pick then a else b) =
        .ok (opndVal V (if pick then a else b)) := by
      refine readValue_sel hk fun r hr' => hr r ?_
      cases pick <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr' <;>
        simp [reads, opndRegs, hr']
    have he : execLocalA A L g t (selp d a b p).op =
        (if (opndVal V (if pick then a else b)).bytes = 4 then
          .ok (PTX.next (setReg t d (opndVal V (if pick then a else b))))
        else .error .typeMismatch) := by
      replace hL := hL rfl
      simp only [op] at hL ⊢
      simp only [hS.exec rfl, execLocalRule_of_none hL,
        execLocal_selp (i := ⟨.selp, .float .f32, false, [some d], [a, b, .reg p]⟩) rfl, execMove,
        DType.width, readReg, hpr]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [hsel]
      by_cases h4 : (opndVal V (if pick then a else b)).bytes = 4 <;>
        simp [h4, throw, throwThe, MonadExceptOf.throw]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [cond, hv, predOf] at h
      rw [he]
      simp [h, post, vals, hv, predOf]
    · simp only [cond, hv, predOf] at h
      rw [he]
      simp only [h, ↓reduceIte]
      exact ⟨_, rfl⟩
  | fmax d a b c =>
    have ha := hr a (by simp [reads])
    have hb := hr b (by simp [reads])
    have he : execLocalA A L g t (fmax d a b c).op =
        (maxE (maxSrcs V a b c)).map fun v => PTX.next (setReg t d v) := by
      cases c with
      | none => exact exec_maxE2 hI hD ha hb
      | some c => exact exec_maxE3 hI hD ha hb (hr c (by simp [reads]))
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨v, hv⟩ := h
      rw [he, hv]
      simp [post, vals, hv, okVal, Except.map]
    · rw [he]
      cases hv : maxE (maxSrcs V a b c) with
      | ok v => exact absurd ⟨v, hv⟩ h
      | error f => exact ⟨f, rfl⟩

/-! ### A run of items -/

/-- The condition of a run: each item's, on the values before it. -/
def rCond (V : Nat → Value) : List RItem → Prop
  | [] => True
  | it :: its => it.cond V ∧ rCond (it.upd V) its

/-- The requirements of a run, decided. -/
def rReq (V : Nat → Value) : List RItem → Bool
  | [] => true
  | it :: its => it.req V && rReq (it.upd V) its

/-- The values after a run. -/
def rFinal (V : Nat → Value) : List RItem → Nat → Value
  | [] => V
  | it :: its => rFinal (it.upd V) its

/-- No assumption of `A` takes a local rule for any item's instruction other than a `max.f32`
(whose rule `IdealAt` and `DeclineAt` give): at every state the local step of such an item is the
Core rule's (`execLocalRule_of_none`). -/
def NoItemRule (A : List Assumption) (items : List RItem) : Prop :=
  ∀ it ∈ items, it.isMax = false →
    ∀ (L : Launch) (g : Nat) (t : TState), ∀ a ∈ A, a.localRule L g t it.op = none

/-- No item's instruction reads a special register whose value changes while the thread runs
(`Op.varyingSregs`): every item is a local instruction. -/
def rVaryingB : List RItem → Bool
  | [] => true
  | it :: its => (it.op.varyingSregs == []) && rVaryingB its

/-- Each item reads registers of `dom` or written before it. -/
def rReadsB (dom : List Nat) : List RItem → Bool
  | [] => true
  | it :: its => it.reads.all (· ∈ dom) && rReadsB (it.writes ++ dom) its

/-- The items' instructions follow each other from `pc`. -/
def rCodeB (K : Kernel) : Nat → List RItem → Bool
  | _, [] => true
  | pc, it :: its => it.codeB K pc && rCodeB K (pc + 1) its

/-- The registers a run writes. -/
def rWrites (items : List RItem) : List Nat := items.flatMap RItem.writes

/-- **One item**, at the state level: under its condition one local step writes its values
and keeps every register it does not write; otherwise the thread is dead. -/
theorem RItem.step (it : RItem) {V : Nat → Value} {dom : List Nat} {t : TState}
    (hc : it.codeB K t.pc = true) (hf : t.fault = none)
    (hd : ∀ r ∈ dom, t.regs r = some (V r)) (hrd : ∀ r ∈ it.reads, r ∈ dom)
    (hq : it.req V = true) (hv : it.op.varyingSregs = [])
    (hS : SegFreePc A t.pc) (hI : IdealAt A (.max .f32) L g t)
    (hD : DeclineAt A (.max .f32) L g t)
    (hL : it.isMax = false → ∀ a ∈ A, a.localRule L g t it.op = none) :
    (it.cond V → run K A L g 1 t = some (it.post V t) ∧ (it.post V t).pc = t.pc + 1 ∧
      (it.post V t).sub = t.sub ∧ (it.post V t).acc = t.acc ∧
      (it.post V t).fault = t.fault ∧
      (∀ r, r ∉ it.writes → (it.post V t).regs r = t.regs r) ∧
      ∀ r ∈ it.writes ++ dom, (it.post V t).regs r = some (it.upd V r)) ∧
    (¬ it.cond V → Machine.Dead (K := K) (A := A) (L := L) (g := g) t) := by
  have hcode := RItem.code_of hc
  have hex := it.exec hS hI hD (fun r hr => hd r (hrd r hr)) hq hL
  obtain ⟨h1, h2, h3, h4⟩ := foldl_setReg_skel t (it.vals V)
  have hregs : (it.post V t).regs = (it.vals V).foldl (fun (R : Nat → Option Value)
      (p : Nat × Value) => Function.update R p.1 (some p.2)) t.regs := by
    simp only [post, PTX.next]
    exact foldl_setReg_regs t (it.vals V)
  refine ⟨fun hc' => ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_⟩, fun hc' => ?_⟩
  · simp only [run, tauStep, tau_of_ok hcode (it.op_isLocal hv) hf (hex.1 hc')]
    rfl
  · simp [post, PTX.next, h1]
  · simp [post, PTX.next, h2]
  · simp [post, PTX.next, h3]
  · simp [post, PTX.next, h4]
  · rw [hregs, foldl_update_other _ (by rw [vals_keys]; exact hr)]
  · rw [hregs]
    rcases List.mem_append.mp hr with hw | hw
    · exact foldl_update_mem _ (by rw [vals_keys]; exact hw)
    · exact foldl_update_some _ (hd r hw)
  · obtain ⟨f, he⟩ := hex.2 hc'
    exact dead_of_error hcode (it.op_isLocal hv) hf he

/-- **A run of items**: under `rCond` local steps write each register the run writes with its
value after the run and keep every other register; otherwise the thread is dead. -/
theorem rRun : ∀ (items : List RItem) (V : Nat → Value) (dom : List Nat) (t : TState),
    rCodeB K t.pc items = true → t.fault = none → (∀ r ∈ dom, t.regs r = some (V r)) →
    rReadsB dom items = true → rReq V items = true → rVaryingB items = true →
    NoItemRule A items → (∀ k < items.length, SegFreePc A (t.pc + k)) →
    (∀ k < items.length, ∀ s : TState, s.pc = t.pc + k → IdealAt A (.max .f32) L g s) →
    (∀ k < items.length, ∀ s : TState, s.pc = t.pc + k → DeclineAt A (.max .f32) L g s) →
    (rCond V items → ∃ t', run K A L g items.length t = some t' ∧
      t'.pc = t.pc + items.length ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧ t'.fault = t.fault ∧
      (∀ r, r ∉ rWrites items → t'.regs r = t.regs r) ∧
      ∀ r ∈ rWrites items ++ dom, t'.regs r = some (rFinal V items r)) ∧
    (¬ rCond V items → Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
  | [], V, dom, t, _, _, hd, _, _, _, _, _, _, _ =>
    ⟨fun _ => ⟨t, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun r hr => hd r (by simpa [rWrites] using hr)⟩, fun h => absurd trivial h⟩
  | it :: its, V, dom, t, hc, hf, hd, hrd, hq, hvb, hN, hS, hI, hDc => by
    simp only [rCodeB, Bool.and_eq_true] at hc
    simp only [rVaryingB, Bool.and_eq_true, beq_iff_eq] at hvb
    simp only [rReadsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hrd
    simp only [rReq, Bool.and_eq_true] at hq
    have hst := it.step hc.1 hf hd hrd.1 hq.1 hvb.1 (by simpa using hS 0 (by simp))
      (hI 0 (by simp) t (by simp)) (hDc 0 (by simp) t (by simp))
      (fun hm => hN it (by simp) hm L g t)
    by_cases hok : it.cond V
    · obtain ⟨hr1, hpc1, hsub1, hacc1, hf1, hfr1, hw1⟩ := hst.1 hok
      have ih := rRun its (it.upd V) (it.writes ++ dom) (it.post V t) (by rw [hpc1]; exact hc.2)
        (hf1.trans hf) hw1 hrd.2 hq.2 hvb.2 (fun it' h' => hN it' (by simp [h']))
        (fun k hk => by rw [hpc1, Nat.add_assoc, Nat.add_comm 1 k]; exact hS _ (by simp; omega))
        (fun k hk s hs => hI (k + 1) (by simp; omega) s (by rw [hs, hpc1]; omega))
        (fun k hk s hs => hDc (k + 1) (by simp; omega) s (by rw [hs, hpc1]; omega))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨t', hr', hpc', hsub', hacc', hf', hfr', hw'⟩ := ih.1 h.2
        refine ⟨t', ?_, by rw [hpc', hpc1, List.length_cons]; omega, hsub'.trans hsub1,
          hacc'.trans hacc1, hf'.trans hf1, fun r hr => ?_, fun r hr => ?_⟩
        · rw [List.length_cons, Nat.add_comm]
          exact run_comp hr1 hr'
        · simp only [rWrites, List.flatMap_cons, List.mem_append, not_or] at hr
          rw [hfr' r hr.2, hfr1 r hr.1]
        · refine hw' r ?_
          simp only [rWrites, List.flatMap_cons, List.mem_append] at hr ⊢
          tauto
      · exact dead_of_run hr1 (ih.2 fun h' => h ⟨hok, h'⟩)
    · exact ⟨fun h => absurd h.1 hok, fun _ => hst.2 hok⟩

/-- **A run of items, as a piece**: from facts with explicit values to the values `exT` after
the run in front, under `rCond`; otherwise the thread is dead. -/
theorem SegD.reads {pc : Nat} {liveS liveT : List Nat} {base : Nat → Value}
    {ex exT : List (Nat × Value)} {items : List RItem} {keys : List Nat}
    (hcode : rCodeB K pc items = true)
    (hreads : rReadsB liveS items = true) (hreq : rReq (valueEx base ex) items = true)
    (hvb : rVaryingB items = true) (hN : NoItemRule A items)
    (hS : ∀ k < items.length, SegFreePc A (pc + k))
    (hI : ∀ k < items.length, ∀ s : TState, s.pc = pc + k → IdealAt A (.max .f32) L g s)
    (hD : ∀ k < items.length, ∀ s : TState, s.pc = pc + k → DeclineAt A (.max .f32) L g s)
    (hT : exT.map (fun p => rFinal (valueEx base ex) items p.1) = exT.map Prod.snd)
    (hk : exT.map Prod.fst = keys) (hTk : ∀ r ∈ keys, r ∈ rWrites items ++ liveS)
    (hcov : ∀ r ∈ liveT, r ∈ keys ∨ (r ∉ rWrites items ∧ r ∈ liveS)) :
    SegD K A L g items.length pc (factsFrom liveS (valueEx base ex)) (pc + items.length)
      (factsFrom liveT (valueEx base (exT ++ ex))) (rCond (valueEx base ex) items) := by
  intro t h
  have hR := h.2.2.2.2
  have hrun := rRun items (valueEx base ex) liveS t (by rw [h.1]; exact hcode) h.2.2.2.1
    (fun r hr => holds_mem hR (mem_factsFrom hr)) hreads hreq hvb hN (fun k hk => h.1 ▸ hS k hk)
    (fun k hk s hs => hI k hk s (by rw [hs, h.1])) (fun k hk s hs => hD k hk s (by rw [hs, h.1]))
  refine ⟨fun hc => ?_, hrun.2⟩
  obtain ⟨t', hr, hpc, hsub, hacc, hf, hfr, hw⟩ := hrun.1 hc
  have hT' : ∀ p ∈ exT, rFinal (valueEx base ex) items p.1 = p.2 := fun p hp =>
    List.map_inj_left.mp hT p hp
  refine ⟨t', hr, by rw [hpc, h.1], hsub.trans h.2.1, hacc.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_ext (W := rWrites items) hR hfr (fun r hr' => ?_) (hk ▸ hcov)⟩
  obtain ⟨v, hv⟩ := lookup_of_mem_keys hr'
  have hm := mem_of_lookup hv
  have hkm : r ∈ keys := hk ▸ List.mem_map_of_mem (f := Prod.fst) hm
  rw [hv, hw r (hTk _ hkm), hT' _ hm]

end
end PTX.Flow
