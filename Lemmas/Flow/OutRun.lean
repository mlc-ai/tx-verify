-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ArithCore
public import Lemmas.Flow.ReadRun

@[expose] public section

/-! # Runs of floating instructions on any operand values

A proof tool, for a straight-line run of local instructions whose operands are values a site
machine does not constrain (words a load returned and what the code computed from them), so that
evaluation cannot decide what the floating instructions write. The run is a list of items
(`OItem`): the moves `mov.b32 d, 0f…`, `mov.b32 d, a`, `mov.b64 d, {a, b}` and
`mov.b64 {lo, hi}, a`, the floating instructions `fma.rn.f32x2`, `add.rn.f32x2`, `ex2.approx.f32`,
`cvt.rn.f16x2.f32`, `mul.f32`, `sub.f32`, `add.f32`, `selp.f32` and `setp.f32` against a `0f`
constant; and (`XItem.fn`) any local instruction with one destination whose outcome function on
its sources' values the assumptions give (a kernel's own reading, or `max.f32` of two or three
sources with `maxE`, `XItem.max2_rule`, `XItem.max3_rule`). Each item has a function of
the register values `V` before it:

* the values it writes (`vals`): the moves' values, and for a floating instruction its outcome
  (`fma2E`, `add2E`, `ex2E`, `cvtPairE`, `mulE`, `subE`, `floatE (addI fz)`, `setpE`: the ideal
  result, or the Core rule's where the ideal rule declines), with a default where it faults;
* a requirement (`req`, decided): the selector of `selp` is a predicate and both operands are
  registers or `0f` constants, and the comparison of `setp` is ordered or unordered;
* a condition (`cond`): the moved values have their widths, a floating outcome is no fault.
  Without it the instruction fails.

At a state where no assumption takes a segment and the assumptions read the item's form as
`OItem.Rule` says (the ideal or approximate reading with its declines left to the Core rule, or no
local rule for a move), the item's step is that function (`OItem.exec`). `oRun` takes the whole
run: under `oCond` local steps write each register the run writes with its value after the run
(`oFinal`), otherwise the thread is dead. `SegD.outs` is the run as a piece from facts by any
value function `V` to facts by `oFinal V items` (`xRun`, `SegD.xouts` for runs of `XItem`s);
`oCond_unpacks` gives the condition of a run of unpacks from the widths of their sources. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- One instruction of an outcome run. -/
inductive OItem where
  /-- `mov.b32 d, 0f…` with the bits `b`. -/
  | movImm (d b : Nat)
  /-- `mov.b32 d, a`. -/
  | mov (d a : Nat)
  /-- `mov.b64 d, {a, b}`. -/
  | pack (d a b : Nat)
  /-- `mov.b64 {lo, hi}, a`. -/
  | unpack (lo hi a : Nat)
  /-- `fma.rn.f32x2 d, a, b, c`. -/
  | fma2 (d a b c : Nat)
  /-- `add.rn.f32x2 d, a, b`. -/
  | add2 (d a b : Nat)
  /-- `ex2.approx{.ftz}.f32 d, a`. -/
  | ex2 (fz : Bool) (d a : Nat)
  /-- `cvt.rn.f16x2.f32 d, a, b`. -/
  | cvt (d a b : Nat)
  /-- `mul{.ftz}.f32 d, a, b`. -/
  | mul (fz : Bool) (d a b : Nat)
  /-- `sub{.ftz}.f32 d, a, b`. -/
  | sub (fz : Bool) (d a b : Nat)
  /-- `add{.ftz}.f32 d, a, b`. -/
  | add (fz : Bool) (d a b : Nat)
  /-- `selp.f32 d, a, b, p`. -/
  | selp (d : Nat) (a b : Opnd) (p : Nat)
  /-- `setp.c{.ftz}.f32 p, a, 0f…` with the bits `k`. -/
  | setp (c : FCmp) (fz : Bool) (p a k : Nat)

/-- The truth of a comparison outcome (`false` where it faults). -/
def okPred : Exec Bool → Bool
  | .ok b => b
  | .error _ => false

/-- The floating form a comparison against the `0f` constant `k` has. -/
def setpForm (k : Nat) : FloatForm :=
  if isInfConst (.f32imm k) then .setpInf .f32 else .setp .f32

namespace OItem

/-- The instruction. -/
def op : OItem → Op
  | movImm d b => .move ⟨.scalar, .int .b 32, [some d], [.f32imm b]⟩
  | mov d a => .move ⟨.scalar, .int .b 32, [some d], [.reg a]⟩
  | pack d a b => .move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩
  | unpack lo hi a => .move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩
  | fma2 d a b c => .float { fma2I with dsts := [some d], srcs := [.reg a, .reg b, .reg c] }
  | add2 d a b => .float { add2I with dsts := [some d], srcs := [.reg a, .reg b] }
  | ex2 fz d a => .float { ex2I fz with dsts := [some d], srcs := [.reg a] }
  | cvt d a b => .cvt (cvtPairInstr d a b)
  | mul fz d a b => .float { mulI fz with dsts := [some d], srcs := [.reg a, .reg b] }
  | sub fz d a b => .float { subI fz with dsts := [some d], srcs := [.reg a, .reg b] }
  | add fz d a b => .float { addI fz with dsts := [some d], srcs := [.reg a, .reg b] }
  | selp d a b p => .int ⟨.selp, .float .f32, false, [some d], [a, b, .reg p]⟩
  | setp c fz p a k => .float { setpI c fz with dsts := [some p], srcs := [.reg a, .f32imm k] }

/-- The registers the item reads. -/
def reads : OItem → List Nat
  | movImm .. => []
  | mov _ a => [a]
  | pack _ a b => [a, b]
  | unpack _ _ a => [a]
  | fma2 _ a b c => [a, b, c]
  | add2 _ a b => [a, b]
  | ex2 _ _ a => [a]
  | cvt _ a b => [a, b]
  | mul _ _ a b => [a, b]
  | sub _ _ a b => [a, b]
  | add _ _ a b => [a, b]
  | selp _ a b p => p :: (opndRegs a ++ opndRegs b)
  | setp _ _ _ a _ => [a]

/-- The registers the item writes. -/
def writes : OItem → List Nat
  | movImm d _ => [d]
  | mov d _ => [d]
  | pack d .. => [d]
  | unpack lo hi _ => [lo, hi]
  | fma2 d .. => [d]
  | add2 d .. => [d]
  | ex2 _ d _ => [d]
  | cvt d .. => [d]
  | mul _ d .. => [d]
  | sub _ d .. => [d]
  | add _ d .. => [d]
  | selp d .. => [d]
  | setp _ _ p .. => [p]

/-- The values the item writes, in the order it writes them. -/
def vals (V : Nat → Value) : OItem → List (Nat × Value)
  | movImm d b => [(d, .bits 32 (BitVec.ofNat 64 b))]
  | mov d a => [(d, V a)]
  | pack d a b => [(d, joinValue (V a) (V b))]
  | unpack lo hi a => [(lo, (splitValue 64 (V a)).1), (hi, (splitValue 64 (V a)).2)]
  | fma2 d a b c => [(d, okVal (.bits 64 0) (fma2E (V a) (V b) (V c)))]
  | add2 d a b => [(d, okVal (.bits 64 0) (add2E (V a) (V b)))]
  | ex2 fz d a => [(d, okVal (.bits 32 0) (ex2E fz (V a)))]
  | cvt d a b => [(d, okVal (.bits 32 0) (cvtPairE (V a) (V b)))]
  | mul fz d a b => [(d, okVal (.bits 32 0) (mulE fz (V a) (V b)))]
  | sub fz d a b => [(d, okVal (.bits 32 0) (subE fz (V a) (V b)))]
  | add fz d a b => [(d, okVal (.bits 32 0) (floatE (addI fz) [V a, V b]))]
  | selp d a b p => [(d, if predOf (V p) then opndVal V a else opndVal V b)]
  | setp c fz p a k => [(p, .pred (okPred (setpE c fz (V a) (.bits 32 (BitVec.ofNat 64 k)))))]

/-- The requirement, decided. -/
def req (V : Nat → Value) : OItem → Bool
  | selp _ a b p => isPred (V p) && (isRegOrF32 a && isRegOrF32 b)
  | setp c .. => (fcmpBase c).isSome
  | _ => true

/-- The condition under which the instruction accepts its operands. -/
def cond (V : Nat → Value) : OItem → Prop
  | movImm .. => True
  | mov _ a => (V a).bytes = 4
  | pack _ a b => (V a).bytes = 4 ∧ (V b).bytes = 4
  | unpack _ _ a => (V a).bytes = 8 ∧ (splitValue 64 (V a)).1.bytes = 4 ∧
      (splitValue 64 (V a)).2.bytes = 4
  | fma2 _ a b c => ∃ v, fma2E (V a) (V b) (V c) = .ok v
  | add2 _ a b => ∃ v, add2E (V a) (V b) = .ok v
  | ex2 fz _ a => ∃ v, ex2E fz (V a) = .ok v
  | cvt _ a b => ∃ v, cvtPairE (V a) (V b) = .ok v
  | mul fz _ a b => ∃ v, mulE fz (V a) (V b) = .ok v
  | sub fz _ a b => ∃ v, subE fz (V a) (V b) = .ok v
  | add fz _ a b => ∃ v, floatE (addI fz) [V a, V b] = .ok v
  | selp _ a b p => (if predOf (V p) then opndVal V a else opndVal V b).bytes = 4
  | setp c fz _ a k => ∃ r, setpE c fz (V a) (.bits 32 (BitVec.ofNat 64 k)) = .ok r

/-- What the assumptions do with the item's instruction at a state: the ideal (or approximate)
reading of its floating form, with the declines left to the Core rule, or no local rule for a
move or a selection. -/
def Rule (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : OItem → Prop
  | fma2 .. => IdealAt A .fmaRnF32x2 L g t ∧ DeclineAt A .fmaRnF32x2 L g t
  | add2 .. => IdealAt A .addRnF32x2 L g t ∧ DeclineAt A .addRnF32x2 L g t
  | ex2 .. => ApproxAt A (.ex2 .f32) L g t ∧ ApproxDeclineAt A (.ex2 .f32) L g t
  | cvt .. => IdealAt A .cvtRnF16x2F32 L g t ∧ DeclineAt A .cvtRnF16x2F32 L g t
  | mul .. => IdealAt A (.mul .f32) L g t ∧ DeclineAt A (.mul .f32) L g t
  | sub .. => IdealAt A (.subRn .f32) L g t ∧ DeclineAt A (.subRn .f32) L g t
  | add .. => IdealAt A (.add .f32) L g t ∧ DeclineAt A (.add .f32) L g t
  | setp _ _ _ _ k => IdealAt A (setpForm k) L g t ∧ DeclineAt A (setpForm k) L g t
  | movImm d b => ∀ a ∈ A, a.localRule L g t (movImm d b).op = none
  | mov d a => ∀ a' ∈ A, a'.localRule L g t (mov d a).op = none
  | pack d a b => ∀ a' ∈ A, a'.localRule L g t (pack d a b).op = none
  | unpack lo hi a => ∀ a' ∈ A, a'.localRule L g t (unpack lo hi a).op = none
  | selp d a b p => ∀ a' ∈ A, a'.localRule L g t (selp d a b p).op = none

/-- The values after the item. -/
def upd (V : Nat → Value) (it : OItem) : Nat → Value :=
  (it.vals V).foldl (fun (V : Nat → Value) (p : Nat × Value) => Function.update V p.1 p.2) V

/-- The state after the item. -/
def post (V : Nat → Value) (it : OItem) (t : TState) : TState :=
  PTX.next ((it.vals V).foldl (fun t p => setReg t p.1 p.2) t)

/-- The instruction `op` is at `pc` (`i` the code at `pc`). -/
def instrB : Option Instr → Op → Bool
  | some ⟨none, .float f⟩, .float f' => decide (f = f')
  | some ⟨none, .move m⟩, .move m' => decide (m = m')
  | some ⟨none, .int i⟩, .int i' => decide (i = i')
  | some ⟨none, .cvt c⟩, .cvt c' => decide (c = c')
  | _, _ => false

theorem instrB_eq {i : Option Instr} {op : Op} (h : instrB i op = true) :
    i = some ⟨none, op⟩ := by
  unfold instrB at h
  split at h <;> simp_all

/-- The item's instruction is at `pc`. -/
def codeB (K : Kernel) (pc : Nat) (it : OItem) : Bool := instrB K.code[pc]? it.op

theorem code_of {K : Kernel} {pc : Nat} {it : OItem} (h : it.codeB K pc = true) :
    K.code[pc]? = some ⟨none, it.op⟩ :=
  instrB_eq h

/-- The item's instruction is local (no operand is a special register that changes while the
thread runs). -/
def localB (it : OItem) : Bool := it.op.isLocal

theorem vals_keys (V : Nat → Value) (it : OItem) : (it.vals V).map Prod.fst = it.writes := by
  cases it <;> rfl

end OItem

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem fcmpBase_cases {c : FCmp} {cmp : Cmp} (h : fcmpBase c = some cmp) :
    c = .ord cmp ∨ c = .unord cmp := by
  cases c <;> simp_all [fcmpBase]

/-- A step of an outcome `E` writing one register. -/
theorem post_one (V : Nat → Value) (it : OItem) {d : Nat} {E : Exec Value} {dflt : Value}
    {t : TState} (hv : it.vals V = [(d, okVal dflt E)]) :
    (∃ v, E = .ok v) → E.map (fun v => PTX.next (setReg t d v)) = .ok (it.post V t) := by
  rintro ⟨v, hE⟩
  simp [OItem.post, hv, hE, okVal, Except.map]

theorem err_one {E : Exec Value} {F : Value → TState} (h : ¬ ∃ v, E = .ok v) :
    ∃ f, E.map F = .error f := by
  rcases hE : E with f | v
  · exact ⟨f, rfl⟩
  · exact absurd ⟨v, hE⟩ h

/-- **One item**: under its condition the instruction steps to `post`; otherwise it fails. -/
theorem OItem.exec (it : OItem) {V : Nat → Value} {t : TState}
    (hS : SegFreePc A t.pc) (hR : it.Rule A L g t)
    (hr : ∀ r ∈ it.reads, t.regs r = some (V r)) (hq : it.req V = true) :
    (it.cond V → execLocalA A L g t it.op = .ok (it.post V t)) ∧
      (¬ it.cond V → ∃ f, execLocalA A L g t it.op = .error f) := by
  cases it with
  | movImm d b =>
    refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
    simp only [OItem.Rule, OItem.op] at hR
    simp [OItem.op, OItem.post, OItem.vals, hS.exec rfl, execLocalRule_of_none hR,
      execLocal_move (m := ⟨.scalar, .int .b 32, [some d], [.f32imm b]⟩) rfl, execMove,
      DType.width, readValue, readBits, Value.bytes, bind, Except.bind, pure, Except.pure]
  | mov d a =>
    have ha := hr a (by simp [OItem.reads])
    simp only [OItem.Rule, OItem.op] at hR
    have he : execLocalA A L g t (OItem.mov d a).op =
        (if (V a).bytes = 4 then .ok (PTX.next (setReg t d (V a))) else .error .typeMismatch) := by
      simp only [hS.exec rfl, execLocalRule_of_none hR, OItem.op, execLocal, Op.rule,
        MoveInstr.rule, execMove, readValue, readReg]
      by_cases h : (V a).bytes = 4 <;>
        simp [h, ha, DType.width, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [OItem.cond] at h
      rw [he]
      simp [h, OItem.post, OItem.vals]
    · simp only [OItem.cond] at h
      rw [he]
      simp only [h, ↓reduceIte]
      exact ⟨_, rfl⟩
  | pack d a b =>
    have ha := hr a (by simp [OItem.reads])
    have hb := hr b (by simp [OItem.reads])
    simp only [OItem.Rule, OItem.op] at hR
    have he : execLocalA A L g t (OItem.pack d a b).op =
        (if (V a).bytes = 4 ∧ (V b).bytes = 4 then
          .ok (PTX.next (setReg t d (joinValue (V a) (V b)))) else .error .typeMismatch) := by
      simp only [hS.exec rfl, execLocalRule_of_none hR, OItem.op, execLocal, Op.rule,
        MoveInstr.rule, execMove, readValue, readReg]
      by_cases h : (V a).bytes = 4 ∧ (V b).bytes = 4 <;>
        simp [h, ha, hb, DType.width, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [OItem.cond] at h
      rw [he]
      simp [h, OItem.post, OItem.vals]
    · simp only [OItem.cond] at h
      rw [he]
      simp only [h, ↓reduceIte]
      exact ⟨_, rfl⟩
  | unpack lo hi a =>
    have ha := hr a (by simp [OItem.reads])
    have he : execLocalA A L g t (OItem.unpack lo hi a).op =
        (if (V a).bytes = 8 then
          (if (splitValue 64 (V a)).1.bytes = 4 ∧ (splitValue 64 (V a)).2.bytes = 4 then
            .ok (PTX.next (setReg (setReg t lo (splitValue 64 (V a)).1) hi
              (splitValue 64 (V a)).2))
          else .error .typeMismatch)
        else .error .typeMismatch) := by
      simp only [OItem.Rule, OItem.op] at hR
      simp only [OItem.op, hS.exec rfl, execLocalRule_of_none hR,
        execLocal_move (m := ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩) rfl, execMove,
        DType.width, readValue, readReg, ha]
      by_cases h8 : (V a).bytes = 8 <;>
        by_cases h4 : (splitValue 64 (V a)).1.bytes = 4 ∧ (splitValue 64 (V a)).2.bytes = 4 <;>
        simp [h8, h4, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨h8, h4⟩ := h
      rw [he]
      simp [h8, h4, OItem.post, OItem.vals]
    · simp only [OItem.cond] at h
      rw [he]
      by_cases h8 : (V a).bytes = 8
      · simp only [h8, ↓reduceIte, ite_eq_right (fun h4 => h ⟨h8, h4⟩)]
        exact ⟨_, rfl⟩
      · simp only [h8, ↓reduceIte]
        exact ⟨_, rfl⟩
  | fma2 d a b c =>
    have he := exec_fma2E (d := d) hR.1 hR.2 (hr a (by simp [OItem.reads]))
      (hr b (by simp [OItem.reads])) (hr c (by simp [OItem.reads]))
    rw [fma2Op_eq] at he
    exact ⟨fun h => he.trans (post_one V _ rfl h), fun h => he ▸ err_one h⟩
  | add2 d a b =>
    have he := exec_add2E (d := d) hR.1 hR.2 (hr a (by simp [OItem.reads]))
      (hr b (by simp [OItem.reads]))
    exact ⟨fun h => he.trans (post_one V _ rfl h), fun h => he ▸ err_one h⟩
  | ex2 fz d a =>
    have he := exec_ex2E (fz := fz) (d := d) hR.1 hR.2 (OpndIs.reg (hr a (by simp [OItem.reads])))
    exact ⟨fun h => he.trans (post_one V _ rfl h), fun h => he ▸ err_one h⟩
  | cvt d a b =>
    have he := exec_cvtPair_at (d := d) hR.1 hR.2 (hr a (by simp [OItem.reads]))
      (hr b (by simp [OItem.reads]))
    exact ⟨fun h => he.trans (post_one V _ rfl h), fun h => he ▸ err_one h⟩
  | mul fz d a b =>
    have he := exec_mulE (fz := fz) (d := d) hR.1 hR.2
      (OpndIs.reg (hr a (by simp [OItem.reads]))) (OpndIs.reg (hr b (by simp [OItem.reads])))
    exact ⟨fun h => he.trans (post_one V _ rfl h), fun h => he ▸ err_one h⟩
  | sub fz d a b =>
    have he := exec_subE (fz := fz) (d := d) hR.1 hR.2
      (OpndIs.reg (hr a (by simp [OItem.reads]))) (OpndIs.reg (hr b (by simp [OItem.reads])))
    exact ⟨fun h => he.trans (post_one V _ rfl h), fun h => he ▸ err_one h⟩
  | add fz d a b =>
    have he := exec_addE_at (fz := fz) (d := d) hR.1 hR.2
      (OpndIs.reg (hr a (by simp [OItem.reads]))) (OpndIs.reg (hr b (by simp [OItem.reads])))
    exact ⟨fun h => he.trans (post_one V _ rfl h), fun h => he ▸ err_one h⟩
  | selp d a b p =>
    simp only [OItem.req, Bool.and_eq_true] at hq
    obtain ⟨hp, hka, hkb⟩ := hq
    have hpr := hr p (by simp [OItem.reads])
    generalize hv : V p = vp at hpr hp
    cases vp <;> simp only [isPred, Bool.false_eq_true] at hp
    rename_i pick
    have hk : isRegOrF32 (if pick then a else b) = true := by cases pick <;> assumption
    have hsel : readValue L g t 32 (if pick then a else b) =
        .ok (opndVal V (if pick then a else b)) := by
      refine readValue_sel hk fun r hr' => hr r ?_
      cases pick <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr' <;>
        simp [OItem.reads, opndRegs, hr']
    have he : execLocalA A L g t (OItem.selp d a b p).op =
        (if (opndVal V (if pick then a else b)).bytes = 4 then
          .ok (PTX.next (setReg t d (opndVal V (if pick then a else b))))
        else .error .typeMismatch) := by
      simp only [OItem.Rule, OItem.op] at hR
      simp only [OItem.op, hS.exec rfl, execLocalRule_of_none hR,
        execLocal_selp (i := ⟨.selp, .float .f32, false, [some d], [a, b, .reg p]⟩) rfl, execMove,
        DType.width, readReg, hpr]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [hsel]
      by_cases h4 : (opndVal V (if pick then a else b)).bytes = 4 <;>
        simp [h4, throw, throwThe, MonadExceptOf.throw]
    have hsel' : opndVal V (if pick then a else b) =
        if pick then opndVal V a else opndVal V b := by cases pick <;> rfl
    rw [hsel'] at he
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [OItem.cond, hv, predOf] at h
      rw [he]
      simp [h, OItem.post, OItem.vals, hv, predOf]
    · simp only [OItem.cond, hv, predOf] at h
      rw [he]
      simp only [h, ↓reduceIte]
      exact ⟨_, rfl⟩
  | setp c fz p a k =>
    simp only [OItem.req, Option.isSome_iff_exists] at hq
    obtain ⟨cmp, hcmp⟩ := hq
    have hc := fcmpBase_cases hcmp
    have ha := OpndIs.reg (L := L) (g := g) (hr a (by simp [OItem.reads]))
    have hk : OpndIs L g t (.f32imm k) (.bits 32 (BitVec.ofNat 64 k)) := OpndIs.imm
    have he : execLocalA A L g t (OItem.setp c fz p a k).op =
        (setpE c fz (V a) (.bits 32 (BitVec.ofNat 64 k))).map
          fun r => PTX.next (setReg t p (.pred r)) := by
      simp only [OItem.Rule, setpForm] at hR
      simp only [OItem.op]
      by_cases hinf : isInfConst (.f32imm k) = true
      · simp only [hinf, ↓reduceIte] at hR
        exact exec_setpInfE hR.1 hR.2 hc (by simp [hinf]) ha hk
      · simp only [hinf, Bool.false_eq_true, ↓reduceIte] at hR
        exact exec_setpE hR.1 hR.2 hc rfl (by simpa using hinf) ha hk
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨r, hE⟩ := h
      rw [he, hE]
      simp [OItem.post, OItem.vals, hE, okPred, Except.map]
    · rw [he]
      rcases hE : setpE c fz (V a) (.bits 32 (BitVec.ofNat 64 k)) with f | r
      · exact ⟨f, rfl⟩
      · exact absurd ⟨r, hE⟩ h

/-! ### Items with a role's reading -/

/-- An item of a run: an `OItem`, or (`fn`) a local instruction `op` writing `d` from the
registers `srcs` whose outcome on their values the assumptions give as `f`, for a reading the
library has no item for (a kernel's own assumption). -/
inductive XItem where
  | base (it : OItem)
  | fn (op : Op) (d : Nat) (srcs : List Nat) (f : List Value → Exec Value)

namespace XItem

def op : XItem → Op
  | base it => it.op
  | fn op .. => op

def reads : XItem → List Nat
  | base it => it.reads
  | fn _ _ srcs _ => srcs

def writes : XItem → List Nat
  | base it => it.writes
  | fn _ d .. => [d]

def vals (V : Nat → Value) : XItem → List (Nat × Value)
  | base it => it.vals V
  | fn _ d srcs f => [(d, okVal (.bits 32 0) (f (srcs.map V)))]

def req (V : Nat → Value) : XItem → Bool
  | base it => it.req V
  | fn .. => true

def cond (V : Nat → Value) : XItem → Prop
  | base it => it.cond V
  | fn _ _ srcs f => ∃ v, f (srcs.map V) = .ok v

/-- What the assumptions do with the item's instruction at a state: `OItem.Rule`, or for `fn`
the outcome function on any values of its sources. -/
def Rule (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : XItem → Prop
  | base it => it.Rule A L g t
  | fn op d srcs f => ∀ W : Nat → Value, (∀ r ∈ srcs, t.regs r = some (W r)) →
      execLocalA A L g t op = (f (srcs.map W)).map fun v => PTX.next (setReg t d v)

def upd (V : Nat → Value) (it : XItem) : Nat → Value :=
  (it.vals V).foldl (fun (V : Nat → Value) (p : Nat × Value) => Function.update V p.1 p.2) V

def post (V : Nat → Value) (it : XItem) (t : TState) : TState :=
  PTX.next ((it.vals V).foldl (fun t p => setReg t p.1 p.2) t)

def codeB (K : Kernel) (pc : Nat) (it : XItem) : Bool := OItem.instrB K.code[pc]? it.op

def localB (it : XItem) : Bool := it.op.isLocal

theorem vals_keys (V : Nat → Value) (it : XItem) : (it.vals V).map Prod.fst = it.writes := by
  cases it with
  | base it => exact OItem.vals_keys V it
  | fn => rfl

/-- **One item**: under its condition the instruction steps to `post`; otherwise it fails. -/
theorem exec (it : XItem) {V : Nat → Value} {t : TState}
    (hS : SegFreePc A t.pc) (hR : it.Rule A L g t)
    (hr : ∀ r ∈ it.reads, t.regs r = some (V r)) (hq : it.req V = true) :
    (it.cond V → execLocalA A L g t it.op = .ok (it.post V t)) ∧
      (¬ it.cond V → ∃ f, execLocalA A L g t it.op = .error f) := by
  cases it with
  | base it => exact it.exec hS hR hr hq
  | fn op d srcs f =>
    have he := hR V hr
    refine ⟨fun ⟨v, hE⟩ => he.trans ?_, fun h => he ▸ err_one h⟩
    simp [XItem.post, XItem.vals, hE, okVal, Except.map]

/-- **`max.f32` of two sources as a run item** (`fn` with `maxE`): its rule under an ideal
reading of `max.f32` that leaves its declines to the Core rule. -/
theorem max2_rule {t : TState} {d a b : Nat} (hI : IdealAt A (.max .f32) L g t)
    (hD : DeclineAt A (.max .f32) L g t) : (fn (maxOp d [a, b]) d [a, b] maxE).Rule A L g t :=
  fun W hW => exec_maxE2 hI hD (hW a (by simp)) (hW b (by simp))

/-- **`max.f32` of three sources as a run item** (`fn` with `maxE`). -/
theorem max3_rule {t : TState} {d a b c : Nat} (hI : IdealAt A (.max .f32) L g t)
    (hD : DeclineAt A (.max .f32) L g t) :
    (fn (maxOp d [a, b, c]) d [a, b, c] maxE).Rule A L g t :=
  fun W hW => exec_maxE3 hI hD (hW a (by simp)) (hW b (by simp)) (hW c (by simp))

end XItem

/-! ### A run of items -/

/-- The condition of a run: each item's, on the values before it. -/
def oCond (V : Nat → Value) : List OItem → Prop
  | [] => True
  | it :: its => it.cond V ∧ oCond (it.upd V) its

/-- The requirements of a run, decided. -/
def oReq (V : Nat → Value) : List OItem → Bool
  | [] => true
  | it :: its => it.req V && oReq (it.upd V) its

/-- The values after a run. -/
def oFinal (V : Nat → Value) : List OItem → Nat → Value
  | [] => V
  | it :: its => oFinal (it.upd V) its

/-- Each item reads registers of `dom` or written before it. -/
def oReadsB (dom : List Nat) : List OItem → Bool
  | [] => true
  | it :: its => it.reads.all (· ∈ dom) && oReadsB (it.writes ++ dom) its

/-- The items' instructions follow each other from `pc`. -/
def oCodeB (K : Kernel) : Nat → List OItem → Bool
  | _, [] => true
  | pc, it :: its => it.codeB K pc && oCodeB K (pc + 1) its

/-- Every item's instruction is local. -/
def oLocalB : List OItem → Bool
  | [] => true
  | it :: its => it.localB && oLocalB its

/-- The registers a run writes. -/
def oWrites (items : List OItem) : List Nat := items.flatMap OItem.writes

/-- At each item's `pc` no assumption takes a segment, and the assumptions do with the item's
instruction what `OItem.Rule` says. -/
def ORules (A : List Assumption) (L : Launch) (g : Nat) : Nat → List OItem → Prop
  | _, [] => True
  | pc, it :: its => (SegFreePc A pc ∧ ∀ s : TState, s.pc = pc → it.Rule A L g s) ∧
      ORules A L g (pc + 1) its

/-- The condition of a run of `XItem`s. -/
def xCond (V : Nat → Value) : List XItem → Prop
  | [] => True
  | it :: its => it.cond V ∧ xCond (it.upd V) its

def xReq (V : Nat → Value) : List XItem → Bool
  | [] => true
  | it :: its => it.req V && xReq (it.upd V) its

/-- The values after a run of `XItem`s. -/
def xFinal (V : Nat → Value) : List XItem → Nat → Value
  | [] => V
  | it :: its => xFinal (it.upd V) its

def xReadsB (dom : List Nat) : List XItem → Bool
  | [] => true
  | it :: its => it.reads.all (· ∈ dom) && xReadsB (it.writes ++ dom) its

def xCodeB (K : Kernel) : Nat → List XItem → Bool
  | _, [] => true
  | pc, it :: its => it.codeB K pc && xCodeB K (pc + 1) its

def xLocalB : List XItem → Bool
  | [] => true
  | it :: its => it.localB && xLocalB its

def xWrites (items : List XItem) : List Nat := items.flatMap XItem.writes

def XRules (A : List Assumption) (L : Launch) (g : Nat) : Nat → List XItem → Prop
  | _, [] => True
  | pc, it :: its => (SegFreePc A pc ∧ ∀ s : TState, s.pc = pc → it.Rule A L g s) ∧
      XRules A L g (pc + 1) its

/-- **One item**, at the state level: under its condition one local step writes its values
and keeps every register it does not write; otherwise the thread is dead. -/
theorem XItem.step (it : XItem) {V : Nat → Value} {dom : List Nat} {t : TState}
    (hc : it.codeB K t.pc = true) (hf : t.fault = none)
    (hd : ∀ r ∈ dom, t.regs r = some (V r)) (hrd : ∀ r ∈ it.reads, r ∈ dom)
    (hq : it.req V = true) (hl : it.localB = true) (hS : SegFreePc A t.pc)
    (hR : it.Rule A L g t) :
    (it.cond V → run K A L g 1 t = some (it.post V t) ∧ (it.post V t).pc = t.pc + 1 ∧
      (it.post V t).sub = t.sub ∧ (it.post V t).acc = t.acc ∧
      (it.post V t).fault = t.fault ∧
      (∀ r, r ∉ it.writes → (it.post V t).regs r = t.regs r) ∧
      ∀ r ∈ it.writes ++ dom, (it.post V t).regs r = some (it.upd V r)) ∧
    (¬ it.cond V → Machine.Dead (K := K) (A := A) (L := L) (g := g) t) := by
  have hcode := OItem.instrB_eq hc
  have hex := it.exec hS hR (fun r hr => hd r (hrd r hr)) hq
  obtain ⟨h1, h2, h3, h4⟩ := foldl_setReg_skel t (it.vals V)
  have hregs : (it.post V t).regs = (it.vals V).foldl (fun (R : Nat → Option Value)
      (p : Nat × Value) => Function.update R p.1 (some p.2)) t.regs := by
    simp only [XItem.post, PTX.next]
    exact foldl_setReg_regs t (it.vals V)
  refine ⟨fun hc' => ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_⟩, fun hc' => ?_⟩
  · simp only [run, tauStep, tau_of_ok hcode hl hf (hex.1 hc')]
    rfl
  · simp [XItem.post, PTX.next, h1]
  · simp [XItem.post, PTX.next, h2]
  · simp [XItem.post, PTX.next, h3]
  · simp [XItem.post, PTX.next, h4]
  · rw [hregs, foldl_update_other _ (by rw [XItem.vals_keys]; exact hr)]
  · rw [hregs]
    rcases List.mem_append.mp hr with hw | hw
    · exact foldl_update_mem _ (by rw [XItem.vals_keys]; exact hw)
    · exact foldl_update_some _ (hd r hw)
  · obtain ⟨f, he⟩ := hex.2 hc'
    exact dead_of_error hcode hl hf he

/-- **A run of items**: under `xCond` local steps write each register the run writes with its
value after the run and keep every other register; otherwise the thread is dead. -/
theorem xRun : ∀ (items : List XItem) (V : Nat → Value) (dom : List Nat) (t : TState),
    xCodeB K t.pc items = true → t.fault = none → (∀ r ∈ dom, t.regs r = some (V r)) →
    xReadsB dom items = true → xReq V items = true → xLocalB items = true →
    XRules A L g t.pc items →
    (xCond V items → ∃ t', run K A L g items.length t = some t' ∧
      t'.pc = t.pc + items.length ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧ t'.fault = t.fault ∧
      (∀ r, r ∉ xWrites items → t'.regs r = t.regs r) ∧
      ∀ r ∈ xWrites items ++ dom, t'.regs r = some (xFinal V items r)) ∧
    (¬ xCond V items → Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
  | [], V, dom, t, _, _, hd, _, _, _, _ =>
    ⟨fun _ => ⟨t, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun r hr => hd r (by simpa [xWrites] using hr)⟩, fun h => absurd trivial h⟩
  | it :: its, V, dom, t, hc, hf, hd, hrd, hq, hl, hR => by
    simp only [xCodeB, Bool.and_eq_true] at hc
    simp only [xLocalB, Bool.and_eq_true] at hl
    simp only [xReadsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hrd
    simp only [xReq, Bool.and_eq_true] at hq
    simp only [XRules] at hR
    have hst := it.step hc.1 hf hd hrd.1 hq.1 hl.1 hR.1.1 (hR.1.2 t rfl)
    by_cases hok : it.cond V
    · obtain ⟨hr1, hpc1, hsub1, hacc1, hf1, hfr1, hw1⟩ := hst.1 hok
      have ih := xRun its (it.upd V) (it.writes ++ dom) (it.post V t) (by rw [hpc1]; exact hc.2)
        (hf1.trans hf) hw1 hrd.2 hq.2 hl.2 (by rw [hpc1]; exact hR.2)
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨t', hr', hpc', hsub', hacc', hf', hfr', hw'⟩ := ih.1 h.2
        refine ⟨t', ?_, by rw [hpc', hpc1, List.length_cons]; omega, hsub'.trans hsub1,
          hacc'.trans hacc1, hf'.trans hf1, fun r hr => ?_, fun r hr => ?_⟩
        · rw [List.length_cons, Nat.add_comm]
          exact run_comp hr1 hr'
        · simp only [xWrites, List.flatMap_cons, List.mem_append, not_or] at hr
          rw [hfr' r hr.2, hfr1 r hr.1]
        · refine hw' r ?_
          simp only [xWrites, List.flatMap_cons, List.mem_append] at hr ⊢
          tauto
      · exact dead_of_run hr1 (ih.2 fun h' => h ⟨hok, h'⟩)
    · exact ⟨fun h => absurd h.1 hok, fun _ => hst.2 hok⟩

/-- **One item**, at the state level: under its condition one local step writes its values
and keeps every register it does not write; otherwise the thread is dead. -/
theorem OItem.step (it : OItem) {V : Nat → Value} {dom : List Nat} {t : TState}
    (hc : it.codeB K t.pc = true) (hf : t.fault = none)
    (hd : ∀ r ∈ dom, t.regs r = some (V r)) (hrd : ∀ r ∈ it.reads, r ∈ dom)
    (hq : it.req V = true) (hl : it.localB = true) (hS : SegFreePc A t.pc)
    (hR : it.Rule A L g t) :
    (it.cond V → run K A L g 1 t = some (it.post V t) ∧ (it.post V t).pc = t.pc + 1 ∧
      (it.post V t).sub = t.sub ∧ (it.post V t).acc = t.acc ∧
      (it.post V t).fault = t.fault ∧
      (∀ r, r ∉ it.writes → (it.post V t).regs r = t.regs r) ∧
      ∀ r ∈ it.writes ++ dom, (it.post V t).regs r = some (it.upd V r)) ∧
    (¬ it.cond V → Machine.Dead (K := K) (A := A) (L := L) (g := g) t) :=
  XItem.step (.base it) hc hf hd hrd hq hl hS hR

theorem xCodeB_base (K : Kernel) : ∀ (pc : Nat) (items : List OItem),
    xCodeB K pc (items.map .base) = oCodeB K pc items
  | _, [] => rfl
  | pc, it :: its => congrArg (it.codeB K pc && ·) (xCodeB_base K (pc + 1) its)

theorem xReadsB_base : ∀ (dom : List Nat) (items : List OItem),
    xReadsB dom (items.map .base) = oReadsB dom items
  | _, [] => rfl
  | dom, it :: its => congrArg (it.reads.all (· ∈ dom) && ·) (xReadsB_base _ its)

theorem xReq_base : ∀ (V : Nat → Value) (items : List OItem),
    xReq V (items.map .base) = oReq V items
  | _, [] => rfl
  | V, it :: its => congrArg (it.req V && ·) (xReq_base (it.upd V) its)

theorem xLocalB_base : ∀ items : List OItem, xLocalB (items.map .base) = oLocalB items
  | [] => rfl
  | it :: its => congrArg (it.localB && ·) (xLocalB_base its)

theorem xCond_base : ∀ (V : Nat → Value) (items : List OItem),
    xCond V (items.map .base) = oCond V items
  | _, [] => rfl
  | V, it :: its => congrArg (it.cond V ∧ ·) (xCond_base (it.upd V) its)

theorem xFinal_base : ∀ (V : Nat → Value) (items : List OItem),
    xFinal V (items.map .base) = oFinal V items
  | _, [] => rfl
  | V, it :: its => xFinal_base (it.upd V) its

theorem xWrites_base : ∀ items : List OItem, xWrites (items.map .base) = oWrites items
  | [] => rfl
  | it :: its => congrArg (it.writes ++ ·) (xWrites_base its)

theorem xRules_base : ∀ (pc : Nat) (items : List OItem),
    XRules A L g pc (items.map .base) = ORules A L g pc items
  | _, [] => rfl
  | pc, _ :: its => congrArg (_ ∧ ·) (xRules_base (pc + 1) its)

/-- **A run of items**: under `oCond` local steps write each register the run writes with its
value after the run and keep every other register; otherwise the thread is dead. -/
theorem oRun (items : List OItem) (V : Nat → Value) (dom : List Nat) (t : TState)
    (hc : oCodeB K t.pc items = true) (hf : t.fault = none) (hd : ∀ r ∈ dom, t.regs r = some (V r))
    (hrd : oReadsB dom items = true) (hq : oReq V items = true) (hl : oLocalB items = true)
    (hR : ORules A L g t.pc items) :
    (oCond V items → ∃ t', run K A L g items.length t = some t' ∧
      t'.pc = t.pc + items.length ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧ t'.fault = t.fault ∧
      (∀ r, r ∉ oWrites items → t'.regs r = t.regs r) ∧
      ∀ r ∈ oWrites items ++ dom, t'.regs r = some (oFinal V items r)) ∧
    (¬ oCond V items → Machine.Dead (K := K) (A := A) (L := L) (g := g) t) := by
  have h := xRun (K := K) (A := A) (L := L) (g := g) (items.map .base) V dom t
    (by rw [xCodeB_base]; exact hc) hf hd (by rw [xReadsB_base]; exact hrd)
    (by rw [xReq_base]; exact hq) (by rw [xLocalB_base]; exact hl) (by rw [xRules_base]; exact hR)
  rw [xCond_base, xWrites_base, xFinal_base, List.length_map] at h
  exact h

/-- **A run of items, as a piece**: from facts by `V` to facts by the values after the run,
under `xCond`; otherwise the thread is dead. -/
theorem SegD.xouts {pc : Nat} {liveS liveT : List Nat} {V : Nat → Value} {items : List XItem}
    (hcode : xCodeB K pc items = true) (hreads : xReadsB liveS items = true)
    (hreq : xReq V items = true) (hloc : xLocalB items = true) (hR : XRules A L g pc items)
    (hcov : ∀ r ∈ liveT, r ∈ xWrites items ∨ r ∈ liveS) :
    SegD K A L g items.length pc (factsFrom liveS V) (pc + items.length)
      (factsFrom liveT (xFinal V items)) (xCond V items) := by
  intro t h
  have hR' := h.2.2.2.2
  have hrun := xRun items V liveS t (by rw [h.1]; exact hcode) h.2.2.2.1
    (fun r hr => holds_mem hR' (mem_factsFrom hr)) hreads hreq hloc (by rw [h.1]; exact hR)
  refine ⟨fun hc => ?_, hrun.2⟩
  obtain ⟨t', hr, hpc, hsub, hacc, hf, -, hw⟩ := hrun.1 hc
  refine ⟨t', hr, by rw [hpc, h.1], hsub.trans h.2.1, hacc.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_of_pointwise fun r hr' => hw r ?_⟩
  rcases hcov r hr' with h1 | h1
  · exact List.mem_append_left _ h1
  · exact List.mem_append_right _ h1

/-- **A run of `OItem`s, as a piece**: `SegD.xouts` of their `XItem`s. -/
theorem SegD.outs {pc : Nat} {liveS liveT : List Nat} {V : Nat → Value} {items : List OItem}
    (hcode : oCodeB K pc items = true) (hreads : oReadsB liveS items = true)
    (hreq : oReq V items = true) (hloc : oLocalB items = true) (hR : ORules A L g pc items)
    (hcov : ∀ r ∈ liveT, r ∈ oWrites items ∨ r ∈ liveS) :
    SegD K A L g items.length pc (factsFrom liveS V) (pc + items.length)
      (factsFrom liveT (oFinal V items)) (oCond V items) := by
  have h := SegD.xouts (K := K) (A := A) (L := L) (g := g) (pc := pc) (liveS := liveS)
    (liveT := liveT) (V := V) (items := items.map .base) (by rw [xCodeB_base]; exact hcode)
    (by rw [xReadsB_base]; exact hreads) (by rw [xReq_base]; exact hreq)
    (by rw [xLocalB_base]; exact hloc) (by rw [xRules_base]; exact hR)
    (by rw [xWrites_base]; exact hcov)
  rwa [xFinal_base, xCond_base, List.length_map] at h

/-- Facts by value functions that agree on the registers are the same facts. -/
theorem factsFrom_congr {live : List Nat} {V W : Nat → Value}
    (h : live.map V = live.map W) : factsFrom live V = factsFrom live W := by
  unfold factsFrom
  induction live with
  | nil => rfl
  | cons r l ih =>
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨by rw [h.1], ih h.2⟩

/-! ### Runs of unpacks -/

/-- The values a run keeps: a register no item writes keeps its value. -/
theorem upd_other {V : Nat → Value} {it : OItem} {r : Nat} (h : r ∉ it.writes) :
    it.upd V r = V r := by
  unfold OItem.upd
  rw [← OItem.vals_keys V it] at h
  generalize it.vals V = l at h
  induction l generalizing V with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [ih h.2, Function.update_of_ne h.1]

/-- A value that `mov.b64 {lo, hi}, a` accepts. -/
def UnpackOk (v : Value) : Prop :=
  v.bytes = 8 ∧ (splitValue 64 v).1.bytes = 4 ∧ (splitValue 64 v).2.bytes = 4

/-- **A run of unpacks** whose sources no item writes and hold values the unpack accepts meets
its condition. -/
theorem oCond_unpacks {V : Nat → Value} :
    ∀ items : List OItem, (∀ it ∈ items, ∃ lo hi a, it = .unpack lo hi a ∧ a ∉ oWrites items ∧
      UnpackOk (V a)) → oCond V items
  | [], _ => trivial
  | it :: its, h => by
    obtain ⟨lo, hi, a, rfl, ha, hok⟩ := h it (by simp)
    refine ⟨hok, oCond_unpacks its fun it' hit' => ?_⟩
    obtain ⟨lo', hi', a', rfl, ha', hok'⟩ := h it' (by simp [hit'])
    refine ⟨lo', hi', a', rfl, fun hm => ha' ?_, ?_⟩
    · simp only [oWrites, List.flatMap_cons, List.mem_append] at hm ⊢
      exact .inr hm
    · rw [upd_other]
      · exact hok'
      · intro hm
        exact ha' (by simp only [oWrites, List.flatMap_cons, List.mem_append]; exact .inl hm)

/-- A pack of two four-byte values, the first no slice, is accepted by the unpack. -/
theorem unpackOk_join {x y : Value} (hx : x.bytes = 4) (hy : y.bytes = 4)
    (hns : ∀ w o n, x ≠ .slice w o n) : UnpackOk (joinValue x y) := by
  unfold UnpackOk joinValue
  split
  · exact absurd rfl (hns _ _ _)
  · rename_i w x' w' y'
    simp only [Value.bytes] at hx hy
    split_ifs with hw
    · obtain ⟨rfl, hw⟩ := hw
      exact ⟨by simp only [Value.bytes]; omega, rfl, rfl⟩
    · simp only [splitValue, Value.bytes]
      omega
  · simp [splitValue, Value.bytes, hx, hy]

end
end PTX.Flow
