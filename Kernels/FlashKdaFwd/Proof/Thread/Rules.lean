-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Assumptions
public import Lemmas.Flow.CvtBf
public import Lemmas.Flow.EmuStep
public import Lemmas.Flow.OutLit
public import Lemmas.Flow.RcpCore
public import Lemmas.Flow.RunFrame
public import Lemmas.Isa.Rule
public import Kernels.FlashKdaFwd.Proof.Thread.DataLib

@[expose] public section

/-! # How the kernel's assumptions read each local data instruction

The lemmas `Tools/out_gen.py` names in the run declarations of this kernel
(`Kernels/FlashKdaFwd/Gen/Out/runs_*.json`,
written by `Gen/thread.py`), and the outcome functions the generated values are written
with. They are stated for the kernel's whole assumption list `Assumptions.all`.

Only the first four assumptions of the list have a local rule (`idealArith`, `approx`, `narrow`,
`sharedBits`); the others restrict executions (`wf`, `ub`) and cannot change a local step. The
list enters the proofs in three places only, so that appending an assumption without a local rule
changes nothing here: `noSegments` (no assumption takes a segment), `inert_none` (the assumptions
after the fourth have no local rule) and `all_eq` (the list is the four, then those).

The local instruction forms that touch a register holding loaded data, and their reading:

| form | outcome on the values of the sources | rule lemma |
| --- | --- | --- |
| `mul.ftz.f32 d, a, b` | `mulE true va vb` | `rule_mul` |
| `mul.ftz.f32 d, a, 0f…` | `mulKE k [va]` | `rule_mulK` |
| `sub.ftz.f32 d, a, b` | `subE true va vb` | `rule_sub` |
| `add.ftz.f32 d, a, b` | `floatE (addI true) [va, vb]` | `rule_add` |
| `add.ftz.f32 d, a, 0f…` | `addKE k [va]` | `rule_addK` |
| `fma.rn.ftz.f32 d, a, b, c` | `fmaE [va, vb, vc]` | `rule_fma` |
| `ex2.approx.ftz.f32 d, a` | `ex2E true va` | `rule_ex2` |
| `rcp.approx.ftz.f32 d, a` | `rcpFE [va]` | `rule_rcp` |
| `cvt.rn.bf16.f32 d, a` | `narrowE [va]` | `rule_narrow` |
| `mov.b32 d, a` | `va` when it has four bytes | `rule_mov` |
| `mov.b32 d, {lo, hi}` | `pack32E [vlo, vhi]` | `rule_pack32` |
| `mov.b32 {lo, hi}, a` | `unpackE 32 va` | `unpack32_piece` |
| `shl.b32 d, a, n` | `shlKE n [va]` | `rule_shl` |
| `cvt.u32.u16 d, a` | `zext16E [va]` | `rule_zext16` |

Each outcome is an `Exec Value`: the value written, or the fault with which the instruction (and
so the thread) stops. For every outcome function the `_fin` lemma gives its value on operands
that are numbers (`valFloat … = .ok x`), which is what the layer above uses once it knows the
loaded data. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread.Rules
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.FlashKdaFwd

noncomputable section

variable {L : Launch} {g : Nat}

/-! ### The assumption list -/

/-- **No assumption takes a segment.** -/
theorem noSegments : NoSegments Assumptions.all := by
  unfold Assumptions.all
  hooks_off

/-- No assumption takes a segment at any program counter. -/
theorem segFree (pc : Nat) : SegFreePc Assumptions.all pc := noSegments.segFreePc

/-- No assumption takes a segment in a range of program counters. -/
theorem segFree_range (s n : Nat) : ∀ i < n, SegFreePc Assumptions.all (s + i) :=
  fun _ _ => segFree _

/-- The assumptions without a local rule: those after the first four. -/
abbrev inert : List Assumption := Assumptions.all.drop 4

/-- The list is the four assumptions with a local rule, then the others. -/
theorem all_eq : Assumptions.all =
    Assumptions.idealArith :: Assumptions.approx :: Assumptions.narrow ::
      Assumptions.sharedBits :: inert := rfl

/-- **The assumptions after the fourth have no local rule.** -/
theorem inert_none : ∀ a ∈ inert, ∀ (L : Launch) (g : Nat) (t : TState) (op : Op),
    a.localRule L g t op = none := by
  simp only [inert, Assumptions.all, List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  repeat' constructor
  all_goals (intros; rfl)

/-- An operation that none of the four rule-carrying assumptions selects has no local rule in
the list. -/
theorem all_none {t : TState} {op : Op}
    (h1 : Assumptions.idealArith.localRule L g t op = none)
    (h2 : Assumptions.approx.localRule L g t op = none)
    (h3 : Assumptions.narrow.localRule L g t op = none)
    (h4 : Assumptions.sharedBits.localRule L g t op = none) :
    ∀ a ∈ Assumptions.all, a.localRule L g t op = none := by
  intro a ha
  rw [all_eq] at ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | rfl | ha
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact inert_none a ha L g t op

/-- The assumptions after `idealArith` have no local rule for an operation that `approx`,
`narrow` and `sharedBits` do not select. -/
theorem tail_none {t : TState} {op : Op}
    (h2 : Assumptions.approx.localRule L g t op = none)
    (h3 : Assumptions.narrow.localRule L g t op = none)
    (h4 : Assumptions.sharedBits.localRule L g t op = none) :
    ∀ a ∈ Assumptions.all.tail, a.localRule L g t op = none := by
  intro a ha
  rw [all_eq] at ha
  simp only [List.tail_cons, List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · exact h2
  · exact h3
  · exact h4
  · exact inert_none a ha L g t op

/-- The local step of an operation without a local rule in the list is the Core rule's. -/
theorem exec_core {t : TState} {op : Op}
    (h : ∀ a ∈ Assumptions.all, a.localRule L g t op = none) :
    execLocalA Assumptions.all L g t op = execLocal L g t op := by
  rw [noSegments.exec, execLocalRule_of_none h]

/-- The local step where the first assumption with a rule is the `k`-th of the four: stated for
the two cases the kernel has (`approx` and `narrow`), with the assumptions before it silent. -/
theorem exec_at_approx {t : TState} {op : Op}
    (h1 : Assumptions.idealArith.localRule L g t op = none) :
    execLocalA Assumptions.all L g t op =
      match Assumptions.approx.localRule L g t op with
      | some r => r
      | none => execLocalRule Assumptions.all.tail.tail L g t op := by
  rw [noSegments.exec]
  simp only [execLocalRule, all_eq, List.findSome?_cons, h1, List.tail_cons]
  cases Assumptions.approx.localRule L g t op <;> rfl

theorem exec_at_narrow {t : TState} {op : Op}
    (h1 : Assumptions.idealArith.localRule L g t op = none)
    (h2 : Assumptions.approx.localRule L g t op = none)
    (h4 : Assumptions.sharedBits.localRule L g t op = none) :
    execLocalA Assumptions.all L g t op =
      match Assumptions.narrow.localRule L g t op with
      | some r => r
      | none => execLocal L g t op := by
  rw [noSegments.exec]
  have hI : inert.findSome? (fun a => a.localRule L g t op) = none :=
    List.findSome?_eq_none_iff.mpr fun a ha => inert_none a ha L g t op
  simp only [execLocalRule, all_eq, List.findSome?_cons, h1, h2, h4, hI]
  cases Assumptions.narrow.localRule L g t op <;> rfl

/-! ### The ideal reading of `mul`, `sub`, `add` and `fma` -/

/-- The floating forms of the data path that `idealArith` reads. -/
abbrev idealForms : List FloatForm := [.mul .f32, .subRn .f32, .add .f32, .fma .f32]

/-- An operation of one of these forms is a floating instruction. -/
theorem float_of_form {op : Op} {f : FloatForm} (hf : f ∈ idealForms)
    (ho : FloatForm.ofOp op = some f) : ∃ fi, op = .float fi := by
  cases op with
  | float fi => exact ⟨fi, rfl⟩
  | cvt c =>
    simp only [FloatForm.ofOp] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> split_ifs at ho <;> cases ho
  | _ => cases ho

/-- **The scalar FP32 arithmetic is exact real arithmetic** at every state, and where the ideal
rule declines (a NaN operand, `∞ - ∞`, `0 · ∞`) the Core rule applies. -/
theorem forms {t : TState} {f : FloatForm} (hf : f ∈ idealForms) :
    IdealAt Assumptions.all f L g t ∧ DeclineAt Assumptions.all f L g t := by
  have hS : SegFreePc Assumptions.all.tail t.pc := (noSegments.tail).segFreePc
  show IdealAt (Assumptions.idealArith :: Assumptions.all.tail) f L g t ∧
    DeclineAt (Assumptions.idealArith :: Assumptions.all.tail) f L g t
  unfold Assumptions.idealArith
  refine ⟨idealAt_head ?_ hS, declineAt_head (fun a ha op ho => ?_) hS⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf ⊢
    tauto
  obtain ⟨fi, rfl⟩ := float_of_form hf ho
  refine tail_none (approxExact_localRule_none fun x hx => ?_) rfl rfl a ha
  rw [approxForm_none_of_float ho] at hx
  cases hx

/-- The ideal reading at a state at `pc` (the form `out_gen.py` asks for). -/
theorem rule_mul {fz : Bool} {d a b : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.base (.mul fz d a b)).Rule Assumptions.all L g s :=
  fun _ _ => forms (by simp)

theorem rule_sub {fz : Bool} {d a b : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.base (.sub fz d a b)).Rule Assumptions.all L g s :=
  fun _ _ => forms (by simp)

theorem rule_add {fz : Bool} {d a b : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.base (.add fz d a b)).Rule Assumptions.all L g s :=
  fun _ _ => forms (by simp)

/-! #### An immediate second operand -/

/-- The value of a `0f…` constant with the bits `k`. -/
abbrev immV (k : Nat) : Value := .bits 32 (BitVec.ofNat 64 k)

/-- `mul.ftz.f32 d, a, 0f…`. -/
def mulKOp (k : Nat) (d : Nat) (s : List Nat) : Op :=
  .float { mulI true with dsts := [some d], srcs := [.reg (s.getD 0 0), .f32imm k] }

/-- The outcome of `mul.ftz.f32 d, a, 0f…` on the value of `a`. -/
def mulKE (k : Nat) : List Value → Exec Value
  | [va] => mulE true va (immV k)
  | _ => .error .typeMismatch

theorem rule_mulK {k d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (mulKOp k d [a]) d [a] (mulKE k)).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  exact exec_mulE (fz := true) (d := d) (forms (by simp)).1 (forms (by simp)).2
    (OpndIs.reg (hW a (by simp))) OpndIs.imm

/-- `add.ftz.f32 d, a, 0f…`. -/
def addKOp (k : Nat) (d : Nat) (s : List Nat) : Op :=
  .float { addI true with dsts := [some d], srcs := [.reg (s.getD 0 0), .f32imm k] }

/-- The outcome of `add.ftz.f32 d, a, 0f…` on the value of `a`. -/
def addKE (k : Nat) : List Value → Exec Value
  | [va] => floatE (addI true) [va, immV k]
  | _ => .error .typeMismatch

theorem rule_addK {k d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (addKOp k d [a]) d [a] (addKE k)).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  exact exec_addE_at (fz := true) (d := d) (forms (by simp)).1 (forms (by simp)).2
    (OpndIs.reg (hW a (by simp))) OpndIs.imm

/-! #### The scalar fused multiply-add -/

/-- `fma.rn.ftz.f32 d, a, b, c`. -/
def fmaOp (d : Nat) (s : List Nat) : Op :=
  .float { fmaI .rn true with
    dsts := [some d], srcs := [.reg (s.getD 0 0), .reg (s.getD 1 0), .reg (s.getD 2 0)] }

/-- The outcome of `fma.rn.ftz.f32 d, a, b, c` on the values of its sources. -/
def fmaE : List Value → Exec Value
  | [va, vb, vc] => floatE (fmaI .rn true) [va, vb, vc]
  | _ => .error .typeMismatch

theorem rule_fma {d a b c : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (fmaOp d [a, b, c]) d [a, b, c] fmaE).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  exact exec_floatE_fma_at (rnd := .rn) (fz := true) (d := d) (forms (by simp)).1
    (forms (by simp)).2 (OpndIs.reg (hW a (by simp))) (OpndIs.reg (hW b (by simp)))
    (OpndIs.reg (hW c (by simp)))

/-! ### The exact reading of `ex2.approx` and `rcp.approx` -/

/-- The approximate forms of the data path. -/
abbrev approxForms : List ApproxForm := [.ex2 .f32, .rcp .f32]

/-- **`ex2.approx.f32` and `rcp.approx.f32` are their exact functions** on a finite operand, and
an infinite or NaN operand is left to the Core rule (the table of special values). -/
theorem approxRule {t : TState} {f : ApproxForm} (hf : f ∈ approxForms) :
    ApproxAt Assumptions.all f L g t ∧ ApproxDeclineAt Assumptions.all f L g t := by
  have key (op : Op) (ho : ApproxForm.ofOp op = some f) :
      execLocalA Assumptions.all L g t op =
        (execApproxExact t op).getD (execLocal L g t op) := by
    have hi : Assumptions.idealArith.localRule L g t op = none :=
      idealReal_localRule_none fun f' hf' => by
        rw [floatForm_none_of_approx ho] at hf'; cases hf'
    have ha : Assumptions.approx.localRule L g t op = execApproxExact t op :=
      approxExact_localRule_of ho hf
    have hfl : ∃ fi, op = .float fi := by
      cases op with
      | float fi => exact ⟨fi, rfl⟩
      | _ => cases ho
    obtain ⟨fi, rfl⟩ := hfl
    rw [exec_at_approx hi, ha]
    cases execApproxExact t (.float fi) with
    | some r => rfl
    | none =>
      show execLocalRule Assumptions.all.tail.tail L g t (.float fi) = _
      refine execLocalRule_of_none fun a ha' => ?_
      rw [all_eq] at ha'
      simp only [List.tail_cons, List.mem_cons] at ha'
      rcases ha' with rfl | rfl | ha'
      · rfl
      · rfl
      · exact inert_none a ha' L g t _
  exact ⟨fun op ho e he => by rw [key op ho, he]; rfl,
    fun op ho he => by rw [key op ho, he]; rfl⟩

theorem rule_ex2 {fz : Bool} {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.base (.ex2 fz d a)).Rule Assumptions.all L g s :=
  fun _ _ => approxRule (by simp)

/-- `rcp.approx.ftz.f32 d, a`. -/
def rcpOp (d : Nat) (s : List Nat) : Op :=
  .float { rcpI true with dsts := [some d], srcs := [.reg (s.getD 0 0)] }

/-- The outcome of `rcp.approx.ftz.f32 d, a` on the value of `a`. -/
def rcpFE : List Value → Exec Value
  | [va] => rcpE true va
  | _ => .error .typeMismatch

theorem rule_rcp {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (rcpOp d [a]) d [a] rcpFE).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  exact exec_rcpE (fz := true) (d := d) (approxRule (by simp)).1 (approxRule (by simp)).2
    (OpndIs.reg (hW a (by simp)))

/-! ### Moves -/

/-- **No assumption has a local rule for a move**: the Core rule applies. -/
theorem moveNone (t : TState) (m : MoveInstr) :
    ∀ a ∈ Assumptions.all, a.localRule L g t (.move m) = none :=
  all_none rfl rfl rfl rfl

theorem coreMoves : CoreMoves Assumptions.all := fun m _ _ t => moveNone t m

theorem rule_mov {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.base (.mov d a)).Rule Assumptions.all L g s :=
  fun s _ => moveNone s _

/-- `mov.b32 d, {lo, hi}`. -/
def pack32Op (d : Nat) (s : List Nat) : Op :=
  .move ⟨.pack, .int .b 32, [some d], [.reg (s.getD 0 0), .reg (s.getD 1 0)]⟩

/-- The outcome of `mov.b32 d, {lo, hi}` on the values of `lo` and `hi`: their pair, when both
have two bytes. -/
def pack32E : List Value → Exec Value
  | [va, vb] => if va.bytes = 2 ∧ vb.bytes = 2 then .ok (joinValue va vb) else .error .typeMismatch
  | _ => .error .typeMismatch

theorem rule_pack32 {d a b : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (pack32Op d [a, b]) d [a, b] pack32E).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  have ha := hW a (by simp)
  have hb := hW b (by simp)
  show execLocalA Assumptions.all L g t
      (.move ⟨.pack, .int .b 32, [some d], [.reg a, .reg b]⟩) = _
  rw [exec_core (moveNone t _)]
  by_cases h2 : (W a).bytes = 2 ∧ (W b).bytes = 2 <;>
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, ha, hb,
      h2, pack32E, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]

/-- The local step of `mov.b32 {lo, hi}, a`: the two halves of the value of `a`, when it has
four bytes and its halves two each. -/
theorem exec_unpack32 {t : TState} {lo hi a : Nat} {v : Value} (h : t.regs a = some v) :
    execLocalA Assumptions.all L g t (.move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg a]⟩) =
      (unpackE 32 v).map fun x => PTX.next (setReg (setReg t lo x.1) hi x.2) :=
  exec_unpackE coreMoves noSegments (.inl rfl) h

/-! ### Integer instructions on data -/

/-- `shl.b32 d, a, n`. -/
def shlOp (n : Int) (d : Nat) (s : List Nat) : Op :=
  .int ⟨.shl, .int .b 32, false, [some d], [.reg (s.getD 0 0), .imm n]⟩

/-- The outcome of `shl.b32 d, a, n` on the value of `a`: its bit pattern shifted, a fault for a
value without one. -/
def shlKE (n : Int) : List Value → Exec Value
  | [va] => shlE va n
  | _ => .error .typeMismatch

theorem rule_shl {n : Int} {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (shlOp n d [a]) d [a] (shlKE n)).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  have ha := hW a (by simp)
  show execLocalA Assumptions.all L g t
      (.int ⟨.shl, .int .b 32, false, [some d], [.reg a, .imm n]⟩) = _
  rw [exec_core (all_none rfl rfl rfl rfl), execLocal_int (by rfl)]
  exact execInt_shl_imm rfl ha

/-- `cvt.u32.u16 d, a`. -/
def zext16Op (d : Nat) (s : List Nat) : Op :=
  .cvt { dst := .int .u 32, src := .int .u 16, d := d, srcs := [.reg (s.getD 0 0)] }

/-- The outcome of `cvt.u32.u16 d, a` on the value of `a`: the low 16 bits of its bit pattern as
a 32-bit word; a 16-bit shared or parameter pointer that is not generic keeps its tag; every
other pointer and a value without a bit pattern fault. -/
def zext16E : List Value → Exec Value
  | [.ptr w generic sp off] =>
    if w = 16 ∧ generic = false then .ok (.ptr 32 generic sp off) else .error .noRule
  | [va] => (readBitsOf 16 va).map fun x => .bits 32 (truncBits 32 x)
  | _ => .error .typeMismatch

theorem rule_zext16 {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (zext16Op d [a]) d [a] zext16E).Rule
      Assumptions.all L g s := by
  intro t _ W hW
  have ha := hW a (by simp)
  show execLocalA Assumptions.all L g t
      (.cvt { dst := .int .u 32, src := .int .u 16, d := d, srcs := [.reg a] }) = _
  rw [exec_core (all_none rfl rfl rfl rfl), execLocal_cvt (by rfl)]
  simp only [execCvt, readValue, readReg, ha, bind, Except.bind, pure, Except.pure,
    List.map_cons, List.map_nil]
  cases hv : W a with
  | ptr w generic sp off =>
    by_cases hc : w = 16 ∧ generic = false
    · obtain ⟨rfl, rfl⟩ := hc
      simp [zext16E, Except.map]
    · simp only [zext16E, hc, ↓reduceIte, Except.map]
      rw [ite_eq_right]
      · rfl
      · rintro ⟨-, -, -, -, rfl, h | ⟨rfl, -, -⟩⟩
        · omega
        · exact hc ⟨rfl, rfl⟩
  | _ =>
    simp only [zext16E, readBits_reg_bitsOf ha, hv]
    generalize readBitsOf 16 _ = e
    rcases e with e | x <;> rfl

/-! ### The kernel rule `narrow`: `cvt.rn.bf16.f32` -/

/-- `cvt.rn.bf16.f32 d, a`. -/
abbrev narrowC (d a : Nat) : CvtInstr :=
  { dst := .float .bf16, src := .float .f32, rnd := some .rn, d := d, srcs := [.reg a] }

/-- `cvt.rn.bf16.f32 d, a`, as a run item's instruction. -/
def narrowOp (d : Nat) (s : List Nat) : Op := .cvt (narrowC d (s.getD 0 0))

/-- The value the Core rule (THREAD-CVT) writes for `cvt.rn.bf16.f32` of a register that holds
`v`: its `.f32` datum rounded to the nearest `.bf16`. -/
def coreNarrow (v : Value) : Exec Value :=
  (if 4 < v.bytes then lowValue 4 v >>= classify .f32 else classify .f32 v) >>= fun x =>
    cvtNum (narrowC 0 0) .bf16 FloatFmt.bf16.layout .rn false 1 x >>= fun y =>
      pure (y.toValue .bf16)

theorem execLocal_narrow_core {t : TState} {d a : Nat} {v : Value} (h : t.regs a = some v) :
    execLocal L g t (.cvt (narrowC d a)) =
      (coreNarrow v).map fun w => PTX.next (setReg t d w) := by
  have hc : cvtNum (narrowC d a) = cvtNum (narrowC 0 0) := rfl
  have hr : (Op.cvt (narrowC d a)).rule = some .threadCvt := rfl
  simp only [execLocal, hr]
  simp [execCvt, readCvtFloat, readReg, h, FType.fmt?, CvtRnd.mode?, hc, coreNarrow, bind,
    Except.bind, Except.map, pure, Except.pure]
  rw [show FloatFmt.f32.bytes = 4 from rfl]
  split_ifs
  · cases lowValue 4 v with
    | error e => rfl
    | ok w =>
      dsimp only
      cases classify .f32 w with
      | error e => rfl
      | ok x =>
        dsimp only
        cases cvtNum (narrowC 0 0) .bf16 FloatFmt.bf16.layout .rn false 1 x <;> rfl
  · cases classify .f32 v with
    | error e => rfl
    | ok x =>
      dsimp only
      cases cvtNum (narrowC 0 0) .bf16 FloatFmt.bf16.layout .rn false 1 x <;> rfl

/-- **The outcome of `cvt.rn.bf16.f32`** on the value `v` of its operand, under the kernel rule
`narrow`: a finite operand is the `bf16` payload of the same real (no rounding); an operand the
rule cannot read as `.f32` (another width, no bit pattern) is that read's fault; an infinite or
NaN operand makes the rule decline, and the Core conversion gives the result (`coreNarrow`). -/
def narrowV (v : Value) : Exec Value :=
  match finiteVal v with
  | some (.ok x) => .ok (.float .bf16 x)
  | some (.error e) => .error e
  | none => coreNarrow v

/-- `narrowV` as a run item's outcome function. -/
def narrowE : List Value → Exec Value
  | [va] => narrowV va
  | _ => .error .typeMismatch

/-- The rule `narrow` at `cvt.rn.bf16.f32 d, a` on the value of `a`. -/
theorem narrow_localRule {t : TState} {d a : Nat} {v : Value} (h : t.regs a = some v) :
    Assumptions.narrow.localRule L g t (.cvt (narrowC d a)) =
      bindRead (finiteVal v) fun x => some (pure (next (setReg t d (.float .bf16 x)))) := by
  simp [Assumptions.narrow, Assumptions.narrowOperands, CvtInstr.plain,
    readFinite_of (readERealOpnd_reg h), bind, Option.bind]

/-- **The local step of `cvt.rn.bf16.f32 d, a`** writes the outcome `narrowV` of the value of
`a` or faults. -/
theorem exec_narrow {t : TState} {d a : Nat} {v : Value} (h : t.regs a = some v) :
    execLocalA Assumptions.all L g t (.cvt (narrowC d a)) =
      (narrowV v).map fun w => PTX.next (setReg t d w) := by
  rw [exec_at_narrow rfl rfl rfl, narrow_localRule h]
  unfold narrowV
  rcases finiteVal v with _ | (e | x)
  · exact execLocal_narrow_core h
  · rfl
  · rfl

theorem rule_narrow {d a : Nat} (pc : Nat) :
    ∀ s : TState, s.pc = pc → (XItem.fn (narrowOp d [a]) d [a] narrowE).Rule
      Assumptions.all L g s :=
  fun _ _ W hW => exec_narrow (hW a (by simp))

/-- **A finite operand narrows to the payload of the same real.** -/
theorem narrowV_fin {v : Value} {x : ℝ} (hx : valFloat .f32 v = .ok x) :
    narrowV v = .ok (.float .bf16 x) := by
  simp only [narrowV, finiteVal_of hx]

theorem narrowE_fin {v : Value} {x : ℝ} (hx : valFloat .f32 v = .ok x) :
    narrowE [v] = .ok (.float .bf16 x) := narrowV_fin hx

/-- An operand that the rule cannot read as `.f32` faults with that read's fault. -/
theorem narrowV_error {v : Value} {e : Fault} (h : finiteVal v = some (.error e)) :
    narrowV v = .error e := by
  simp only [narrowV, h]

/-- Where the rule declines (an infinite or NaN operand), the outcome is the Core rule's. -/
theorem narrowV_decline {v : Value} (h : finiteVal v = none) : narrowV v = coreNarrow v := by
  simp only [narrowV, h]

/-- **The Core rule has no value for an infinite operand** (`cvt` to `.bf16` without
`.satfinite`): the thread faults. -/
theorem coreNarrow_inf {v : Value} {neg : Bool} (hb : ¬ 4 < v.bytes)
    (h : classify .f32 v = .ok (.inf neg)) : coreNarrow v = .error .noRule := by
  simp [coreNarrow, hb, h, cvtNum, cvtSpecial, bind, Except.bind]
  rfl

/-- **The Core rule converts a NaN operand to the opaque `bf16` NaN**: the thread continues. -/
theorem coreNarrow_nan {v : Value} {p : Option Nat} (hb : ¬ 4 < v.bytes)
    (h : classify .f32 v = .ok (.nan p)) : coreNarrow v = .ok (.nan .bf16) := by
  simp [coreNarrow, hb, h, cvtNum, cvtSpecial, cvtFinish, FloatFmt.layout, bind, Except.bind,
    pure, Except.pure]
  rfl

/-- A value that is no `.f32` payload and whose datum is an infinity is declined by the rule. -/
theorem finiteVal_inf {v : Value} {neg : Bool} (hv : ∀ x, v ≠ .float .f32 x)
    (h : classify .f32 v = .ok (.inf neg)) : finiteVal v = none := by
  have hr : readEReal .f32 v = some (pure (if neg then ⊥ else ⊤)) := by
    cases v with
    | float f x =>
      by_cases hf : f = .f32
      · subst hf; exact absurd rfl (hv x)
      · simp only [readEReal, hf, ↓reduceIte, h, readEReal.ofDatum]
    | _ => simp only [readEReal, h, readEReal.ofDatum]
  simp only [finiteVal, hr, bindRead, pure, Except.pure]
  cases neg <;> simp

/-- A value whose datum is a NaN is declined by the rule. -/
theorem finiteVal_nan {v : Value} {p : Option Nat} (hv : ∀ x, v ≠ .float .f32 x)
    (h : classify .f32 v = .ok (.nan p)) : finiteVal v = none := by
  have hr : readEReal .f32 v = none := by
    cases v with
    | float f x =>
      by_cases hf : f = .f32
      · subst hf; exact absurd rfl (hv x)
      · simp only [readEReal, hf, ↓reduceIte, h, readEReal.ofDatum]
    | _ => simp only [readEReal, h, readEReal.ofDatum]
  simp only [finiteVal, hr, bindRead]

/-- **An infinite operand kills the thread** at `cvt.rn.bf16.f32`. -/
theorem narrowV_inf {v : Value} {neg : Bool} (hv : ∀ x, v ≠ .float .f32 x)
    (hb : ¬ 4 < v.bytes) (h : classify .f32 v = .ok (.inf neg)) :
    narrowV v = .error .noRule := by
  rw [narrowV_decline (finiteVal_inf hv h), coreNarrow_inf hb h]

/-- **A NaN operand narrows to the opaque `bf16` NaN.** -/
theorem narrowV_nan {v : Value} {p : Option Nat} (hv : ∀ x, v ≠ .float .f32 x)
    (hb : ¬ 4 < v.bytes) (h : classify .f32 v = .ok (.nan p)) :
    narrowV v = .ok (.nan .bf16) := by
  rw [narrowV_decline (finiteVal_nan hv h), coreNarrow_nan hb h]

/-- **Every value of a narrowing has two bytes** (so a pack of two narrowed values is
accepted). -/
theorem narrowV_bytes {v w : Value} (h : narrowV v = .ok w) : w.bytes = 2 := by
  unfold narrowV at h
  split at h
  · cases h; rfl
  · cases h
  · unfold coreNarrow at h
    obtain ⟨x, -, h⟩ := exec_bind_ok h
    obtain ⟨y, -, h⟩ := exec_bind_ok h
    cases h
    exact toValue_bf16_bytes _

/-! ### Unpacks -/

/-- **`mov.b32 {lo, hi}, a` as a piece checked against stated values** (the form
`Tools/out_gen.py` writes for the kind `unpack32`). -/
theorem unpack32_piece {K : Kernel} {pc lo hi a : Nat} {F G : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg a]⟩⟩)
    (ha : (F.map Prod.fst).contains a = true) (hne : (lo != hi) = true)
    (hcov : (G.map Prod.fst).all (fun r => r == lo || r == hi ||
      (F.map Prod.fst).contains r) = true)
    (hG : factsFrom (G.map Prod.fst) (valueEx (lookupD F)
      [(hi, (splitValue 32 (lookupD F a)).2), (lo, (splitValue 32 (lookupD F a)).1)]) = G) :
    SegD K Assumptions.all L g 1 pc F (pc + 1) G (∃ x, unpackE 32 (lookupD F a) = .ok x) :=
  unpack_piece coreMoves noSegments (.inl rfl) hc ha hne hcov hG

/-- A pair of two-byte halves unpacks into its halves. -/
theorem unpackE32_pair {a b : Value} (ha : a.bytes = 2) (hb : b.bytes = 2) :
    unpackE 32 (.pair a b) = .ok (a, b) := by
  simp [unpackE, splitValue, Value.bytes, ha, hb]

/-- A 32-bit word unpacks into its two 16-bit halves. -/
theorem unpackE32_bits (x : BitVec 64) :
    unpackE 32 (.bits 32 x) = .ok (.bits 16 (truncBits 16 x),
      .bits 16 (truncBits 16 (BitVec.ofNat 64 (x.toNat / 2 ^ 16)))) := by
  simp [unpackE, splitValue, Value.bytes]

/-! ### The outcomes on numbers and words -/

/-- **A product with a constant**, of numbers, is the exact product. -/
theorem mulKE_fin {k : Nat} {va : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hk : valFloat .f32 (immV k) = .ok y) : mulKE k [va] = .ok (.float .f32 (x * y)) :=
  mulE_fin hx hk

/-- **A sum with a constant**, of numbers, is the exact sum. -/
theorem addKE_fin {k : Nat} {va : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hk : valFloat .f32 (immV k) = .ok y) : addKE k [va] = .ok (.float .f32 (x + y)) :=
  floatE_add_fin hx hk

/-- **A fused multiply-add of numbers** is the exact `x * y + z`. -/
theorem fmaE_fin {va vb vc : Value} {x y z : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) (hz : valFloat .f32 vc = .ok z) :
    fmaE [va, vb, vc] = .ok (.float .f32 (x * y + z)) :=
  floatE_fma_fin hx hy hz

/-- **The reciprocal of a nonzero number** is the exact one. -/
theorem rcpFE_fin {va : Value} {x : ℝ} (hx : valFloat .f32 va = .ok x) (h0 : x ≠ 0) :
    rcpFE [va] = .ok (.float .f32 (1 / x)) :=
  rcpE_fin hx h0

/-- **The reciprocal of zero faults** (`badValue`): the thread is dead. -/
theorem rcpFE_zero {va : Value} (hx : valFloat .f32 va = .ok 0) :
    rcpFE [va] = .error .badValue := by
  simp [rcpFE, rcpE, rcpVal, finiteVal_of hx, bindRead, throw, throwThe, MonadExceptOf.throw]

/-- A pack of two two-byte values is their pair. -/
theorem pack32E_ok {va vb : Value} (ha : va.bytes = 2) (hb : vb.bytes = 2) :
    pack32E [va, vb] = .ok (joinValue va vb) := by
  simp [pack32E, ha, hb]

/-- A pack of two `bf16` payloads is the pair of the payloads. -/
theorem pack32E_bf16 (x y : ℝ) :
    pack32E [.float .bf16 x, .float .bf16 y] = .ok (.pair (.float .bf16 x) (.float .bf16 y)) := by
  rw [pack32E_ok rfl rfl]; rfl

/-- The shift by 16 of a word (the bits of a `bf16` moved to the high half of an `f32`). -/
theorem shlKE_16_bits {w : Nat} (x : BitVec 64) :
    shlKE 16 [.bits w x] = .ok (.bits 32 (truncBits 32 (truncBits 32 x <<< 16))) := rfl

/-- The zero-extension of a word is the word of its low 16 bits. -/
theorem zext16E_bits {w : Nat} (x : BitVec 64) :
    zext16E [.bits w x] = .ok (.bits 32 (truncBits 32 (truncBits 16 x))) := rfl

/-! ### The local rules write only their instruction's registers -/

theorem frame_next_setReg {op : Op} {t : TState} {d : Nat} {v : Value}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    LocalFrame op t (next (setReg t d v)) :=
  ⟨.inl hpc.symm, rfl, rfl, rfl, fun r hr =>
    Function.update_of_ne (fun e => hr (by subst e; exact hd)) _ _⟩

theorem narrow_frame {t t' : TState} {op : Op}
    (h : Assumptions.narrow.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.narrow] at h
  cases hop : Assumptions.narrowOperands op with
  | none => simp [hop, bind, Option.bind] at h
  | some p =>
    obtain ⟨d, a⟩ := p
    have hc : ∃ c, op = .cvt c ∧ c.d = d := by
      unfold Assumptions.narrowOperands at hop
      split at hop
      · rename_i c
        split at hop
        · split_ifs at hop
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          exact ⟨c, rfl, hop.1⟩
        · cases hop
      · cases hop
    obtain ⟨c, rfl, rfl⟩ := hc
    simp only [hop, bind, Option.bind] at h
    obtain ⟨x, -, hx⟩ := bindRead_ok h
    simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hx
    subst hx
    exact frame_next_setReg rfl (by simp [writesRegs])

theorem sharedBits_frame {t t' : TState} {op : Op}
    (h : Assumptions.sharedBits.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  change Assumptions.sharedBitsRule t op = some (.ok t') at h
  unfold Assumptions.sharedBitsRule at h
  split at h
  · rename_i d r hsh
    have hop : op = .int ⟨.shr, .int .u 64, false, [some d], [.reg r, .imm 3]⟩ := by
      unfold Assumptions.swizzleShift at hsh
      split at hsh
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsh
        obtain ⟨rfl, rfl⟩ := hsh
        rfl
      · cases hsh
    subst hop
    split at h
    · simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact frame_next_setReg rfl (by simp [writesRegs])
    · cases h
  · split at h
    · rename_i d m r hx
      have hop : op = .int ⟨.xor, .int .b 64, false, [some d], [.reg m, .reg r]⟩ := by
        unfold Assumptions.swizzleXor at hx
        split at hx
        · simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl, rfl⟩ := hx
          rfl
        · cases hx
      subst hop
      split at h
      · split_ifs at h
        simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact frame_next_setReg rfl (by simp [writesRegs])
      · cases h
    · cases h

/-- **Every local rule of the kernel's assumptions writes only its instruction's registers**
(what `SegD.frame` needs to carry facts over a run). -/
theorem rulesFrame : RulesFrame Assumptions.all := by
  intro a ha
  rw [all_eq] at ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | rfl | ha
  · exact fun _ _ _ _ _ => idealReal_frame
  · exact fun _ _ _ _ _ => approxExact_frame
  · exact fun _ _ _ _ _ => narrow_frame
  · exact fun _ _ _ _ _ => sharedBits_frame
  · intro L g t op t' h
    rw [inert_none a ha L g t op] at h
    cases h

end
end PTX.Kernels.FlashKdaFwd.Proof.Thread.Rules
