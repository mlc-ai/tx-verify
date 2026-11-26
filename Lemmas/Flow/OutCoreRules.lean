-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutCore

@[expose] public section

/-! # The rule lemmas of Core's forms as run items

`XItem.core_<form>` for the forms of `Lemmas/Flow/OutCore.lean`: at a pc where no assumption
takes a segment and none has a local rule for the instruction, and the form's Boolean checks hold
(by `rfl` on the literal instruction), the `fn` item `coreF` reads Core's value. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

section
variable {A : List Assumption} {L : Launch} {g : Nat}

/-- `setp.<cmp>` without a combining predicate. -/
theorem XItem.core_setp {pc d : Nat} {cmp : Cmp} {ty : DType} {sat : Bool} {a b : Opnd}
    (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.setp cmp none, ty, sat, [some d], [a, b]⟩))
    (hc : Ok2 (.int ⟨.setp cmp none, ty, sat, [some d], [a, b]⟩) .threadInt a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.setp cmp none, ty, sat, [some d], [a, b]⟩) d
      (regsOf [a, b]) (coreF (.int ⟨.setp cmp none, ty, sat, [some d], [a, b]⟩)
        (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  simp only [execLocal, hr, execInt, coreW, readBits_oBits ha (reg_of_mem (by simp) hW),
    readBits_oBits hb (reg_of_mem (by simp) hW)]
  cases oBits W ty.width a <;> cases oBits W ty.width b <;> rfl

/-- `add` of a scalar integer type. -/
theorem XItem.core_add {pc d w : Nat} {k : IType} {a b : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.add, .int k w, false, [some d], [a, b]⟩))
    (hc : Ok2 (.int ⟨.add, .int k w, false, [some d], [a, b]⟩) .threadInt a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.add, .int k w, false, [some d], [a, b]⟩) d
      (regsOf [a, b]) (coreF (.int ⟨.add, .int k w, false, [some d], [a, b]⟩)
        (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  have hWa := reg_of_mem (by simp) hW (o := a)
  have hWb := reg_of_mem (by simp) hW (o := b)
  simp only [execLocal, hr, execInt, coreW, addW, readValue_oVal ha hWa, readValue_oVal hb hWb,
    readBits_oBits ha hWa, readBits_oBits hb hWb]
  cases oVal W (DType.int k w).width a <;> cases oVal W (DType.int k w).width b <;>
    cases oBits W (DType.int k w).width a <;> cases oBits W (DType.int k w).width b <;> core_close

/-- `sub` of a scalar integer type. -/
theorem XItem.core_sub {pc d w : Nat} {k : IType} {a b : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.sub, .int k w, false, [some d], [a, b]⟩))
    (hc : Ok2 (.int ⟨.sub, .int k w, false, [some d], [a, b]⟩) .threadInt a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.sub, .int k w, false, [some d], [a, b]⟩) d
      (regsOf [a, b]) (coreF (.int ⟨.sub, .int k w, false, [some d], [a, b]⟩)
        (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  have hWa := reg_of_mem (by simp) hW (o := a)
  have hWb := reg_of_mem (by simp) hW (o := b)
  simp only [execLocal, hr, execInt, coreW, subW, readValue_oVal ha hWa,
    readBits_oBits ha hWa, readBits_oBits hb hWb]
  cases oVal W (DType.int k w).width a <;> cases oBits W (DType.int k w).width a <;>
    cases oBits W (DType.int k w).width b <;> core_close

/-- `shl` by a register or an immediate. -/
theorem XItem.core_shl {pc d : Nat} {ty : DType} {sat : Bool} {a b : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.shl, ty, sat, [some d], [a, b]⟩))
    (hc : Ok2 (.int ⟨.shl, ty, sat, [some d], [a, b]⟩) .threadInt a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.shl, ty, sat, [some d], [a, b]⟩) d
      (regsOf [a, b]) (coreF (.int ⟨.shl, ty, sat, [some d], [a, b]⟩)
        (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  simp only [execLocal, hr, execInt, coreW, readBits_oBits ha (reg_of_mem (by simp) hW),
    readBits_oBits hb (reg_of_mem (by simp) hW)]
  cases sat <;> cases oBits W ty.width a <;> cases oBits W 32 b <;> rfl

/-- `mul.lo`. -/
theorem XItem.core_mulLo {pc d : Nat} {ty : DType} {sat : Bool} {a b : Opnd}
    (hS : SegFreePc A pc) (hn : NoLocalRule A L g pc (.int ⟨.mul .lo, ty, sat, [some d], [a, b]⟩))
    (hc : Ok2 (.int ⟨.mul .lo, ty, sat, [some d], [a, b]⟩) .threadInt a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.mul .lo, ty, sat, [some d], [a, b]⟩) d
      (regsOf [a, b]) (coreF (.int ⟨.mul .lo, ty, sat, [some d], [a, b]⟩)
        (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  simp only [execLocal, hr, execInt, coreW, readBits_oBits ha (reg_of_mem (by simp) hW),
    readBits_oBits hb (reg_of_mem (by simp) hW)]
  cases sat <;> cases oBits W ty.width a <;> cases oBits W ty.width b <;> rfl

/-- `prmt.b32` of three operands, with a mode or the default one (`prmt none`, the generic byte
selector form `prmt.b32 d, a, b, c`). -/
theorem XItem.core_prmt {pc d : Nat} {mode : Option PrmtMode} {ty : DType} {sat : Bool}
    {a b c : Opnd}
    (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.prmt mode, ty, sat, [some d], [a, b, c]⟩))
    (hc : (Ok2 (.int ⟨.prmt mode, ty, sat, [some d], [a, b, c]⟩) .threadInt a b && plainB c &&
      ty.intLanes?.isSome) = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.prmt mode, ty, sat, [some d], [a, b, c]⟩) d
      (regsOf [a, b, c]) (coreF (.int ⟨.prmt mode, ty, sat, [some d], [a, b, c]⟩)
        (regsOf [a, b, c]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hc
  obtain ⟨⟨⟨⟨hr, ha⟩, hb⟩, hc'⟩, ⟨⟨k, lw, n⟩, hl⟩⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  simp only [execLocal, hr, execInt, intResult, hl, coreW,
    readBits_oBits ha (reg_of_mem (by simp) hW), readBits_oBits hb (reg_of_mem (by simp) hW),
    readBits_oBits hc' (reg_of_mem (by simp) hW)]
  cases sat <;> cases oBits W 32 a <;> cases oBits W 32 b <;> cases oBits W 32 c <;> rfl

set_option linter.unusedSimpArgs false in
/-- `selp` of two operands by a predicate register. -/
theorem XItem.core_selp {pc d p : Nat} {ty : DType} {sat : Bool} {a b : Opnd}
    (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩))
    (hc : Ok2 (.int ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩) .threadMove a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩) d
      (regsOf [a, b, .reg p]) (coreF (.int ⟨.selp, ty, sat, [some d], [a, b, .reg p]⟩)
        (regsOf [a, b, .reg p]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  have hWa := reg_of_mem (by simp) hW (o := a)
  have hWb := reg_of_mem (by simp) hW (o := b)
  have hp := reg_of_mem (by simp) hW (o := .reg p) p rfl
  simp only [execLocal, hr, execMove, coreW, readReg, hp, bind, Except.bind, pure, Except.pure]
  cases hv : W p <;> try rfl
  rename_i pick
  cases pick
  · simp only [Bool.false_eq_true, ↓reduceIte, readValue_oVal hb hWb]
    cases oVal W ty.width b with
    | error => rfl
    | ok v =>
      by_cases hb' : v.bytes = ty.width / 8 <;> simp [hb', throw, throwThe,
        MonadExceptOf.throw, Except.map, pure, Except.pure]
  · simp only [↓reduceIte, readValue_oVal ha hWa]
    cases oVal W ty.width a with
    | error => rfl
    | ok v =>
      by_cases ha' : v.bytes = ty.width / 8 <;> simp [ha', throw, throwThe,
        MonadExceptOf.throw, Except.map, pure, Except.pure]

/-- `shr` by a register or an immediate. -/
theorem XItem.core_shr {pc d : Nat} {ty : DType} {sat : Bool} {a b : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.shr, ty, sat, [some d], [a, b]⟩))
    (hc : Ok2 (.int ⟨.shr, ty, sat, [some d], [a, b]⟩) .threadInt a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.shr, ty, sat, [some d], [a, b]⟩) d
      (regsOf [a, b]) (coreF (.int ⟨.shr, ty, sat, [some d], [a, b]⟩)
        (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  simp only [execLocal, hr, execInt, coreW, readBits_oBits ha (reg_of_mem (by simp) hW),
    readBits_oBits hb (reg_of_mem (by simp) hW)]
  cases sat <;> cases oBits W ty.width a <;> cases oBits W 32 b <;> core_close

/-- `and` of bits, or of predicates at width 1. -/
theorem XItem.core_and {pc d : Nat} {ty : DType} {sat : Bool} {a b : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.and, ty, sat, [some d], [a, b]⟩))
    (hc : Ok2 (.int ⟨.and, ty, sat, [some d], [a, b]⟩) .threadInt a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.and, ty, sat, [some d], [a, b]⟩) d
      (regsOf [a, b]) (coreF (.int ⟨.and, ty, sat, [some d], [a, b]⟩)
        (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  have hWa := reg_of_mem (by simp) hW (o := a)
  have hWb := reg_of_mem (by simp) hW (o := b)
  simp only [execLocal, hr, execInt, coreW, logicW, readBits_oBits ha hWa,
    readBits_oBits hb hWb, readPred_oPred ha hWa, readPred_oPred hb hWb]
  cases sat <;> by_cases hw : ty.width = 1 <;> simp only [hw, ↓reduceIte] <;>
    (try cases oPred W a) <;> (try cases oPred W b) <;> (try cases oBits W ty.width a) <;>
    (try cases oBits W ty.width b) <;> rfl

/-- `or` of bits, or of predicates at width 1. -/
theorem XItem.core_or {pc d : Nat} {ty : DType} {sat : Bool} {a b : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.int ⟨.or, ty, sat, [some d], [a, b]⟩))
    (hc : Ok2 (.int ⟨.or, ty, sat, [some d], [a, b]⟩) .threadInt a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.int ⟨.or, ty, sat, [some d], [a, b]⟩) d
      (regsOf [a, b]) (coreF (.int ⟨.or, ty, sat, [some d], [a, b]⟩)
        (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  have hWa := reg_of_mem (by simp) hW (o := a)
  have hWb := reg_of_mem (by simp) hW (o := b)
  simp only [execLocal, hr, execInt, coreW, logicW, readBits_oBits ha hWa,
    readBits_oBits hb hWb, readPred_oPred ha hWa, readPred_oPred hb hWb]
  cases sat <;> by_cases hw : ty.width = 1 <;> simp only [hw, ↓reduceIte] <;>
    (try cases oPred W a) <;> (try cases oPred W b) <;> (try cases oBits W ty.width a) <;>
    (try cases oBits W ty.width b) <;> rfl

/-- `mov` of one operand. -/
theorem XItem.core_mov {pc d : Nat} {ty : DType} {a : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.move ⟨.scalar, ty, [some d], [a]⟩))
    (hc : ((Op.move ⟨.scalar, ty, [some d], [a]⟩).rule == some .threadMove && plainB a) = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.move ⟨.scalar, ty, [some d], [a]⟩) d (regsOf [a])
      (coreF (.move ⟨.scalar, ty, [some d], [a]⟩) (regsOf [a]))).Rule A L g s := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hr, ha⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  have hWa := reg_of_mem (by simp) hW (o := a)
  simp only [execLocal, hr, execMove, coreW, readValue_oVal ha hWa, readPred_oPred ha hWa]
  by_cases hp : ty = .pred <;> simp only [hp, ↓reduceIte]
  · cases oPred W a <;> rfl
  · cases oVal W ty.width a with
    | error => rfl
    | ok v =>
      by_cases hb : v.bytes = ty.width / 8 <;> simp [hb, throw, throwThe, MonadExceptOf.throw,
        Except.map, bind, Except.bind, pure, Except.pure]

/-- `mov` packing two operands. -/
theorem XItem.core_pack {pc d : Nat} {ty : DType} {a b : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (.move ⟨.pack, ty, [some d], [a, b]⟩))
    (hc : Ok2 (.move ⟨.pack, ty, [some d], [a, b]⟩) .threadMove a b = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.move ⟨.pack, ty, [some d], [a, b]⟩) d (regsOf [a, b])
      (coreF (.move ⟨.pack, ty, [some d], [a, b]⟩) (regsOf [a, b]))).Rule A L g s := by
  simp only [Ok2, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, ha⟩, hb⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  simp only [execLocal, hr, execMove, coreW, readValue_oVal ha (reg_of_mem (by simp) hW),
    readValue_oVal hb (reg_of_mem (by simp) hW)]
  cases oVal W (ty.width / 2) a with
  | error => rfl
  | ok x =>
    cases oVal W (ty.width / 2) b with
    | error => rfl
    | ok y =>
      by_cases hb : x.bytes = ty.width / 16 ∧ y.bytes = ty.width / 16 <;> simp [hb, throw,
        throwThe, MonadExceptOf.throw, Except.map, bind, Except.bind, pure, Except.pure]

/-- `cvt` from an integer to an integer. -/
theorem XItem.core_cvtInt {pc dw sw : Nat} {dk sk : IType} {c : CvtInstr} {a : Opnd}
    (hS : SegFreePc A pc) (hn : NoLocalRule A L g pc (.cvt c)) (hd : c.dst = .int dk dw)
    (hsrc : c.src = .int sk sw) (hs : c.srcs = [a])
    (hc : ((Op.cvt c).rule == some .threadCvt && plainB a) = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.cvt c) c.d (regsOf [a])
      (coreF (.cvt c) (regsOf [a]))).Rule A L g s := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hr, ha⟩ := hc
  refine XItem.core_of hS hn fun t W hW => ?_
  have hWa := reg_of_mem (by simp) hW (o := a)
  simp only [execLocal, hr, execCvt, coreW, cvtW, hs, hd, hsrc, readValue_oVal ha hWa,
    readBits_oBits ha hWa]
  cases oVal W sw a <;> cases oBits W sw a <;> core_close

/-- `cvt` from a float register to a float. -/
theorem XItem.core_cvtFloat {pc r : Nat} {df sf : FType} {c : CvtInstr}
    (hS : SegFreePc A pc) (hn : NoLocalRule A L g pc (.cvt c)) (hd : c.dst = .float df)
    (hsrc : c.src = .float sf) (hs : c.srcs = [.reg r])
    (hc : ((Op.cvt c).rule == some .threadCvt) = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (.cvt c) c.d (regsOf [.reg r])
      (coreF (.cvt c) (regsOf [.reg r]))).Rule A L g s := by
  simp only [beq_iff_eq] at hc
  refine XItem.core_of hS hn fun t W hW => ?_
  have hWa := reg_of_mem (by simp) hW (o := .reg r)
  simp only [execLocal, hc, execCvt, coreW, cvtW, hs, hd, hsrc, readCvtFloat_oCvt (hWa r rfl)]
  cases df.fmt? <;> cases sf.fmt? <;> try rfl
  simp only [bind, Except.bind]
  repeat' (split <;> (try simp_all only [Except.map, pure, Except.pure]))

end

end
end PTX.Flow
