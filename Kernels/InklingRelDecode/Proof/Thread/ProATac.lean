-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProATable

@[expose] public section

/-! # Tools of the prologue's segment and step lemmas

The segment tactic `pro_seg` (a local segment of the code, evaluated on the registers it reads,
whose end facts are the table's: each register the segment writes is valued by the unfolding of
its definition), the local steps that the evaluator cannot run on symbolic operands (`ld.param`
of a scalar parameter, `mov.b32` packing of two 16-bit values, the signed `div.s32`), the
facts of a state after a register write, and the commands `seg_run`, `seg_elect`, `seg_pack` and
`seg_param` that state and prove one segment lemma of `ProASeg*` each. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- No assumption of the kernel has a local rule for these operations: the Core rule applies. -/
theorem asms_localRule_mem {L : Launch} {g : Nat} {t : TState} {ma : MemAccess} :
    ∀ a ∈ asms, a.localRule L g t (.mem ma) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

theorem asms_localRule_move {L : Launch} {g : Nat} {t : TState} {m : MoveInstr} :
    ∀ a ∈ asms, a.localRule L g t (.move m) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

theorem asms_localRule_int {L : Launch} {g : Nat} {t : TState} {i : IntInstr} :
    ∀ a ∈ asms, a.localRule L g t (.int i) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

theorem asms_localRule_bra {L : Launch} {g : Nat} {t : TState} {target : Nat} {uni : Bool} :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

theorem asms_segFree {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc asms pc := by
  intro a ha L g t ht
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · rfl
  · have : pc ∉ Assumptions.emuSites := by simpa using h
    simp [Assumptions.swExp2, ht, this]
  all_goals rfl

macro "asms_free" : tactic => `(tactic| exact asms_segFree (by decide +kernel))

theorem at_set_live {L : Launch} {g pc d : Nat} {t : TState} {dt : Dat} {v : Value}
    (h : At t pc (factsAt L g pc dt)) (hv : valueOf L g dt d = v)
    (hl : ∀ r ∈ Flow.live (pc + 1), r = d ∨ r ∈ Flow.live pc) :
    At (PTX.next (setReg t d v)) (pc + 1) (factsAt L g (pc + 1) dt) := by
  refine ⟨congrArg (· + 1) h.1, h.2.1, h.2.2.1, h.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
  rcases hl r hr with rfl | hr'
  · simp [setReg, PTX.next, hv]
  · by_cases hd : r = d
    · subst hd
      simp [setReg, PTX.next, hv]
    · simp only [setReg, PTX.next, Function.update_of_ne hd]
      exact holds_mem h.2.2.2.2 (mem_factsFrom hr')

/-- `ld.param` of a scalar parameter as a segment of one step. -/
theorem seg_ldParam {L : Launch} {g pc d w : Nat} {dt : Dat} {p : String} {x : BitVec 64}
    {ty : DType}
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] }⟩)
    (hw : ty.width = w) (hx : L.params p = some x) (hsf : Assumption.SegFreePc asms pc)
    (hv : valueOf L g dt d = .bits w (truncBits w x))
    (hl : ∀ r ∈ Flow.live (pc + 1), r = d ∨ r ∈ Flow.live pc)
    (hm : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] } = some .threadMove := by rfl) :
    Seg kernel asms L g 1 pc (factsAt L g pc dt) (pc + 1) (factsAt L g (pc + 1) dt) := by
  intro t h
  refine ⟨_, run_local hc rfl h
    (exec_ldParam hx (Assumption.SegFreePc.of_eq h.1 hsf) asms_localRule_mem hw hm), ?_⟩
  exact at_set_live h hv hl

/-- `mov.b32 d, {a, b}`: two 16-bit values packed, as a segment of one step. -/
theorem seg_pack32 {L : Launch} {g pc d a b : Nat} {dt : Dat}
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.pack, .int .b 32, [some d],
      [.reg a, .reg b]⟩⟩)
    (hsf : Assumption.SegFreePc asms pc) (hxa : a ∈ Flow.live pc) (hxb : b ∈ Flow.live pc)
    (hbx : (valueOf L g dt a).bytes = 2) (hby : (valueOf L g dt b).bytes = 2)
    (hv : valueOf L g dt d = joinValue (valueOf L g dt a) (valueOf L g dt b))
    (hl : ∀ r ∈ Flow.live (pc + 1), r = d ∨ r ∈ Flow.live pc) :
    Seg kernel asms L g 1 pc (factsAt L g pc dt) (pc + 1) (factsAt L g (pc + 1) dt) := by
  intro t h
  have hra : t.regs a = some (valueOf L g dt a) := holds_mem h.2.2.2.2 (mem_factsFrom hxa)
  have hrb : t.regs b = some (valueOf L g dt b) := holds_mem h.2.2.2.2 (mem_factsFrom hxb)
  have hexec : execLocalA asms L g t (.move ⟨.pack, .int .b 32, [some d], [.reg a, .reg b]⟩) =
      .ok (PTX.next (setReg t d (joinValue (valueOf L g dt a) (valueOf L g dt b)))) := by
    have hs := Assumption.SegFreePc.of_eq h.1 hsf
    simp only [hs.exec, execLocalRule_of_none (asms_localRule_move (t := t)), execLocal, Op.rule,
      MoveInstr.rule, execMove, readValue, readReg]
    simp [hra, hrb, hbx, hby, DType.width, bind, Except.bind, pure, Except.pure]
  refine ⟨_, run_local hc rfl h hexec, ?_⟩
  exact at_set_live h hv hl

theorem toSigned32_lt (x : BitVec 64) : toSigned 32 x < 2 ^ 31 := by
  dsimp only [toSigned]
  split_ifs with h <;> omega

theorem intDiv_s32 {x y : BitVec 64} (hnn : 0 ≤ intOf IType.s 32 x)
    (hpos : 0 < intOf IType.s 32 y) :
    intDiv IType.s 32 x y = .ok ((intOf IType.s 32 x).tdiv (intOf IType.s 32 y)) := by
  have h1 : intOf IType.s 32 x < 2 ^ 31 := by
    simp only [intOf, ↓reduceIte]; exact toSigned32_lt x
  have h2 : (intOf IType.s 32 x).tdiv (intOf IType.s 32 y) < 2 ^ 31 := by
    have h5 : (intOf IType.s 32 x).tdiv (intOf IType.s 32 y) =
        intOf IType.s 32 x / intOf IType.s 32 y := by
      rw [Int.tdiv_eq_ediv]; simp [hnn]
    have := Int.ediv_le_self (intOf IType.s 32 y) hnn
    omega
  unfold intDiv
  simp only [hpos.ne', bind, Except.bind, pure, Except.pure, ge_iff_le, true_and, ne_eq,
    ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
  split_ifs <;> first | rfl | (exfalso; simp only [eq_iff_iff, Nat.reduceSub] at *; omega)

/-- `div.s32 d, a, b` of two registers whose values have a rule (a non-negative dividend and a
positive divisor), as a segment of one step. -/
theorem seg_divS32 {L : Launch} {g pc d a b : Nat} {dt : Dat} {x y : BitVec 64}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.div, .int .s 32, false, [some d],
      [.reg a, .reg b]⟩⟩)
    (hsf : Assumption.SegFreePc asms pc) (hxa : a ∈ Flow.live pc) (hxb : b ∈ Flow.live pc)
    (ha : valueOf L g dt a = .bits 32 x) (hb : valueOf L g dt b = .bits 32 y)
    (hnn : 0 ≤ intOf IType.s 32 (truncBits 32 x)) (hpos : 0 < intOf IType.s 32 (truncBits 32 y))
    (hv : valueOf L g dt d = .bits 32 (intBits 32
      ((intOf IType.s 32 (truncBits 32 x)).tdiv (intOf IType.s 32 (truncBits 32 y)))))
    (hl : ∀ r ∈ Flow.live (pc + 1), r = d ∨ r ∈ Flow.live pc) :
    Seg kernel asms L g 1 pc (factsAt L g pc dt) (pc + 1) (factsAt L g (pc + 1) dt) := by
  intro t h
  have hra : t.regs a = some (.bits 32 x) := ha ▸ holds_mem h.2.2.2.2 (mem_factsFrom hxa)
  have hrb : t.regs b = some (.bits 32 y) := hb ▸ holds_mem h.2.2.2.2 (mem_factsFrom hxb)
  have hexec : execLocalA asms L g t
      (.int ⟨.div, .int .s 32, false, [some d], [.reg a, .reg b]⟩) =
      .ok (PTX.next (setReg t d (.bits 32 (intBits 32
        ((intOf IType.s 32 (truncBits 32 x)).tdiv (intOf IType.s 32 (truncBits 32 y))))))) := by
    have hs := Assumption.SegFreePc.of_eq h.1 hsf
    have hrule : (IntInstr.mk .div (.int .s 32) false [some d] [.reg a, .reg b]).rule =
        some .threadInt := by rfl
    simp only [hs.exec, execLocalRule_of_none (asms_localRule_int (t := t)),
      execLocal_int hrule, execInt]
    have hln : (DType.int IType.s 32).intLanes? = some (IType.s, 32, 1) := by rfl
    simp [intResult, readBits, readReg, hra, hrb, hln, intDiv_s32 hnn hpos, DType.width, bind,
      Except.bind, pure, Except.pure]
  refine ⟨_, run_local hc rfl h hexec, ?_⟩
  exact at_set_live h hv hl

/-- Evaluate a segment from `h`: the registers it writes are unfolded, as the table states them,
and each equation between a computed and a stated value closes by `rfl`. -/
syntax "pro_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| pro_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
        try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none]
        all_goals (try dsimp only [$extra,*, qZero, v_rs18, wCta, wSmem, wAdd32, wSub32,
          wMulLo32, wMadLo32, wMaxS32, wMinS32, wMinU32, wShrU32, wShrS32, wShl32, wShl64,
          wShl16, wAnd32, wOr32, wXor32, wNot32, wOr16, wAdd16, wCvt16of32, wCvt32of16,
          wMulHiU16, wBfeU32, wAdd64, wMulWideU32, wMulWideS32, wMadWideU32, wMadWideS32,
          wDivS32, pLtU32, pGtS32, pEqB32, pNeB32, kind_s_beq_s, kind_u_beq_s, kind_b_beq_s])
        all_goals first | rfl | (simp [$extra,*]; done) | (simp [qZero, $extra,*]; done))

/-- `seg_run name a b [skip r] [q lo hi] [extra,*]`: the segment lemma `name` from pc `a` to `b`
by `pro_seg`. `skip r` adds the fact that the predicate `r` is false at `a` (a branch that skips);
`q lo hi` takes the hypothesis that the query values `lo ≤ j < hi` are zero (`hq`), which
`pro_seg` then uses; `extra` are further unfolding lemmas. -/
syntax "seg_run " ident num num (&" skip " num)? (&" q " num num)?
    (" [" Lean.Parser.Tactic.simpLemma,* "]")? : command
/-- `seg_elect name a b ra rb hit|miss [extra,*]`: the segment lemma after an election, from the
facts of the predicates `ra` and `rb` (elected lane and guard), on their hit or miss branch. -/
syntax "seg_elect " ident num num num num ident
    " [" Lean.Parser.Tactic.simpLemma,* "]" : command
/-- `seg_pack name a j1 j2`: the `mov.b32` at `a` that packs the query values `j1` and `j2`. -/
syntax "seg_pack " ident num num num : command
/-- `seg_param name a p x`: the `ld.param` at `a` of the parameter `p` into `dt.pro.x`. -/
syntax "seg_param " ident num str ident : command

set_option hygiene false in
macro_rules
  | `(seg_run $n $a $b $[skip $r]? $[q $lo $hi]? $[[$ex,*]]?) => do
    let k := Lean.Syntax.mkNumLit (toString (b.getNat - a.getNat))
    let pre ← match r with
      | some r => `(($r, Value.pred false) :: factsAt L g $a dt)
      | none => `(factsAt L g $a dt)
    match lo, hi with
    | some lo, some hi =>
      `(theorem $n (L : Launch) (g : Nat) (dt : Dat)
          (hq : ∀ j, $lo ≤ j → j < $hi → dt.q j = qZero) :
          Seg kernel asms L g $k $a $pre $b (factsAt L g $b dt) :=
        fun t h => by pro_seg h [hq])
    | _, _ =>
      let ex := (ex.map (·.getElems)).getD #[]
      `(theorem $n (L : Launch) (g : Nat) (dt : Dat) :
          Seg kernel asms L g $k $a $pre $b (factsAt L g $b dt) :=
        fun t h => by pro_seg h [$ex,*])
  | `(seg_elect $n $a $b $ra $rb $hm [$ex,*]) => do
    let k := Lean.Syntax.mkNumLit (toString (b.getNat - a.getNat))
    let v ← match hm.getId with
      | `hit => `(true)
      | `miss => `(false)
      | _ => Lean.Macro.throwErrorAt hm "expected `hit` or `miss`"
    `(theorem $n (L : Launch) (g : Nat) (dt : Dat) (a b : Bool) (hab : (a && b) = $v) :
        Seg kernel asms L g $k $a ((($ra, Value.pred a) :: ($rb, Value.pred b) ::
          factsAt L g $a dt)) $b (factsAt L g $b dt) :=
      fun t h => by
        cases a <;> cases b <;>
          first
          | (exfalso; revert hab; decide)
          | (pro_seg h [$ex,*]))
  | `(seg_pack $n $a $j1 $j2) => do
    let b := Lean.Syntax.mkNumLit (toString (a.getNat + 1))
    let c := Lean.mkIdent (.str `Flow s!"code_{a.getNat}")
    `(theorem $n (L : Launch) (g : Nat) (dt : Dat) (hq : ∀ j, (dt.q j).bytes = 2) :
        Seg kernel asms L g 1 $a (factsAt L g $a dt) $b (factsAt L g $b dt) :=
      seg_pack32 $c (by asms_free) (by table_decide) (by table_decide) (hq $j1) (hq $j2) rfl
        (by table_decide))
  | `(seg_param $n $a $p $x) => do
    let b := Lean.Syntax.mkNumLit (toString (a.getNat + 1))
    let c := Lean.mkIdent (.str `Flow s!"code_{a.getNat}")
    `(theorem $n (L : Launch) (g : Nat) (dt : Dat) (hx : L.params (param $p) = some dt.pro.$x) :
        Seg kernel asms L g 1 $a (factsAt L g $a dt) $b (factsAt L g $b dt) :=
      seg_ldParam $c rfl hx (by asms_free) rfl (by table_decide))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
