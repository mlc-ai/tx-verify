-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.FloatPlain
public import Lemmas.Flow.OutLit
public import Lemmas.Flow.OutFloatItems
public import Lemmas.Flow.OutCoreRules
public import Lemmas.Flow.OutUnpack
public import Lemmas.Flow.MaxCore

@[expose] public section

/-! # The softmax warp's readings for generated runs

The lemmas `Tools/out_gen.py` names in `Gen/Out/softmax_*.json`, at a pc of a run (`smPc`). Outside
the software `exp2` sites (pcs 1913 and above) and the single-instruction readings (pcs 600, 807
and 2562) the assumption list reads the floating forms of the runs exactly (`idealArith`, as
`FloatPlain` already uses it) and no other assumption has a local rule for them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow PTX.Flow.TyG PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat}

/-- A pc of the first run window: the scores' scaling, bias and maximum (pcs 1299 to 1837). -/
def smPc (pc : Nat) : Bool := decide (1299 ≤ pc ∧ pc < 1838)

/-- A pc of a run outside the software `exp2` sites and the single-instruction readings. -/
def intPc (pc : Nat) : Bool := decide (pc < 1913 ∧ pc ≠ 600 ∧ pc ≠ 807)

theorem smSegFree {pc : Nat} (hp : intPc pc = true) : Assumption.SegFreePc Assumptions.all pc := by
  simp only [intPc, decide_eq_true_eq] at hp
  refine Kernels.InklingRelDecode.Proof.segFree ?_
  rw [Bool.eq_false_iff]
  intro h
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, he⟩ := h
  omega

/-- No assumption reads an integer, a move or an integer conversion at a pc that is none of the
single-instruction readings' sites (pcs 600, 807 and 2562). -/
theorem noRuleAt {op : Op} (pc : Nat) (hp : pc ≠ 600 ∧ pc ≠ 807 ∧ pc ≠ 2562)
    (hk : (match op with
      | .int _ | .move _ => true
      | .cvt c => match c.dst with | .int .. => true | _ => false
      | _ => false) = true := by exact rfl) : NoLocalRule Assumptions.all L g pc op := by
  intro t ht a ha
  have hf : ∀ f, FloatForm.ofOp op = some f → False := by
    intro f hf
    cases op <;> simp at hk
    all_goals first
      | (simp [FloatForm.ofOp] at hf; done)
      | (rename_i c
         cases hd : c.dst <;> simp [hd] at hk
         simp [FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, hd] at hf)
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | ha
  · exact idealReal_localRule_none fun f h => (hf f h).elim
  · exact approxExact_localRule_none fun f h => by
      cases op <;> simp at hk <;> simp [ApproxForm.ofOp] at h
  by_cases hc : ∃ c, op = .cvt c
  · obtain ⟨c, rfl⟩ := hc
    have hd : ∃ k w, c.dst = .int k w := by
      cases hd : c.dst <;> simp [hd] at hk
      exact ⟨_, _, rfl⟩
    obtain ⟨k, w, hd⟩ := hd
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact, Assumptions.negExact,
        Assumptions.bf16Exact, hd]
  · exact other_rules_none (by omega) (by omega) (by omega) (fun c h => hc ⟨c, h⟩) a
      (by simp only [Assumptions.all, List.drop_succ_cons, List.drop_zero, List.mem_cons,
        List.not_mem_nil, or_false]; exact ha)

/-- No assumption reads an integer, a move or an integer conversion at a pc of the runs. -/
theorem noRuleSm {op : Op} (pc : Nat) (hp : intPc pc = true)
    (hk : (match op with
      | .int _ | .move _ => true
      | .cvt c => match c.dst with | .int .. => true | _ => false
      | _ => false) = true := by exact rfl) : NoLocalRule Assumptions.all L g pc op := by
  simp only [intPc, decide_eq_true_eq] at hp
  exact noRuleAt pc ⟨hp.2.1, hp.2.2, by omega⟩ hk

/-- No assumption reads a move or a selection of a run. -/
theorem rule_move {it : OItem} (pc : Nat) (hp : intPc pc = true)
    (hk : (match it with
      | .mov .. | .movImm .. | .pack .. | .unpack .. | .selp .. => true
      | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  cases it <;> simp at hk <;> exact noRuleSm pc hp rfl t ht

/-- The unpack of a word into two halves is Core's move. -/
theorem rule_unpack {w lo hi a : Nat} (pc : Nat) (hp : intPc pc = true)
    (hr : (YItem.unpack w lo hi a).op.rule = some .threadMove) :
    ∀ s : TState, s.pc = pc → (YItem.unpack w lo hi a).Rule Assumptions.all L g s :=
  YItem.unpack_rule hr (fun s hs a' ha' => noRuleSm pc hp rfl s hs a' ha')

/-- The fused multiply-add of two lanes is read as exact. -/
theorem rule_fma2 {it : OItem} (pc : Nat) (hp : smPc pc = true)
    (hk : (match it with | .fma2 .. => true | _ => false) = true) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  cases it <;> simp at hk
  have h := (floatPlain (L := L) (g := g) (a := 1299) (b := 1838) le_rfl le_rfl).ideal t
    (by simp only [smPc, decide_eq_true_eq] at hp; omega)
    (by simp only [smPc, decide_eq_true_eq] at hp; omega)
  exact h.2

/-- The same rules for the items of a run with unpacks (`YItem.x`). -/
theorem rule_moveY {it : OItem} (pc : Nat) (hp : intPc pc = true)
    (hk : (match it with
      | .mov .. | .movImm .. | .pack .. | .unpack .. | .selp .. => true
      | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (YItem.x (XItem.base it)).Rule Assumptions.all L g t :=
  rule_move pc hp hk

theorem rule_fma2Y {it : OItem} (pc : Nat) (hp : smPc pc = true)
    (hk : (match it with | .fma2 .. => true | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (YItem.x (XItem.base it)).Rule Assumptions.all L g t :=
  rule_fma2 pc hp hk

theorem rule_maxF {d : Nat} {a b : Opnd} (pc : Nat) (hp : smPc pc = true)
    (hq : [a, b].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp maxFI d [a, b]) d (regsOf [a, b]) (fF maxFL [a, b])).Rule
      Assumptions.all L g t := by
  intro t ht
  have h := (floatPlain (L := L) (g := g) (a := 1299) (b := 1838) le_rfl le_rfl).ideal t
    (by simp only [smPc, decide_eq_true_eq] at hp; omega)
    (by simp only [smPc, decide_eq_true_eq] at hp; omega)
  exact XItem.maxF_rule h.1.1 h.1.2 hq

/-- `max.f32` of two or three sources (the library's `maxE`) at a pc of the first window. -/
theorem rule_max {d : Nat} {srcs : List Nat} (pc : Nat) (hp : smPc pc = true)
    (hk : (srcs.length = 2 ∨ srcs.length = 3) := by exact Or.inl rfl) :
    ∀ t : TState, t.pc = pc → (XItem.fn (maxOp d srcs) d srcs maxE).Rule Assumptions.all L g t := by
  intro t ht
  have h := (floatPlain (L := L) (g := g) (a := 1299) (b := 1838) le_rfl le_rfl).ideal t
    (by simp only [smPc, decide_eq_true_eq] at hp; omega)
    (by simp only [smPc, decide_eq_true_eq] at hp; omega)
  match srcs, hk with
  | [a, b], _ => exact XItem.max2_rule h.1.1 h.1.2
  | [a, b, c], _ => exact XItem.max3_rule h.1.1 h.1.2

/-! ### The widening of a bias half -/

/-- The value the Core rule (THREAD-CVT) writes for `cvt.f32.bf16` of a register holding `h`. -/
def coreWidenBf (h : Value) : Exec Value :=
  classify .bf16 h >>= fun x =>
    widenElem (widenBfC 0 (.reg 0)) .f32 FloatFmt.f32.layout false x >>= fun y =>
      pure (y.toValue .f32)

/-- **The outcome of `cvt.f32.bf16`** (`bf16Exact`): the number of the half as an `.f32` extended
real, the fault of a value the reading rejects, Core's value for a NaN. -/
def widenBfE : List Value → Exec Value
  | [h] => match readEReal .bf16 h with
    | some (.error e) => .error e
    | some (.ok x) => .ok (erealValue .f32 x)
    | none => coreWidenBf h
  | _ => .error .noRule

theorem execLocal_widenBf_value {t : TState} {d r : Nat} {v : Value} (h : t.regs r = some v) :
    execLocal L g t (.cvt (widenBfC d (.reg r))) =
      (coreWidenBf v).map fun w => PTX.next (setReg t d w) := by
  have hw : widenElem (widenBfC d (.reg r)) = widenElem (widenBfC 0 (.reg 0)) := rfl
  have hr : (Op.cvt (widenBfC d (.reg r))).rule = some .threadCvt := by
    simp [Op.rule, CvtInstr.rule, CvtInstr.exact, CvtInstr.widens]
  simp only [execLocal, hr]
  simp [execCvt, readCvtFloat, readReg, h, FType.fmt?, hw, coreWidenBf, bind, Except.bind,
    Except.map, pure, Except.pure]
  cases classify .bf16 v with
  | error e => rfl
  | ok x =>
    dsimp only
    cases widenElem (widenBfC 0 (.reg 0)) .f32 FloatFmt.f32.layout false x <;> rfl

/-- `cvt.f32.bf16 d, a`. -/
def widenBfOp (d : Nat) (s : List Nat) : Op := .cvt (widenBfC d (.reg (s.getD 0 0)))

theorem rule_widenBf {d a : Nat} (pc : Nat) (hp : smPc pc = true) :
    ∀ t : TState, t.pc = pc →
      (XItem.fn (widenBfOp d [a]) d [a] widenBfE).Rule Assumptions.all L g t := by
  intro t ht W hW
  have h := hW a (by simp)
  have hp' : 1299 ≤ t.pc ∧ t.pc < 1838 := by
    simp only [smPc, decide_eq_true_eq] at hp; omega
  obtain ⟨hs, hn⟩ := (floatPlain (L := L) (g := g) (a := 1299) (b := 1838) le_rfl le_rfl).widen t
    hp'.1 hp'.2 d a
  have hrd : readERealOpnd t .bf16 (.reg a) = readEReal .bf16 (W a) := by
    simp [readERealOpnd, readReg, h, pure, Except.pure]
  show execLocalA Assumptions.all L g t (.cvt (widenBfC d (.reg a))) = (widenBfE [W a]).map _
  simp only [widenBfE]
  cases hx : readEReal .bf16 (W a) with
  | none =>
    have := hn (by simp [execWidenBf, hrd, hx, bindRead])
    rw [this, execLocal_widenBf_value h]
  | some r =>
    cases r with
    | error e =>
      have := hs (.error e) (by simp [execWidenBf, hrd, hx, bindRead])
      rw [this]; rfl
    | ok x =>
      have := hs (.ok (next (setReg t d (erealValue .f32 x))))
        (by simp [execWidenBf, hrd, hx, bindRead, pure, Except.pure])
      rw [this]; rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
