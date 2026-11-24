-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Lib.OutKinds
public import Lemmas.Flow.CvtBf
public import Lemmas.Flow.FloatRead
public import Lemmas.Flow.MaskedPack
public import Lemmas.Flow.OutLit
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' readings for generated runs

The lemmas `Tools/out_gen.py` names in the softmax warps' run declarations (`Gen/*.json`): no
assumption takes a segment at a pc outside the software-exponent sites (`segFree`); the scalar and
packed floating instructions of the role's numeric stretches are read ideally (`rule_mul`,
`rule_add`, `rule_sub`, `rule_fma2`, `rule_add2`), `ex2` approximately (`rule_ex2`), moves by Core
(`rule_pack`, `rule_unpack`, `rule_mov`). Two conversions are the role's own readings (`XItem.fn`):
at a bias-widening site `cvt.f32.bf16` writes `widenE` of its operand (`rule_widen`: a finite
`bf16` payload as itself by the kernel's `bf16Convert`, else the Core conversion), and at a
probability-pack site `cvt.rn.bf16x2.f32` writes `packE` of its operands (`rule_cvt`: two finite
reals as `bf16` payloads, else a read fault or the Core conversion). The first version of these
lemmas is lane L's test file for the exponent stretch (`Tests/Gen/Out/ExpoRules.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Gen
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd
noncomputable section
variable {l : Launch} {g : Nat}

theorem segFree (pc : Nat) (hp : Assumptions.swExp2Sites.contains pc = false) :
    SegFreePc Assumptions.all pc := by
  have hn : pc ∉ Assumptions.swExp2Sites := by simpa using hp
  intro a ha L g t ht
  simp only [Assumptions.all, List.mem_append, List.mem_singleton] at ha
  rcases ha with (h | h) | h
  · exact Assumptions.numeric_segSites.pc hn a h L g t ht
  · simp only [Assumptions.synchronization, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · subst h; rfl

/-- The floating forms of the role's runs that the ideal assumption reads. -/
abbrev idealForms : List FloatForm :=
  [.mul .f32, .fmaRnF32x2, .add .f32, .subRn .f32, .addRnF32x2]

theorem forms {t : TState} {f : FloatForm}
    (hf : f ∈ idealForms) (hp : t.pc ∉ Assumptions.swExp2Sites) :
    IdealAt Assumptions.all f l g t ∧ DeclineAt Assumptions.all f l g t := by
  have hSeg := (Assumptions.numeric_segSites.pc hp)
  have hArith : f ∈ Assumptions.arithScope.float := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_⟩
  · intro op ho result hr
    rw [Assumptions.execLocalA_all_eq_numeric]
    exact (idealAt_head hArith hSeg.tail : IdealAt Assumptions.numeric f l g t) op ho result hr
  · intro op ho hr
    rw [Assumptions.execLocalA_all_eq_numeric]
    apply declineAt_head _ hSeg.tail op ho hr
    intro a ha op ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · apply approxExact_localRule_none
      intro x hx
      rw [approxForm_none_of_float ho] at hx
      cases hx
    · have hLog : Assumptions.lg2Operands op = none := by
        cases op <;> try rfl
        rename_i i
        cases h : i.op <;> simp [Assumptions.lg2Operands, h]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl <;> simp [FloatForm.ofOp, h] at ho
      simp [Assumptions.lg2, hLog]
    · cases op <;> try rfl
      rename_i c
      simp only [FloatForm.ofOp] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl <;> split_ifs at ho <;> cases ho
    · rfl

theorem ex2Rule {t : TState} (hp : t.pc ∉ Assumptions.swExp2Sites) :
    ApproxAt Assumptions.all (.ex2 .f32) l g t ∧
      ApproxDeclineAt Assumptions.all (.ex2 .f32) l g t := by
  have key (op : Op) (hf : ApproxForm.ofOp op = some (.ex2 .f32)) :
      execLocalA Assumptions.all l g t op =
        (execApproxExact t op).getD (execLocal l g t op) := by
    rw [Assumptions.execLocalA_all_eq_numeric, ((Assumptions.numeric_segSites.pc hp).at rfl).exec]
    have hi : Assumptions.idealArith.localRule l g t op = none :=
      idealReal_localRule_none fun f hf' => by rw [floatForm_none_of_approx hf] at hf'; cases hf'
    have ha : Assumptions.approx.localRule l g t op = execApproxExact t op :=
      approxExact_localRule_of hf (by decide)
    have hl : Assumptions.lg2Operands op = none := by
      cases op <;> try rfl
      rename_i i
      cases he : i.op <;> simp [Assumptions.lg2Operands, he]
      simp [ApproxForm.ofOp, he] at hf
    have hL : Assumptions.lg2.localRule l g t op = none := by simp [Assumptions.lg2, hl]
    have hB : Assumptions.bf16Convert.localRule l g t op = none := by
      cases op <;> try rfl
      cases hf
    simp only [execLocalRule, Assumptions.numeric, List.findSome?_cons, hi, ha, hL, hB]
    cases execApproxExact t op <;> rfl
  exact ⟨fun op hf e he => by rw [key op hf, he]; rfl,
    fun op hf he => by rw [key op hf, he]; rfl⟩

theorem moveNone (t : TState) (m : MoveInstr) :
    ∀ a ∈ Assumptions.all, a.localRule l g t (.move m) = none := by
  intro a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem off {s : TState} {pc : Nat} (h : s.pc = pc)
    (hp : Assumptions.swExp2Sites.contains pc = false) : s.pc ∉ Assumptions.swExp2Sites := by
  rw [h]; simpa using hp

theorem rule_mul {fz : Bool} {d a b : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.base (.mul fz d a b)).Rule Assumptions.all l g s :=
  fun _ h => forms (by simp) (off h hp)

theorem rule_add {fz : Bool} {d a b : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.base (.add fz d a b)).Rule Assumptions.all l g s :=
  fun _ h => forms (by simp) (off h hp)

theorem rule_sub {fz : Bool} {d a b : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.base (.sub fz d a b)).Rule Assumptions.all l g s :=
  fun _ h => forms (by simp) (off h hp)

theorem rule_fma2 {d a b c : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.base (.fma2 d a b c)).Rule Assumptions.all l g s :=
  fun _ h => forms (by simp) (off h hp)

theorem rule_add2 {d a b : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.base (.add2 d a b)).Rule Assumptions.all l g s :=
  fun _ h => forms (by simp) (off h hp)

theorem rule_ex2 {fz : Bool} {d a : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.base (.ex2 fz d a)).Rule Assumptions.all l g s :=
  fun _ h => ex2Rule (off h hp)

theorem rule_pack {d a b : Nat} (_pc : Nat) :
    ∀ s : TState, s.pc = _pc → (XItem.base (.pack d a b)).Rule Assumptions.all l g s :=
  fun s _ => moveNone s _

theorem rule_unpack {lo hi a : Nat} (_pc : Nat) :
    ∀ s : TState, s.pc = _pc → (XItem.base (.unpack lo hi a)).Rule Assumptions.all l g s :=
  fun s _ => moveNone s _

theorem rule_mov {d a : Nat} (_pc : Nat) :
    ∀ s : TState, s.pc = _pc → (XItem.base (.mov d a)).Rule Assumptions.all l g s :=
  fun s _ => moveNone s _

/-! ### The probability packs -/

/-- The kernel's reading of a probability operand: its real value when finite. -/
def finV (v : Value) : Option (Exec ℝ) :=
  bindRead (readEReal .f32 v) fun x => if x = ⊤ ∨ x = ⊥ then none else some (pure x.toReal)

/-- What `cvt.rn.bf16x2.f32` at a probability-pack site writes: the two finite reals as `bf16`
payloads, a read fault, or the Core conversion. -/
def packE : List Value → Exec Value
  | [va, vb] => (bindRead (finV va) fun x => bindRead (finV vb) fun y =>
      some (pure (.pair (.float .bf16 y) (.float .bf16 x)))).getD (coreCvtBf va vb)
  | _ => .error .typeMismatch

def cvtOp (d : Nat) (s : List Nat) : Op := .cvt (cvtBfInstr d (s.getD 0 0) (s.getD 1 0))

theorem rule_cvt {d a b : Nat} (pc : Nat)
    (hp : Assumptions.probPackSites.contains pc = true)
    (hs : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.fn (cvtOp d [a, b]) d [a, b] packE).Rule
      Assumptions.all l g s := by
  intro t ht W hW
  have ha := hW a (by simp)
  have hb := hW b (by simp)
  have hn : t.pc ∉ Assumptions.swExp2Sites := off ht hs
  have hm : Assumptions.probPackSites.contains t.pc = true := by rw [ht]; exact hp
  show execLocalA Assumptions.all l g t (cvtOp d [a, b]) =
    (packE [W a, W b]).map fun v => PTX.next (setReg t d v)
  rw [Assumptions.execLocalA_all_eq_numeric, ((Assumptions.numeric_segSites.pc hn).at rfl).exec]
  have hI : Assumptions.idealArith.localRule l g t (cvtOp d [a, b]) = none := rfl
  have hA : Assumptions.approx.localRule l g t (cvtOp d [a, b]) = none := rfl
  have hL : Assumptions.lg2.localRule l g t (cvtOp d [a, b]) = none := rfl
  have hS : Assumptions.swExp2.localRule l g t (cvtOp d [a, b]) = none := rfl
  have hB : Assumptions.bf16Convert.localRule l g t (cvtOp d [a, b]) =
      bindRead (finV (W a)) fun x => bindRead (finV (W b)) fun y =>
        some (pure (next (setReg t d (.pair (.float .bf16 y) (.float .bf16 x))))) := by
    change (if !Assumptions.probPackSites.contains t.pc then none
      else bindRead (readFinite t .f32 (.reg a)) fun x =>
        bindRead (readFinite t .f32 (.reg b)) fun y =>
          some (pure (next (setReg t d (.pair (.float .bf16 y) (.float .bf16 x)))))) = _
    simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, readFinite,
      readERealOpnd_reg ha, readERealOpnd_reg hb, finV]
  have hC := execLocal_cvtBf (L := l) (g := g) (d := d) ha hb
  simp only [execLocalRule, Assumptions.numeric, List.findSome?_cons, List.findSome?_nil, hI, hA,
    hL, hB, hS, packE]
  rcases finV (W a) with _ | (e | x)
  · exact hC
  · rfl
  rcases finV (W b) with _ | (e | y)
  · exact hC
  · rfl
  · rfl

/-! ### The bias widenings -/

/-- The kernel's reading of a bias half: its real value when finite. -/
def finBf (v : Value) : Option (Exec ℝ) :=
  bindRead (readEReal .bf16 v) fun x => if x = ⊤ ∨ x = ⊥ then none else some (pure x.toReal)

/-- What `cvt.f32.bf16` at a bias-widening site writes: a finite payload as itself in `f32`, a
read fault, or the Core conversion. -/
def widenE : List Value → Exec Value
  | [h] => (bindRead (finBf h) fun x => some (pure (.float .f32 x))).getD (coreWidenBf h)
  | _ => .error .typeMismatch

def widenOp (d : Nat) (s : List Nat) : Op := .cvt (widenBfC d (.reg (s.getD 0 0)))

theorem rule_widen {d a : Nat} (pc : Nat)
    (hp : Assumptions.biasWidenSites.contains pc = true)
    (hs : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.fn (widenOp d [a]) d [a] widenE).Rule
      Assumptions.all l g s := by
  intro t ht W hW
  have ha := hW a (by simp)
  have hn : t.pc ∉ Assumptions.swExp2Sites := off ht hs
  have hm : Assumptions.biasWidenSites.contains t.pc = true := by rw [ht]; exact hp
  show execLocalA Assumptions.all l g t (widenOp d [a]) =
    (widenE [W a]).map fun v => PTX.next (setReg t d v)
  rw [Assumptions.execLocalA_all_eq_numeric, ((Assumptions.numeric_segSites.pc hn).at rfl).exec]
  have hI : Assumptions.idealArith.localRule l g t (widenOp d [a]) = none := rfl
  have hA : Assumptions.approx.localRule l g t (widenOp d [a]) = none := rfl
  have hL : Assumptions.lg2.localRule l g t (widenOp d [a]) = none := rfl
  have hS : Assumptions.swExp2.localRule l g t (widenOp d [a]) = none := rfl
  have hB : Assumptions.bf16Convert.localRule l g t (widenOp d [a]) =
      bindRead (finBf (W a)) fun x => some (pure (next (setReg t d (.float .f32 x)))) := by
    change (if !Assumptions.biasWidenSites.contains t.pc then none
      else bindRead (readFinite t .bf16 (.reg a)) fun x =>
          some (pure (next (setReg t d (.float .f32 x))))) = _
    simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, readFinite,
      readERealOpnd_reg ha, finBf]
  have hC := execLocal_widenBf_core (L := l) (g := g) (d := d) ha
  simp only [execLocalRule, Assumptions.numeric, List.findSome?_cons, List.findSome?_nil, hI, hA,
    hL, hB, hS, widenE]
  rcases finBf (W a) with _ | (e | x)
  · exact hC
  · rfl
  · rfl

/-! ### The local rules write only their instruction's registers -/

theorem frame_next_setReg {op : Op} {t : TState} {d : Nat} {v : Value}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    LocalFrame op t (next (setReg t d v)) :=
  ⟨.inl hpc.symm, rfl, rfl, rfl, fun r hr =>
    Function.update_of_ne (fun e => hr (by subst e; exact hd)) _ _⟩

theorem lg2Operands_spec {op : Op} {d : Nat} {a : Opnd}
    (h : Assumptions.lg2Operands op = some (d, a)) : nextPc op 0 = 1 ∧ d ∈ writesRegs op := by
  unfold Assumptions.lg2Operands at h
  split at h
  · rename_i f
    split at h
    · split_ifs at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rename_i hd _ _
      refine ⟨rfl, ?_⟩
      simp [writesRegs, hd]
    · cases h
  · cases h

theorem nextPc_float (f : FloatInstr) (pc : Nat) : nextPc (.float f) pc = pc + 1 := rfl
theorem nextPc_cvt (c : CvtInstr) (pc : Nat) : nextPc (.cvt c) pc = pc + 1 := rfl

theorem bindRead_eq_ok {α β : Type} {X : Option (Exec α)} {k : α → Option (Exec β)} {u : β}
    (h : bindRead X k = some (.ok u)) : ∃ x, X = some (.ok x) ∧ k x = some (.ok u) := by
  rcases X with _ | (e | x)
  · cases h
  · cases h
  · exact ⟨x, rfl, h⟩

theorem lg2_frame {t t' : TState} {op : Op}
    (h : Assumptions.lg2.localRule l g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.lg2] at h
  cases hop : Assumptions.lg2Operands op with
  | none => simp [hop] at h
  | some p =>
    obtain ⟨d, a⟩ := p
    obtain ⟨-, hd⟩ := lg2Operands_spec hop
    have hf : ∃ f, op = .float f := by
      unfold Assumptions.lg2Operands at hop; split at hop
      · exact ⟨_, rfl⟩
      · cases hop
    obtain ⟨f, rfl⟩ := hf
    rw [hop] at h
    by_cases hs : (!Assumptions.lg2Sites.contains t.pc) = true
    · simp only [hs, ↓reduceIte] at h; cases h
    simp only [hs, Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at h
    obtain ⟨x, -, hx⟩ := bindRead_eq_ok h
    split_ifs at hx
    simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hx
    subst hx
    exact frame_next_setReg (nextPc_float f t.pc) hd

theorem bf16_frame {t t' : TState} {op : Op}
    (h : Assumptions.bf16Convert.localRule l g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.bf16Convert] at h
  split at h
  · rename_i d a hw
    have hc : ∃ c, op = .cvt c ∧ c.d = d := by
      unfold Assumptions.biasWidenOperands at hw
      split at hw
      · rename_i c
        split at hw
        · split_ifs at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          exact ⟨c, rfl, hw.1⟩
        · cases hw
      · cases hw
    obtain ⟨c, rfl, rfl⟩ := hc
    split_ifs at h
    obtain ⟨x, -, hx⟩ := bindRead_eq_ok h
    simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hx
    subst hx
    exact frame_next_setReg (nextPc_cvt c t.pc) (by simp [writesRegs])
  · cases hop : Assumptions.probPackOperands op with
    | none => simp [hop] at h
    | some p =>
      obtain ⟨d, a, b⟩ := p
      have hc : ∃ c, op = .cvt c ∧ c.d = d := by
        cases op <;> simp only [Assumptions.probPackOperands, reduceCtorEq] at hop
        rename_i c _
        refine ⟨c, rfl, ?_⟩
        revert hop
        split
        · split_ifs <;> intro hop <;> simp_all
        · intro hop; cases hop
      obtain ⟨c, rfl, hcd⟩ := hc
      rw [hop] at h
      by_cases hs : (!Assumptions.probPackSites.contains t.pc) = true
      · simp only [hs, ↓reduceIte] at h; cases h
      simp only [hs, Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at h
      obtain ⟨x, -, hx⟩ := bindRead_eq_ok h
      obtain ⟨y, -, hy⟩ := bindRead_eq_ok hx
      simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hy
      subst hy
      exact frame_next_setReg (nextPc_cvt c t.pc) (by simp [writesRegs, hcd])

/-- **Every local rule of the kernel's assumptions writes only its instruction's registers.** -/
theorem rulesFrame : RulesFrame Assumptions.all := by
  intro a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ _ _ => idealReal_frame
  · exact fun _ _ _ _ _ => approxExact_frame
  · exact fun _ _ _ _ _ => lg2_frame
  · exact fun _ _ _ _ _ => bf16_frame
  all_goals intro _ _ _ _ _ h; cases h

/-- No assumption takes a segment at the positions `s` to `s + n - 1` when none is a software
exponent site (a Boolean check). -/
theorem segFree_range {s n : Nat}
    (h : (List.range n).all (fun i => !Assumptions.swExp2Sites.contains (s + i)) = true) :
    ∀ i < n, SegFreePc Assumptions.all (s + i) := by
  intro i hi
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  exact segFree _ (by simpa using this)

/-! ### The readings' specifications for the kind checker -/

theorem finBf_float (r : ℝ) : finBf (.float .bf16 r) = some (.ok r) := by
  simp [finBf, readEReal, bindRead, pure, Except.pure]

theorem finBf_mask : finBf (.bits 16 (BitVec.ofNat 64 0xFF80)) = none := by
  have hc := classify_negInf_bf16
  simp only [finBf, readEReal, readEReal.ofDatum, hc, ↓reduceIte, bindRead, pure, Except.pure]
  simp

theorem widenE_spec : WidenSpec widenE := by
  intro h hh
  rcases hh with ⟨r, rfl⟩ | rfl
  · refine ⟨.float .f32 r, ?_, .inl ⟨clean_float r, r, readEReal_float r⟩⟩
    simp only [widenE, finBf_float, bindRead, Option.getD_some]
    rfl
  · refine ⟨negInf32, ?_, .inr rfl⟩
    simp only [widenE, finBf_mask, bindRead, Option.getD_none]
    exact coreWidenBf_negInf

theorem finV_real {v : Value} {r : ℝ} (h : readEReal .f32 v = some (.ok (r : EReal))) :
    finV v = some (.ok r) := by
  simp [finV, h, bindRead, pure, Except.pure]

theorem packE_spec : PackSpec packE := by
  intro a b ha hb
  obtain ⟨-, x, hx⟩ := ha
  obtain ⟨-, y, hy⟩ := hb
  refine ⟨.pair (.float .bf16 y) (.float .bf16 x), ?_, ?_⟩
  · simp only [packE, finV_real hx, finV_real hy, bindRead, Option.getD_some]
    rfl
  · refine ⟨rfl, ?_, ?_⟩
    · intro _ _ _ e; cases e
    · intro _ _ e; cases e

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Gen
