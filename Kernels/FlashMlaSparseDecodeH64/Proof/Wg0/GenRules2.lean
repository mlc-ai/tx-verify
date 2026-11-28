-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules
public import Lemmas.Flow.OutFloatItems
public import Lemmas.Flow.Lg2Core
public import Lemmas.Flow.CvtBf
public import Lemmas.Flow.MaxCore

@[expose] public section

/-! # Warpgroup 0's numeric readings for generated runs (softmax loop and epilogue)

The lemmas `Tools/out_gen.py` names in the run declarations of the online softmax
(`Gen/Out/wg0_*.json`), at a pc of the runs (`w0Pc`: pc 157, the sink word's scaling, pcs 253
to 393 and from 474 on, outside the dead pack at 712 and the parameter addition at 1197). There
the assumption list is its numeric head (`execLocalA_w0`): `idealArith` reads the floating forms
of the runs exactly (`w0Ideal`: `IdealAt` and `DeclineAt` of every form of `w0Forms`), `approx`
reads `ex2.approx` and
`div.approx` as the exact `2 ^ x` and `x / y` on finite operands (`w0Approx`), and two kernel
readings are items of their own:

* `lg2.approx.ftz.f32 d, a` (`lg2E`, `rule_lg2`). Core's semantics (THREAD-FLOAT-APPROX) gives
  only the table of special values: `lg2(+0) = lg2(-0) = -inf`, `lg2(+inf) = +inf`, a negative
  operand or NaN gives NaN, a finite positive operand has no exact value (the table's `none` arm
  makes the Core rule fail). The kernel's `lg2Exact` gives a positive finite operand the exact
  `Real.log x / Real.log 2` and leaves every other operand to Core. `Spec.Post` speaks of the
  LSE only through `lse P e q h = lseLog2Factor * (Real.log (rowSum P e q h) / Real.log 2)` for a
  row with `rowSum ≠ 0`, and of the `+inf` bytes otherwise: at pc 1162 the operand is the
  combined row sum `l + l'` in units of `2 ^ m` (positive exactly when `rowSum ≠ 0` under the
  exact readings), so the exact branch is the one `Post` needs, and the zero row takes Core's
  `-inf`, which the `selp` of pc 1166 replaces by `+inf`.
* `cvt.rn.bf16x2.f32 d, a, b` (`bfE`, `rule_bf`): the kernel's `cvtBf16x2` packs two finite
  `f32` numbers as their exact values (`b`'s in the low half), else Core's conversion
  (`coreCvtBf`).

`div.approx.ftz.f32` (pc 1196, `1 / (l + l' + 2 ^ (sink - m))`): Core's table gives only special
values (`x / ±0`, infinities, NaN); the `approx` assumption gives two finite operands with a
nonzero divisor the exact `x / y` (a zero divisor faults), and Core's table otherwise. `Post`'s
`attn` divides by `rowSum + sinkWeight` for a row with `rowSum ≠ 0`, where the divisor at
pc 1196 is that sum in units of `2 ^ m`, positive and finite: the exact branch again. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
variable {L : Launch} {g : Nat}

/-- A pc of warpgroup 0's numeric runs: the loop body outside the peer pack, and after it. -/
def w0Pc (pc : Nat) : Bool :=
  (decide (253 ≤ pc ∧ pc < 394) || decide (474 ≤ pc) || decide (pc = 157)) && pc != 712 &&
    !paramAdds.contains pc

/-- At a pc of the runs the pc-selected rules decline. -/
theorem w0_pcRules {t : TState} {op : Op} (hp : w0Pc t.pc = true) :
    Assumptions.paramPointers.localRule L g t op = none ∧
      Assumptions.sharedBits.localRule L g t op = none := by
  simp only [w0Pc, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨h474, h712⟩, hpa⟩ := hp
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h474
  have hpa : t.pc ∉ paramAdds := by simpa [paramAdds] using hpa
  have hf : t.pc ∉ prefetchTensorMapSites := by
    simp [prefetchTensorMapSites]; omega
  have hs : t.pc ∉ Assumptions.sharedBitsSites := by simp [Assumptions.sharedBitsSites]; omega
  have hd : Assumptions.deadPackRule L g t op = none :=
    Assumptions.deadPackRule_of_none (Assumptions.deadPackWords.eq_3 _ (by omega) h712)
  have hpeer : Assumptions.peerPackRule t op = none :=
    Assumptions.peerPackRule_of_none (Assumptions.peerPack_none_of_outside (by omega))
  exact ⟨by simp [Assumptions.paramPointers, hpa, hf],
    by simp [Assumptions.sharedBits, hs, hd, hpeer]⟩

/-- **At a pc of the runs the assumption list is its numeric head.** -/
theorem execLocalA_w0 {t : TState} {op : Op} (hp : w0Pc t.pc = true) :
    execLocalA Assumptions.all L g t op =
      (Assumptions.idealArith.localRule L g t op).getD
        ((Assumptions.approx.localRule L g t op).getD
          ((Assumptions.mulBf16x2.localRule L g t op).getD
            ((Assumptions.cvtBf16x2.localRule L g t op).getD
              ((Assumptions.cvtUe8m0.localRule L g t op).getD
                ((Assumptions.lg2Exact.localRule L g t op).getD (execLocal L g t op)))))) := by
  obtain ⟨hpar, hsh⟩ := w0_pcRules (L := L) (g := g) (op := op) hp
  rw [execLocalA_noSegment (fun a ha => noSegments a ha L g t), execLocalRule]
  simp only [Assumptions.all, List.findSome?_cons, List.findSome?_nil, hpar, hsh,
    show Assumptions.ncReadOnly.localRule L g t op = none from rfl,
    show Assumptions.storeDrain.localRule L g t op = none from rfl,
    show Assumptions.commitOrder.localRule L g t op = none from rfl]
  cases Assumptions.idealArith.localRule L g t op <;>
    cases Assumptions.approx.localRule L g t op <;>
    cases Assumptions.mulBf16x2.localRule L g t op <;>
    cases Assumptions.cvtBf16x2.localRule L g t op <;>
    cases Assumptions.cvtUe8m0.localRule L g t op <;>
    cases Assumptions.lg2Exact.localRule L g t op <;> rfl

/-! ### The readings of the floating forms -/

/-- An instruction of a floating form has no kernel reading other than the ideal one. -/
theorem kernel_none {t : TState} {op : Op} {f : FloatForm} (ho : FloatForm.ofOp op = some f)
    (hc : f ≠ .cvtF32F16 ∧ f ≠ .cvtRnF16x2F32) :
    Assumptions.approx.localRule L g t op = none ∧
      Assumptions.mulBf16x2.localRule L g t op = none ∧
      Assumptions.cvtBf16x2.localRule L g t op = none ∧
      Assumptions.cvtUe8m0.localRule L g t op = none ∧
      Assumptions.lg2Exact.localRule L g t op = none := by
  have hA : Assumptions.approx.localRule L g t op = none := by
    refine approxExact_localRule_none fun x hx => ?_
    rw [approxForm_none_of_float ho] at hx
    cases hx
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · cases op with
    | float i =>
      simp only [Assumptions.mulBf16x2]
      split
      · exfalso
        simp_all [FloatForm.ofOp]
      · rfl
    | _ => rfl
  · cases op with
    | cvt c =>
      simp only [FloatForm.ofOp] at ho
      split_ifs at ho <;> cases ho <;> simp_all
    | _ => rfl
  · cases op with
    | cvt c =>
      simp only [FloatForm.ofOp] at ho
      split_ifs at ho <;> cases ho <;> simp_all
    | _ => rfl
  · cases op with
    | float i =>
      simp only [Assumptions.lg2Exact]
      split
      · exfalso
        simp_all [FloatForm.ofOp]
      · rfl
    | _ => rfl

/-- The floating forms of the runs that `idealArith` reads. -/
abbrev w0Forms : List FloatForm :=
  [.add .f32, .mul .f32, .subRn .f32, .fma .f32, .max .f32, .setp .f32, .setpInf .f32, .neg .f32,
    .addRnF32x2, .fmaRnF32x2, .mulF32x2]

/-- **The ideal readings at a pc of the runs.** -/
theorem w0Ideal {t : TState} {f : FloatForm} (hf : f ∈ w0Forms) (hp : w0Pc t.pc = true) :
    IdealAt Assumptions.all f L g t ∧ DeclineAt Assumptions.all f L g t := by
  have hs : f ∈ ([.add .f32, .mul .f32, .subRn .f32, .fma .f32, .max .f32, .setp .f32,
      .setpInf .f32, .neg .f32, .addRnF32x2, .fmaRnF32x2, .mulF32x2] : List FloatForm) := hf
  have hc : f ≠ .cvtF32F16 ∧ f ≠ .cvtRnF16x2F32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨fun op ho e he => ?_, fun op ho he => ?_⟩
  · rw [execLocalA_w0 hp]
    obtain ⟨-, -, -, -, -⟩ := kernel_none (L := L) (g := g) (t := t) ho hc
    have hi : Assumptions.idealArith.localRule L g t op = some e := by
      simp only [Assumptions.idealArith, Assumption.idealReal, ho, hs, ↓reduceIte, he]
    rw [hi]
    rfl
  · rw [execLocalA_w0 hp]
    obtain ⟨ha, hm, hb, hu, hl⟩ := kernel_none (L := L) (g := g) (t := t) ho hc
    have hi : Assumptions.idealArith.localRule L g t op = none := by
      simp only [Assumptions.idealArith, Assumption.idealReal, ho, hs, ↓reduceIte, he]
    rw [hi, ha, hm, hb, hu, hl]
    rfl

/-- **The approximate readings at a pc of the runs.** -/
theorem w0Approx {t : TState} {f : ApproxForm} (hf : f = .ex2 .f32 ∨ f = .div .f32)
    (hp : w0Pc t.pc = true) :
    ApproxAt Assumptions.all f L g t ∧ ApproxDeclineAt Assumptions.all f L g t := by
  have key (op : Op) (ho : ApproxForm.ofOp op = some f) :
      execLocalA Assumptions.all L g t op = (execApproxExact t op).getD (execLocal L g t op) := by
    rw [execLocalA_w0 hp]
    have hi : Assumptions.idealArith.localRule L g t op = none :=
      idealReal_localRule_none fun f' hf' => by rw [floatForm_none_of_approx ho] at hf'; cases hf'
    have ha : Assumptions.approx.localRule L g t op = execApproxExact t op :=
      approxExact_localRule_of ho (by rcases hf with rfl | rfl <;> decide)
    cases op with
    | float i =>
      have hm : Assumptions.mulBf16x2.localRule L g t (.float i) = none := by
        simp only [Assumptions.mulBf16x2]
        split
        · exfalso
          rcases hf with rfl | rfl <;> simp_all [ApproxForm.ofOp]
        · rfl
      have hl : Assumptions.lg2Exact.localRule L g t (.float i) = none := by
        simp only [Assumptions.lg2Exact]
        split
        · exfalso
          rcases hf with rfl | rfl <;> simp_all [ApproxForm.ofOp]
        · rfl
      rw [hi, ha, hm, show Assumptions.cvtBf16x2.localRule L g t (.float i) = none from rfl,
        show Assumptions.cvtUe8m0.localRule L g t (.float i) = none from rfl, hl]
      cases execApproxExact t (.float i) <;> rfl
    | _ => cases ho
  exact ⟨fun op ho e he => by rw [key op ho, he]; rfl, fun op ho he => by rw [key op ho, he]; rfl⟩

/-! ### The kernel's two readings -/

/-- What `lg2.approx.ftz.f32` writes: the exact base-2 logarithm of a positive finite operand,
else Core's table value. -/
def lg2E : List Value → Exec Value
  | [v] => match (valFloat .f32 v).toOption with
    | some x => if 0 < x then .ok (.float .f32 (Real.log x / Real.log 2))
      else coreFloat (lg2I true) [v]
    | none => coreFloat (lg2I true) [v]
  | _ => .error .noRule

/-- `lg2.approx.ftz.f32 d, a`. -/
def lg2Op (d : Nat) (s : List Nat) : Op := fOp (lg2I true) d [.reg (s.getD 0 0)]

theorem rule_lg2 {d a : Nat} (pc : Nat) (hp : w0Pc pc = true) :
    ∀ t : TState, t.pc = pc → (XItem.fn (lg2Op d [a]) d [a] lg2E).Rule Assumptions.all L g t := by
  intro t ht W hW
  have h := hW a (by simp)
  rw [execLocalA_w0 (ht ▸ hp)]
  have hi : Assumptions.idealArith.localRule L g t (lg2Op d [a]) = none :=
    idealReal_localRule_none fun f hf => by simp [lg2Op, fOp, FloatForm.ofOp] at hf
  have ha : Assumptions.approx.localRule L g t (lg2Op d [a]) = none :=
    approxExact_localRule_none fun f hf => by simp [lg2Op, fOp, ApproxForm.ofOp] at hf
  have hv : Assumptions.f32ValueOf L g t (.reg a) = (valFloat .f32 (W a)).toOption := by
    simp [Assumptions.f32ValueOf, readValue, readReg, h, pure, Except.pure]
  rw [hi, ha, show Assumptions.mulBf16x2.localRule L g t (lg2Op d [a]) = none from rfl,
    show Assumptions.cvtBf16x2.localRule L g t (lg2Op d [a]) = none from rfl,
    show Assumptions.cvtUe8m0.localRule L g t (lg2Op d [a]) = none from rfl]
  have hc := execLocal_lg2_core (L := L) (g := g) (fz := true) (d := d) (OpndIs.reg h)
  simp only [Assumptions.lg2Exact, lg2Op, fOp, List.getD_cons_zero, hv, List.map_cons,
    List.map_nil, lg2E]
  rcases (valFloat .f32 (W a)).toOption with _ | x
  · exact hc
  · by_cases hx : 0 < x
    · simp [hx, pure, Except.pure, Except.map]
    · simpa [hx] using hc

/-- What `cvt.rn.bf16x2.f32` writes: two finite `f32` numbers as their exact `bf16` values (the
second source's in the low half), else Core's conversion. -/
def bfE : List Value → Exec Value
  | [va, vb] => match (valFloat .f32 va).toOption, (valFloat .f32 vb).toOption with
    | some x, some y => .ok (Assumptions.bf16Pair y x)
    | _, _ => coreCvtBf va vb
  | _ => .error .noRule

/-- `cvt.rn.bf16x2.f32 d, a, b`. -/
def bfOp (d : Nat) (s : List Nat) : Op := .cvt (cvtBfInstr d (s.getD 0 0) (s.getD 1 0))

theorem rule_bf {d a b : Nat} (pc : Nat) (hp : w0Pc pc = true) :
    ∀ t : TState, t.pc = pc →
      (XItem.fn (bfOp d [a, b]) d [a, b] bfE).Rule Assumptions.all L g t := by
  intro t ht W hW
  have ha := hW a (by simp)
  have hb := hW b (by simp)
  rw [execLocalA_w0 (ht ▸ hp)]
  have hi : Assumptions.idealArith.localRule L g t (bfOp d [a, b]) = none :=
    idealReal_localRule_none fun f hf => by
      simp [bfOp, FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?] at hf
  have hva : Assumptions.f32ValueOf L g t (.reg a) = (valFloat .f32 (W a)).toOption := by
    simp [Assumptions.f32ValueOf, readValue, readReg, ha, pure, Except.pure]
  have hvb : Assumptions.f32ValueOf L g t (.reg b) = (valFloat .f32 (W b)).toOption := by
    simp [Assumptions.f32ValueOf, readValue, readReg, hb, pure, Except.pure]
  rw [hi, show Assumptions.approx.localRule L g t (bfOp d [a, b]) = none from rfl,
    show Assumptions.mulBf16x2.localRule L g t (bfOp d [a, b]) = none from rfl,
    show Assumptions.cvtUe8m0.localRule L g t (bfOp d [a, b]) = none from rfl,
    show Assumptions.lg2Exact.localRule L g t (bfOp d [a, b]) = none from rfl]
  have hc := execLocal_cvtBf (L := L) (g := g) (d := d) ha hb
  simp only [Assumptions.cvtBf16x2, bfOp, cvtBfInstr, List.getD_cons_zero, List.getD_cons_succ,
    hva, hvb, List.map_cons, List.map_nil, bfE]
  rcases (valFloat .f32 (W a)).toOption with _ | x <;>
    rcases (valFloat .f32 (W b)).toOption with _ | y
  all_goals first | rfl | exact hc

/-! ### Rules of the items, by pc -/

theorem rule_maxF {d : Nat} {a b : Opnd} (pc : Nat) (hp : w0Pc pc = true)
    (hq : [a, b].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp maxFI d [a, b]) d (regsOf [a, b]) (fF maxFL [a, b])).Rule
      Assumptions.all L g t :=
  fun _ ht => have h := w0Ideal (by decide) (ht ▸ hp); XItem.maxF_rule h.1 h.2 hq

theorem rule_add2N {d a b : Nat} (pc : Nat) (hp : w0Pc pc = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp add2NI d [.reg a, .reg b]) d (regsOf [.reg a, .reg b])
      (fF add2NL [.reg a, .reg b])).Rule Assumptions.all L g t :=
  fun _ ht => have h := w0Ideal (by decide) (ht ▸ hp); XItem.add2N_rule h.1 h.2

theorem rule_mul2N {d a b : Nat} (pc : Nat) (hp : w0Pc pc = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp mul2NI d [.reg a, .reg b]) d (regsOf [.reg a, .reg b])
      (fF mul2NL [.reg a, .reg b])).Rule Assumptions.all L g t :=
  fun _ ht => have h := w0Ideal (by decide) (ht ▸ hp); XItem.mul2N_rule h.1 h.2

theorem rule_mulF {fz : Bool} {d : Nat} {a b : Opnd} (pc : Nat) (hp : w0Pc pc = true)
    (hq : [a, b].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp (mulI fz) d [a, b]) d (regsOf [a, b]) (fF (mulL fz) [a, b])).Rule
      Assumptions.all L g t :=
  fun _ ht => have h := w0Ideal (by decide) (ht ▸ hp); XItem.mul_rule h.1 h.2 hq

theorem rule_fmaF {rnd : FloatRound} {fz : Bool} {d : Nat} {a b c : Opnd} (pc : Nat)
    (hp : w0Pc pc = true) (hq : [a, b, c].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp (fmaI rnd fz) d [a, b, c]) d (regsOf [a, b, c])
      (fF (floatE (fmaI rnd fz)) [a, b, c])).Rule Assumptions.all L g t :=
  fun _ ht => have h := w0Ideal (by decide) (ht ▸ hp); XItem.fma_rule h.1 h.2 hq

theorem rule_negF {fz : Bool} {d : Nat} {a : Opnd} (pc : Nat) (hp : w0Pc pc = true)
    (hq : [a].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp (negI fz) d [a]) d (regsOf [a]) (fF (negL fz) [a])).Rule
      Assumptions.all L g t :=
  fun _ ht => have h := w0Ideal (by decide) (ht ▸ hp); XItem.neg_rule h.1 h.2 hq

theorem rule_divF {fz : Bool} {d : Nat} {a b : Opnd} (pc : Nat) (hp : w0Pc pc = true)
    (hq : [a, b].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp (divI fz) d [a, b]) d (regsOf [a, b]) (fF (approxE (divI fz)) [a, b])).Rule
      Assumptions.all L g t :=
  fun _ ht => have h := w0Approx (.inr rfl) (ht ▸ hp); XItem.div_rule h.1 h.2 hq

theorem rule_w0 {it : OItem} (pc : Nat) (hp : w0Pc pc = true)
    (hk : (match it with
      | .fma2 .. | .add2 .. | .mul .. | .sub .. | .add .. | .setp .. => true
      | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  cases it <;> simp at hk
  all_goals first
    | exact w0Ideal (by decide) (ht ▸ hp)
    | (show IdealAt _ (setpForm _) _ _ _ ∧ DeclineAt _ (setpForm _) _ _ _
       unfold setpForm
       split <;> exact w0Ideal (by decide) (ht ▸ hp))

theorem rule_w0ex2 {fz : Bool} {d a : Nat} (pc : Nat) (hp : w0Pc pc = true) :
    ∀ t : TState, t.pc = pc → (XItem.base (.ex2 fz d a)).Rule Assumptions.all L g t :=
  fun _ ht => w0Approx (.inl rfl) (ht ▸ hp)

/-- No assumption reads an integer, move or integer conversion at a pc of the runs. -/
theorem noRuleW0 {op : Op} (pc : Nat) (hp : w0Pc pc = true)
    (hk : (match op with
      | .int _ | .move _ => true
      | .cvt c => match c.dst with | .int .. => true | _ => false
      | _ => false) = true := by exact rfl) : NoLocalRule Assumptions.all L g pc op := by
  intro t ht a ha
  obtain ⟨hpar, hsh⟩ := w0_pcRules (L := L) (g := g) (op := op) (ht ▸ hp)
  have hf : ∀ f, FloatForm.ofOp op = some f → False := by
    intro f hf
    cases op <;> simp at hk
    all_goals first
      | (simp [FloatForm.ofOp] at hf; done)
      | (rename_i c
         cases hd : c.dst <;> simp [hd] at hk
         simp [FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, hd] at hf)
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact idealReal_localRule_none fun f h => (hf f h).elim
  · exact approxExact_localRule_none fun f h => by
      cases op <;> simp at hk <;> simp [ApproxForm.ofOp] at h
  rotate_left 5
  · exact hpar
  rotate_left 1
  · exact hsh
  all_goals (cases op <;> simp at hk)
  all_goals first
    | rfl
    | (rename_i c
       cases hd : c.dst <;> simp [hd] at hk
       simp [Assumptions.cvtBf16x2, Assumptions.cvtUe8m0, hd])

/-- No assumption reads a move or a selection of a run. -/
theorem rule_move {it : OItem} (pc : Nat) (hp : w0Pc pc = true)
    (hk : (match it with
      | .mov .. | .movImm .. | .pack .. | .unpack .. | .selp .. => true
      | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  cases it <;> simp at hk <;> exact noRuleW0 pc hp rfl t ht

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
