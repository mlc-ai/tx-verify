-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutLit
public import Lemmas.Flow.CvtBf
public import Lemmas.Flow.FloatRead
public import Kernels.TmlFa4Fwd.Assumptions.Transparency

@[expose] public section

/-! # The readings of tml-fa4's exponent stretch, for `Tests/Gen/Out/Expo.lean`

The lemmas `Tools/out_gen.py` names in `Tests/Gen/Out/expo.json` for the run of pcs 4399–4825
(the scale product, the 64 packed `fma` of the scores, 128 `ex2.approx.ftz`, 64 conversions to
`bf16` pairs and the moves between them): no assumption takes a segment off the software-exponent
sites (`segFree`); the product and the packed `fma` are read ideally (`rule_mul`, `rule_fma2`),
`ex2` approximately (`rule_ex2`), `max.f32` of two or three sources ideally (`rule_max2`,
`rule_max3`, for `Tests/Gen/Out/max.json`), moves by Core (`rule_pack`, `rule_unpack`); a
conversion at a probability-pack site writes `packE` of its operands (`rule_cvt`: the two finite
reals as `bf16` payloads by the kernel's `bf16Convert`, else a read fault or the Core
conversion). -/

namespace PTX.Tests.Gen.ExpoRules
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

theorem forms {t : TState} {f : FloatForm}
    (hf : f ∈ [.mul .f32, .fmaRnF32x2, .max .f32]) (hp : t.pc ∉ Assumptions.swExp2Sites) :
    IdealAt Assumptions.all f l g t ∧ DeclineAt Assumptions.all f l g t := by
  have hSeg := (Assumptions.numeric_segSites.pc hp)
  have hArith : f ∈ Assumptions.arithScope.float := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> decide
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
        rcases hf with rfl | rfl | rfl <;> simp [FloatForm.ofOp, h] at ho
      simp [Assumptions.lg2, hLog]
    · cases op <;> try rfl
      rename_i c
      simp only [FloatForm.ofOp] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> split_ifs at ho <;> cases ho
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

theorem rule_fma2 {d a b c : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.base (.fma2 d a b c)).Rule Assumptions.all l g s :=
  fun _ h => forms (by simp) (off h hp)

theorem rule_ex2 {fz : Bool} {d a : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.base (.ex2 fz d a)).Rule Assumptions.all l g s :=
  fun _ h => ex2Rule (off h hp)

theorem rule_max2 {d a b : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.fn (maxOp d [a, b]) d [a, b] maxE).Rule
      Assumptions.all l g s :=
  fun _ h => have hf := forms (f := .max .f32) (by simp) (off h hp); XItem.max2_rule hf.1 hf.2

theorem rule_max3 {d a b c : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.fn (maxOp d [a, b, c]) d [a, b, c] maxE).Rule
      Assumptions.all l g s :=
  fun _ h => have hf := forms (f := .max .f32) (by simp) (off h hp); XItem.max3_rule hf.1 hf.2

theorem rule_pack {d a b : Nat} (_pc : Nat) :
    ∀ s : TState, s.pc = _pc → (XItem.base (.pack d a b)).Rule Assumptions.all l g s :=
  fun s _ => moveNone s _

theorem rule_unpack {lo hi a : Nat} (_pc : Nat) :
    ∀ s : TState, s.pc = _pc → (XItem.base (.unpack lo hi a)).Rule Assumptions.all l g s :=
  fun s _ => moveNone s _


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

end
end PTX.Tests.Gen.ExpoRules
