-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Machine
public import Lemmas.Flow.FloatRead
public import Lemmas.Assumption.Facts

@[expose] public section

/-! # Conversions to half precision

A proof tool. Under the ideal-real assumption a `cvt.rn.f16x2.f32 d, a, b` reads its two operands
as extended reals and writes their pair of halves (`cvtPairE`): an infinity is converted to that
infinity, an operand the ideal rule rejects (a value of the wrong width, or no bit pattern at all)
makes it fault, and a NaN operand makes the ideal rule decline, so that the Core conversion rule
converts the two data (`coreCvtPair`). For a run of such conversions: when every conversion has an
outcome, local steps write each destination with its pair (`cvt_chain`, `cvtPairV`) and keep every
other register; otherwise the thread is dead (`cvt_chain_dead`). For two single-precision numbers
the pair is that of their halves (`cvtPairV_of_valFloat`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- The half-precision value a conversion makes of a value: the real it reads as a
single-precision float. -/
def half (v : Value) : Value := .float .f16 ((valFloat .f32 v).toOption.getD 0)

theorem readFloat_reg {t : TState} {r : Nat} {v : Value} (h : t.regs r = some v) :
    readFloat t .f32 (.reg r) = valFloat .f32 v := by
  cases v <;> simp [readFloat, readReg, h, valFloat, bind, Except.bind, pure, Except.pure]

theorem half_of {v : Value} {x : ℝ} (h : valFloat .f32 v = .ok x) : half v = .float .f16 x := by
  simp [half, h, Except.toOption]

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- `cvt.rn.f16x2.f32 d, a, b`. -/
abbrev cvtPairInstr (d a b : Nat) : CvtInstr :=
  { dst := .packed (.float .f16) 2, src := .float .f32, rnd := some .rn, d := d,
    srcs := [.reg a, .reg b] }

/-- The pair the Core rule of `cvt.rn.f16x2.f32 d, a, b` (THREAD-CVT) writes for the value `va` of
`a` and `vb` of `b`: each operand's datum rounded to the nearest `.f16`, `b`'s in the low half. -/
def coreCvtPair (va vb : Value) : Exec Value := do
  let xa ← classify .f32 va
  let xb ← classify .f32 vb
  let hi ← cvtNum (cvtPairInstr 0 0 0) .f16 FloatFmt.f16.layout .rn false 1 xa
  let lo ← cvtNum (cvtPairInstr 0 0 0) .f16 FloatFmt.f16.layout .rn false 1 xb
  pure (.pair (lo.toValue .f16) (hi.toValue .f16))

/-- **The Core rule of a conversion to a pair of halves** writes the pair `coreCvtPair` of its
operands' values. -/
theorem execLocal_cvtPair {t : TState} {d a b : Nat} {va vb : Value} (ha : t.regs a = some va)
    (hb : t.regs b = some vb) :
    execLocal L g t (.cvt (cvtPairInstr d a b)) =
      (coreCvtPair va vb).map fun v => PTX.next (setReg t d v) := by
  have hr : (Op.cvt (cvtPairInstr d a b)).rule = some .threadCvt := by
    simp [Op.rule, CvtInstr.rule, CvtInstr.exact]
  have hc : cvtNum (cvtPairInstr d a b) = cvtNum (cvtPairInstr 0 0 0) := rfl
  simp only [execLocal, hr]
  simp [execCvt, readCvtFloat, readReg, ha, hb, cvtScales, FType.layout?, FType.fmt?, cvtPack,
    CvtRnd.mode?, hc, coreCvtPair]
  generalize classify .f32 va = ca
  generalize classify .f32 vb = cb
  rcases ca with _ | xa
  · rfl
  rcases cb with _ | xb
  · rfl
  simp only [bind, Except.bind, Except.map, Functor.map]
  generalize cvtNum (cvtPairInstr 0 0 0) .f16 FloatFmt.f16.layout .rn false 1 xa = ya
  generalize cvtNum (cvtPairInstr 0 0 0) .f16 FloatFmt.f16.layout .rn false 1 xb = yb
  rcases ya with _ | ya <;> rcases yb with _ | yb <;> rfl

/-- What `cvt.rn.f16x2.f32 d, a, b` writes for the values `va`, `vb` of its operands under an
ideal-real assumption for the form (`Assumption.execIdealFloat`): the pair of their extended reals
as halves, `vb`'s in the low half; the fault of the first operand the ideal rule rejects; and the
Core rule's pair when the ideal rule declines a NaN operand. -/
def cvtPairE (va vb : Value) : Exec Value :=
  match Assumption.readEReal .f32 va with
  | some (.error e) => .error e
  | some (.ok x) => match Assumption.readEReal .f32 vb with
    | some (.error e) => .error e
    | some (.ok y) => .ok (.pair (Assumption.erealValue .f16 y) (Assumption.erealValue .f16 x))
    | none => coreCvtPair va vb
  | none => coreCvtPair va vb

/-- The pair a conversion writes (`b32 0` where it faults). -/
def cvtPairV (va vb : Value) : Value :=
  match cvtPairE va vb with
  | .ok v => v
  | .error _ => .bits 32 0

theorem cvtPairV_of_ok {va vb v : Value} (h : cvtPairE va vb = .ok v) : cvtPairV va vb = v := by
  simp [cvtPairV, h]

/-- **The local step of a conversion to a pair of halves** under an ideal-real assumption for the
form that leaves a declined conversion to the Core rule. -/
theorem exec_cvtPair (hA : Assumption.IdealFor A .cvtRnF16x2F32)
    (hD : Assumption.DeclineCore A .cvtRnF16x2F32) {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.cvt (cvtPairInstr d a b)) =
      (cvtPairE va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : Assumption.FloatForm.ofOp (.cvt (cvtPairInstr d a b)) = some .cvtRnF16x2F32 := by
    simp [Assumption.FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, CvtInstr.plain]
  have hra := readERealOpnd_reg (fmt := .f32) ha
  have hrb := readERealOpnd_reg (fmt := .f32) hb
  have hI : Assumption.execIdealFloat L g t (.cvt (cvtPairInstr d a b)) =
      Assumption.bindRead (Assumption.readEReal .f32 va) fun x =>
        Assumption.bindRead (Assumption.readEReal .f32 vb) fun y =>
          some (pure (PTX.next (setReg t d
            (.pair (Assumption.erealValue .f16 y) (Assumption.erealValue .f16 x))))) := by
    simp [Assumption.execIdealFloat, CvtInstr.widenF16?, CvtInstr.packF16?, CvtInstr.plain, hra,
      hrb]
  unfold cvtPairE
  rcases hx : Assumption.readEReal .f32 va with _ | (e | x)
  · rw [hD L g t _ hf (by rw [hI, hx]; rfl), execLocal_cvtPair ha hb]
  · rw [hA L g t _ hf _ (by rw [hI, hx]; rfl)]; rfl
  · rcases hy : Assumption.readEReal .f32 vb with _ | (e | y)
    · rw [hD L g t _ hf (by rw [hI, hx, hy]; rfl), execLocal_cvtPair ha hb]
    · rw [hA L g t _ hf _ (by rw [hI, hx, hy]; rfl)]; rfl
    · rw [hA L g t _ hf _ (by rw [hI, hx, hy]; rfl)]; rfl

/-- **Two single-precision numbers convert to the pair of their halves.** -/
theorem cvtPairE_of_valFloat {va vb : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) :
    cvtPairE va vb = .ok (.pair (.float .f16 y) (.float .f16 x)) := by
  have hv : ∀ z : ℝ, Assumption.erealValue .f16 (z : EReal) = .float .f16 z := fun z => by
    unfold Assumption.erealValue
    rw [ite_eq_right (EReal.coe_ne_top z), ite_eq_right (EReal.coe_ne_bot z)]
    rfl
  simp only [cvtPairE, readEReal_of_valFloat hx, readEReal_of_valFloat hy, hv]

theorem cvtPairV_of_valFloat {va vb : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) : cvtPairV va vb = .pair (half vb) (half va) := by
  rw [cvtPairV_of_ok (cvtPairE_of_valFloat hx hy), half_of hx, half_of hy]

theorem toValue_f16_bytes (x : FVal) : (x.toValue .f16).bytes = 2 := by
  rcases x with neg | q | neg | p
  · cases neg <;> rfl
  · rfl
  · rfl
  · cases p <;> rfl

theorem erealValue_f16_bytes (x : EReal) : (Assumption.erealValue .f16 x).bytes = 2 := by
  unfold Assumption.erealValue
  split_ifs <;> rfl

theorem pair_f16_bytes (x y : FVal) :
    (Value.pair (x.toValue .f16) (y.toValue .f16)).bytes = 4 := by
  show (x.toValue .f16).bytes + (y.toValue .f16).bytes = 4
  rw [toValue_f16_bytes, toValue_f16_bytes]

/-- A converted pair has four bytes. -/
theorem cvtPairV_bytes (va vb : Value) : (cvtPairV va vb).bytes = 4 := by
  have hc : ∀ w, coreCvtPair va vb = .ok w → w.bytes = 4 := by
    intro w hw
    simp only [coreCvtPair, bind, Except.bind, pure, Except.pure] at hw
    repeat' split at hw
    all_goals first | (cases hw; exact pair_f16_bytes _ _) | cases hw
  unfold cvtPairV
  split
  · rename_i v h
    unfold cvtPairE at h
    repeat' split at h
    all_goals first
      | exact hc v h
      | (cases h
         show (Assumption.erealValue .f16 _).bytes + (Assumption.erealValue .f16 _).bytes = 4
         rw [erealValue_f16_bytes, erealValue_f16_bytes])
      | cases h
  · rfl

/-- One conversion whose operands hold `va` and `vb`: a local step to the state with its pair, or
undefined behaviour. -/
theorem out_cvtPair (hA : Assumption.IdealFor A .cvtRnF16x2F32)
    (hD : Assumption.DeclineCore A .cvtRnF16x2F32) {t : TState} {c : Nat × Nat × Nat}
    {va vb : Value}
    (hc : K.code[t.pc]? = some ⟨none, .cvt (cvtPairInstr c.1 c.2.1 c.2.2)⟩)
    (hf : t.fault = none) (ha : t.regs c.2.1 = some va) (hb : t.regs c.2.2 = some vb) :
    out K A L g t = match cvtPairE va vb with
      | .ok v => .tau (PTX.next (setReg t c.1 v))
      | .error f => .ev (.ub f) := by
  simp only [out, hf, hc, guardHolds, pure, Except.pure, Op.isLocal,
    exec_cvtPair (L := L) (g := g) hA hD ha hb]
  cases cvtPairE va vb <;> rfl

/-- The code holds the conversions `cs` from `pc` on. -/
def CvtCode (K : Kernel) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | pc, c :: cs => K.code[pc]? = some ⟨none, .cvt (cvtPairInstr c.1 c.2.1 c.2.2)⟩ ∧
      CvtCode K (pc + 1) cs

/-- No conversion writes a register a later one reads or writes. -/
def CvtFresh : List (Nat × Nat × Nat) → Prop
  | [] => True
  | c :: cs => (∀ c' ∈ cs, c.1 ≠ c'.2.1 ∧ c.1 ≠ c'.2.2 ∧ c.1 ≠ c'.1) ∧ CvtFresh cs

instance decCvtFresh : (cs : List (Nat × Nat × Nat)) → Decidable (CvtFresh cs)
  | [] => isTrue trivial
  | c :: cs =>
    have := decCvtFresh cs
    inferInstanceAs (Decidable ((∀ c' ∈ cs, c.1 ≠ c'.2.1 ∧ c.1 ≠ c'.2.2 ∧ c.1 ≠ c'.1) ∧
      CvtFresh cs))

/-- **A run of conversions that all have an outcome**: local steps write each destination with
the pair of its operands' values and keep every other register. -/
theorem cvt_chain (hA : Assumption.IdealFor A .cvtRnF16x2F32)
    (hD : Assumption.DeclineCore A .cvtRnF16x2F32) :
    ∀ (cs : List (Nat × Nat × Nat)) (t : TState), CvtCode K t.pc cs → CvtFresh cs →
      t.fault = none → t.sub = 0 → t.acc = [] →
      (∀ c ∈ cs, ∃ va vb, t.regs c.2.1 = some va ∧ t.regs c.2.2 = some vb ∧
        ∃ v, cvtPairE va vb = .ok v) →
      ∃ t', run K A L g cs.length t = some t' ∧ t'.pc = t.pc + cs.length ∧ t'.sub = 0 ∧
        t'.acc = [] ∧ t'.fault = none ∧
        (∀ c ∈ cs, ∀ va vb, t.regs c.2.1 = some va → t.regs c.2.2 = some vb →
          t'.regs c.1 = some (cvtPairV va vb)) ∧
        ∀ r, r ∉ cs.map (·.1) → t'.regs r = t.regs r
  | [], t, _, _, hf, hs, ha, _ => ⟨t, rfl, rfl, hs, ha, hf, by simp, fun _ _ => rfl⟩
  | c :: cs, t, ⟨hc, hcs⟩, ⟨hfr, hfs⟩, hf, hs, ha, hok => by
    obtain ⟨va, vb, hva, hvb, v, hv⟩ := hok c (by simp)
    have hout := out_cvtPair (K := K) (L := L) (g := g) hA hD hc hf hva hvb
    rw [hv] at hout
    set t1 := PTX.next (setReg t c.1 v) with ht1
    have hreg : ∀ r, r ≠ c.1 → t1.regs r = t.regs r := fun r hr => by
      simp [ht1, PTX.next, setReg, Function.update_of_ne hr]
    obtain ⟨t', hr, hpc, hs', ha', hf', hd, ho⟩ := cvt_chain hA hD cs t1
      (by simpa [ht1, PTX.next, setReg] using hcs) hfs
      (by simp [ht1, PTX.next, setReg, hf]) (by simp [ht1, PTX.next, setReg, hs])
      (by simp [ht1, PTX.next, setReg, ha])
      (fun c' hc' => by
        obtain ⟨va', vb', hva', hvb', hok'⟩ := hok c' (by simp [hc'])
        obtain ⟨h1, h2, -⟩ := hfr c' hc'
        exact ⟨va', vb', by rw [hreg _ (Ne.symm h1)]; exact hva',
          by rw [hreg _ (Ne.symm h2)]; exact hvb', hok'⟩)
    refine ⟨t', ?_, by rw [hpc]; simp [ht1, PTX.next, setReg]; omega, hs', ha', hf', ?_, ?_⟩
    · simp only [List.length_cons, run, tauStep, hout, Option.bind_some]
      exact hr
    · intro c' hc' va' vb' ha' hb'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · have hnot : c'.1 ∉ cs.map (·.1) := by
          intro hm
          obtain ⟨c'', hc'', he⟩ := List.mem_map.mp hm
          exact (hfr c'' hc'').2.2 he.symm
        rw [hva] at ha'
        rw [hvb] at hb'
        cases ha'; cases hb'
        rw [ho _ hnot]
        simp [ht1, PTX.next, setReg, cvtPairV_of_ok hv]
      · obtain ⟨h1, h2, -⟩ := hfr c' hc'
        exact hd c' hc' va' vb' (by rw [hreg _ (Ne.symm h1)]; exact ha')
          (by rw [hreg _ (Ne.symm h2)]; exact hb')
    · intro r hr
      simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, hreg r hr.1]

/-- **A run of conversions one of which faults**: the thread is dead. -/
theorem cvt_chain_dead (hA : Assumption.IdealFor A .cvtRnF16x2F32)
    (hD : Assumption.DeclineCore A .cvtRnF16x2F32) :
    ∀ (cs : List (Nat × Nat × Nat)) (t : TState), CvtCode K t.pc cs → CvtFresh cs →
      t.fault = none →
      (∀ c ∈ cs, (∃ va, t.regs c.2.1 = some va) ∧ ∃ vb, t.regs c.2.2 = some vb) →
      (∃ c ∈ cs, ∀ va vb, t.regs c.2.1 = some va → t.regs c.2.2 = some vb →
        ∃ f, cvtPairE va vb = .error f) →
      Machine.Dead (K := K) (A := A) (L := L) (g := g) t
  | [], _, _, _, _, _, ⟨_, hc, _⟩ => by simp at hc
  | c :: cs, t, ⟨hc, hcs⟩, ⟨hfr, hfs⟩, hf, hval, hbad => by
    obtain ⟨⟨va, hva⟩, ⟨vb, hvb⟩⟩ := hval c (by simp)
    have hout := out_cvtPair (K := K) (L := L) (g := g) hA hD hc hf hva hvb
    rcases hv : cvtPairE va vb with f | v
    · rw [hv] at hout
      exact Machine.dead_of_ub hout
    · rw [hv] at hout
      have hreg : ∀ r, r ≠ c.1 → (PTX.next (setReg t c.1 v)).regs r = t.regs r := fun r hr => by
        simp [PTX.next, setReg, Function.update_of_ne hr]
      refine Machine.dead_of_tau hout (cvt_chain_dead hA hD cs _
        (by simpa [PTX.next, setReg] using hcs) hfs (by simp [PTX.next, setReg, hf])
        (fun c' hc' => ?_) ?_)
      · obtain ⟨h1, h2, -⟩ := hfr c' hc'
        obtain ⟨⟨va', h1'⟩, ⟨vb', h2'⟩⟩ := hval c' (by simp [hc'])
        exact ⟨⟨va', by rw [hreg _ (Ne.symm h1)]; exact h1'⟩,
          ⟨vb', by rw [hreg _ (Ne.symm h2)]; exact h2'⟩⟩
      · obtain ⟨c', hc', hb⟩ := hbad
        rcases List.mem_cons.mp hc' with rfl | hc'
        · obtain ⟨f, hf'⟩ := hb va vb hva hvb
          rw [hv] at hf'; cases hf'
        · obtain ⟨h1, h2, -⟩ := hfr c' hc'
          exact ⟨c', hc', fun va' vb' ha' hb' =>
            hb va' vb' (by rwa [hreg _ (Ne.symm h1)] at ha')
              (by rwa [hreg _ (Ne.symm h2)] at hb')⟩

end
end PTX.Flow
