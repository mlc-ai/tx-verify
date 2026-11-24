-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.IdealReal

@[expose] public section

/-! # Facts about the family rules

A proof tool. Facts about `IntInstr.rule`, `CvtInstr.rule` and the rules of the other instruction
families (PROG-RULE-ID) that proofs about concrete instructions share: whether the conversions the
ideal-real assumption names have a rule of their own (`CvtInstr.rule_eq_none`,
`CvtInstr.rule_of_widenF16`, `CvtInstr.rule_of_packF16`), and `execLocal` of an instruction whose
rule is known is the semantic function that rule names (`execLocal_int`, `execLocal_move`, ...).
-/

namespace PTX

/-- A conversion has no rule exactly when it is not one of the conversions THREAD-CVT gives a rule
(`CvtInstr.exact`). -/
theorem CvtInstr.rule_eq_none {c : CvtInstr} : c.rule = none ↔ c.exact = false := by
  by_cases h : c.exact <;> simp [CvtInstr.rule, h]

/-- `cvt.f32.f16` has no conversion rule exactly when its destination register sign-extends the
result: PROG-ISA-CVT gives a rule to the widening between `.f16`, `.bf16`, `.f32` and `.f64`
without a rounding modifier, and `CvtInstr.exact` asks a floating conversion not to be
sign-extended. -/
theorem CvtInstr.rule_of_widenF16 {c : CvtInstr} (h : c.widenF16?.isSome) :
    c.rule = none ↔ ∃ w, c.ext = .sign w := by
  obtain ⟨⟨d, a⟩, hw⟩ := Option.isSome_iff_exists.mp h
  have hf : c.dst = .float .f32 ∧ c.src = .float .f16 ∧ c.rnd = none ∧ c.srcs = [a] ∧
      c.plain = true := by
    unfold CvtInstr.widenF16? at hw
    split at hw <;> simp_all
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf
  have hp : c.ftz = false ∧ c.sat = false ∧ c.relu = false ∧ c.satfinite = false ∧
      c.pzo = false ∧ c.scaled = false ∧ c.pack = false := by
    rw [CvtInstr.plain] at h5
    simp_all
  obtain ⟨-, -, hrelu, hsatf, hpzo, hscaled, hpack⟩ := hp
  rw [CvtInstr.rule_eq_none]
  cases he : c.ext with
  | sign w =>
    refine ⟨fun _ => ⟨w, rfl⟩, fun _ => ?_⟩
    simp [CvtInstr.exact, h1, h2, h3, h4, he]
  | same | zero w =>
    refine ⟨fun hc => ?_, fun hex => ?_⟩
    · simp [CvtInstr.exact, h1, h2, h3, h4, CvtInstr.widens, he, hrelu, hsatf, hpzo, hscaled,
        hpack] at hc
    · obtain ⟨w', hw'⟩ := hex
      cases hw'

/-- `cvt.rn.f16x2.f32` has no conversion rule exactly when its destination register is not the
width of its packed type. PROG-ISA-CVT gives a rule to two `.f32` sources to `.f16x2` with one of
`.rn`, `.rz`, `.rm` and `.rp`, and asks a `cvt.pack` destination to keep the exact width of its
type (`CvtInstr.exact`). -/
theorem CvtInstr.rule_of_packF16 {c : CvtInstr} (h : c.packF16?.isSome) :
    c.rule = none ↔ c.ext ≠ .same := by
  obtain ⟨⟨d, a, b⟩, hp⟩ := Option.isSome_iff_exists.mp h
  have hf : c.dst = .packed (.float .f16) 2 ∧ c.src = .float .f32 ∧ c.rnd = some .rn ∧
      c.srcs = [a, b] ∧ c.plain = true := by
    unfold CvtInstr.packF16? at hp
    split at hp <;> simp_all
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf
  have hp' : c.ftz = false ∧ c.sat = false ∧ c.scaled = false ∧ c.pack = false := by
    rw [CvtInstr.plain] at h5
    simp_all
  obtain ⟨hftz, hsat, hscaled, hpack⟩ := hp'
  rw [CvtInstr.rule_eq_none]
  refine ⟨fun hc he => ?_, fun he => ?_⟩
  · simp [CvtInstr.exact, h1, h2, h3, h4, he, hftz, hsat, hscaled, hpack] at hc
  · cases he2 : c.ext with
    | same => exact absurd he2 he
    | sign w | zero w =>
      simp [CvtInstr.exact, h1, h2, h3, h4, he2, hftz, hsat, hscaled, hpack]

/-- The destination `cvt.f32.f16` names is the conversion's destination. -/
theorem CvtInstr.widenF16?_d {c : CvtInstr} {d : Nat} {a : Opnd} (h : c.widenF16? = some (d, a)) :
    d = c.d := by
  unfold widenF16? at h
  split at h <;> (try split at h) <;> simp_all

/-- The destination `cvt.rn.f16x2.f32` names is the conversion's destination. -/
theorem CvtInstr.packF16?_d {c : CvtInstr} {d : Nat} {a b : Opnd}
    (h : c.packF16? = some (d, a, b)) : d = c.d := by
  unfold packF16? at h
  split at h <;> (try split at h) <;> simp_all

section Local
variable {L : Launch} {g : Nat} {t : TState}

/-- An integer instruction with THREAD-INT as its rule runs `execInt`. -/
theorem execLocal_int {i : IntInstr} (h : i.rule = some .threadInt) :
    execLocal L g t (.int i) = execInt L g t i := by
  simp only [execLocal, Op.rule, h]

/-- A `selp` with THREAD-MOVE as its rule runs `execMove`. -/
theorem execLocal_selp {i : IntInstr} (h : i.rule = some .threadMove) :
    execLocal L g t (.int i) = execMove L g t (.int i) := by
  simp only [execLocal, Op.rule, h]

/-- A move with THREAD-MOVE as its rule runs `execMove`. -/
theorem execLocal_move {m : MoveInstr} (h : m.rule = some .threadMove) :
    execLocal L g t (.move m) = execMove L g t (.move m) := by
  simp only [execLocal, Op.rule, h]

/-- A conversion with THREAD-CVT as its rule runs `execCvt`. -/
theorem execLocal_cvt {c : CvtInstr} (h : c.rule = some .threadCvt) :
    execLocal L g t (.cvt c) = execCvt L g t c := by
  simp only [execLocal, Op.rule, h]

/-- A conversion without a rule has no local step. -/
theorem execLocal_cvt_none {c : CvtInstr} (h : c.rule = none) :
    execLocal L g t (.cvt c) = throw .noRule := by
  simp only [execLocal, Op.rule, h]

/-- An `ld.param` with THREAD-MOVE as its rule runs `execMove`. -/
theorem execLocal_mem {a : MemAccess} (h : a.rule = some .threadMove) :
    execLocal L g t (.mem a) = execMove L g t (.mem a) := by
  simp only [execLocal, Op.rule, h]

/-- A `mapa` or `getctarank` with THREAD-SHARED-POINTER as its rule runs `execSharedAddress`.
Every `cvta` and every `isspacep` has the window rule instead (THREAD-CVTA, `execLocal_cvta`),
not the data-movement or parameter-pointer rule that ran `cvta.global` and `cvta.param` before
the windows had one rule. -/
theorem execLocal_shared {c : AddrInstr} (h : c.rule = some .threadSharedPointer) :
    execLocal L g t (.addr c) = execSharedAddress L g t c := by
  simp only [execLocal, Op.rule, h]

end Local

end PTX
