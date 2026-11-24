-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxHardwareWords
public import Lemmas.Flow.Widen

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

def firstPackPc (quarter : Fin 4) (word : Nat) : Nat := firstHardwarePc quarter + 32 + 3 * word

def firstPackScratch (quarter : Fin 4) : Nat := 3815 + 16 * quarter.val

def firstPackedReg (quarter : Fin 4) : Nat := 8154 + 8 * quarter.val

def probabilityWord (exponents : Nat → ℝ) (word : Nat) : Value :=
  .pair (.float .bf16 (exponents (2 * word))) (.float .bf16 (exponents (2 * word + 1)))

def probabilityDoubleWord (exponents : Nat → ℝ) (word : Nat) : Value :=
  .pair (probabilityWord exponents (2 * word)) (probabilityWord exponents (2 * word + 1))

private def movePackInstr (dst lo hi : Nat) : MoveInstr :=
  ⟨.pack, .int .b 64, [some dst], [.reg lo, .reg hi]⟩

private def cvtPackInstr (dst a b : Nat) : CvtInstr :=
  { dst := .packed (.float .bf16) 2
    src := .float .f32
    rnd := some .rn
    d := dst
    srcs := [.reg a, .reg b] }

private def isCvtPack (pc dst a b : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .cvt c⟩ => decide (c = cvtPackInstr dst a b)
  | _ => false

private def isMovePack (pc dst lo hi : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .move m⟩ => decide (m = movePackInstr dst lo hi)
  | _ => false

private def packWordCheck (quarter : Fin 4) (word : Nat) : Bool :=
  let pc := firstPackPc quarter word
  let input := firstHardwareOutput quarter + 4 * word
  let high := firstPackScratch quarter + 2 * word
  let low := high + 1
  isCvtPack pc high (input + 3) (input + 2) &&
    Assumptions.probPackSites.contains pc &&
    isCvtPack (pc + 1) low (input + 1) input &&
    Assumptions.probPackSites.contains (pc + 1) &&
    isMovePack (pc + 2) (firstPackedReg quarter + word) low high

set_option maxRecDepth 100000 in
private theorem packWordTable (quarter : Fin 4) :
    (List.range 8).all (packWordCheck quarter) = true := by
  fin_cases quarter <;> kernel_rfl

private theorem cvtPackCode {pc dst a b : Nat} (h : isCvtPack pc dst a b = true) :
    kernel.code[pc]? = some ⟨none, probabilityConvertOp dst a b⟩ := by
  unfold isCvtPack at h
  split at h
  · rename_i c hc
    rw [hc, of_decide_eq_true h]
    rfl
  · cases h

private theorem movePackCode {pc dst lo hi : Nat} (h : isMovePack pc dst lo hi = true) :
    kernel.code[pc]? = some ⟨none, .move (movePackInstr dst lo hi)⟩ := by
  unfold isMovePack at h
  split at h
  · rename_i c hc
    rw [hc, of_decide_eq_true h]
  · cases h

private theorem readProbability {t : TState} {r : Nat} {x : ℝ}
    (h : t.regs r = some (.float .f32 x)) : readFinite t .f32 (.reg r) = some (.ok x) := by
  simp [readFinite, readERealOpnd_reg h, readEReal, bindRead, pure, Except.pure,
    EReal.coe_ne_top, EReal.coe_ne_bot]

section
variable {l : Launch}

/-- Two consecutive rounded-format conversions and their pack place four probabilities
in a 64-bit register, in increasing score-column order from low to high. -/
theorem firstPackWordRun {g : Nat} (quarter : Fin 4) {word : Nat} (hw : word < 8) {t : TState}
    (exponents : Nat → ℝ) (ht : At t (firstPackPc quarter word) [])
    (hInput : ∀ i < 32, t.regs (firstHardwareOutput quarter + i) = some (.float .f32 (exponents i)))
    :
    ∃ u, run kernel Assumptions.all l g 3 t = some u ∧
      At u (firstPackPc quarter (word + 1)) [] ∧
      u.regs (firstPackedReg quarter + word) = some (probabilityDoubleWord exponents word) ∧
      ∀ r, r ≠ firstPackScratch quarter + 2 * word →
        r ≠ firstPackScratch quarter + 2 * word + 1 → r ≠ firstPackedReg quarter + word →
          u.regs r = t.regs r := by
  let pc := firstPackPc quarter word
  let input := firstHardwareOutput quarter + 4 * word
  let high := firstPackScratch quarter + 2 * word
  let low := high + 1
  let packed := firstPackedReg quarter + word
  let highVal := probabilityWord exponents (2 * word + 1)
  let lowVal := probabilityWord exponents (2 * word)
  let s := next (setReg t high highVal)
  let v := next (setReg s low lowVal)
  let u := next (setReg v packed (probabilityDoubleWord exponents word))
  have hTable := List.all_eq_true.mp (packWordTable quarter) word (List.mem_range.mpr hw)
  simp only [packWordCheck, Bool.and_eq_true] at hTable
  obtain ⟨⟨⟨⟨hcHigh, hSiteHigh⟩, hcLow⟩, hSiteLow⟩, hcMove⟩ := hTable
  have hRaw {i : Nat} (hi : i < 4) :
      t.regs (input + i) = some (.float .f32 (exponents (4 * word + i))) := by
    unfold input
    rw [Nat.add_assoc]
    exact hInput _ (by omega)
  have hHigh := probabilityConvertRun (l := l) (g := g) ht (cvtPackCode hcHigh)
    (by simpa using hSiteHigh) (readProbability (hRaw (i := 3) (by decide)))
    (readProbability (hRaw (i := 2) (by decide)))
  have hHighEq : run kernel Assumptions.all l g 1 t = some s := by
    have h1 : 2 * (2 * word + 1) = 4 * word + 2 := by omega
    have h2 : 2 * (2 * word + 1) + 1 = 4 * word + 3 := by omega
    simpa only [s, highVal, probabilityWord, h1, h2] using hHigh
  have hs : At s (pc + 1) [(high, highVal)] := ht.set (by simp)
  have hlo0 : s.regs input = some (.float .f32 (exponents (4 * word))) := by
    have hne : input ≠ high := by
      have := quarter.isLt
      unfold input high firstHardwareOutput firstPackScratch
      omega
    simpa only [s, next, setReg, Function.update_of_ne hne, Nat.add_zero] using
      (hRaw (i := 0) (by decide))
  have hlo1 : s.regs (input + 1) = some (.float .f32 (exponents (4 * word + 1))) := by
    have hne : input + 1 ≠ high := by
      have := quarter.isLt
      unfold input high firstHardwareOutput firstPackScratch
      omega
    simpa only [s, next, setReg, Function.update_of_ne hne] using (hRaw (i := 1) (by decide))
  have hLow := probabilityConvertRun (l := l) (g := g) hs (cvtPackCode hcLow)
    (by simpa using hSiteLow) (readProbability hlo1) (readProbability hlo0)
  have hLowEq : run kernel Assumptions.all l g 1 s = some v := by
    have h0 : 2 * (2 * word) = 4 * word := by omega
    simpa only [v, lowVal, probabilityWord, h0] using hLow
  have hv : At v (pc + 2) [(low, lowVal), (high, highVal)] := by
    have ht' := hs.set (r := low) (v := lowVal) (by simp [low])
    exact ht'
  have hOff : v.pc ∉ Assumptions.swExp2Sites := by
    have := quarter.isLt
    rw [hv.1]
    simp only [pc, firstPackPc, firstHardwarePc, Assumptions.swExp2Sites,
      List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hMove : run kernel Assumptions.all l g 1 v = some u := by
    apply run_local (movePackCode hcMove) rfl hv
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
    exact exec_pack (A := []) (d := packed) (by simp [NoPack])
      hv.2.2.2.2.1 hv.2.2.2.2.2.1 SegFreePc.nil
  have hp : u.pc = firstPackPc quarter (word + 1) := by
    have hh := hv.1
    change v.pc + 1 = _
    unfold pc firstPackPc at *
    omega
  have hAt : At u (firstPackPc quarter (word + 1)) [] :=
    ⟨hp, hv.2.1, hv.2.2.1, hv.2.2.2.1, trivial⟩
  refine ⟨u, run_comp (run_comp hHighEq hLowEq) hMove, hAt, Function.update_self .., ?_⟩
  intro r hHighR hLowR hPackedR
  change r ≠ high at hHighR
  change r ≠ low at hLowR
  change r ≠ packed at hPackedR
  simp only [u, v, s, next, setReg, Function.update_of_ne hHighR, Function.update_of_ne hLowR,
    Function.update_of_ne hPackedR]

private theorem firstPackInterval {g : Nat} (quarter : Fin 4) (values : Nat → ℝ) :
    ∀ (count offset : Nat) (t : TState), offset + count ≤ 8 →
      At t (firstPackPc quarter offset) [] →
      (∀ i < 32, t.regs (firstHardwareOutput quarter + i) = some (.float .f32 (values i))) →
      ∃ u, run kernel Assumptions.all l g (3 * count) t = some u ∧
        At u (firstPackPc quarter (offset + count)) [] ∧
        (∀ i, offset ≤ i → i < offset + count →
          u.regs (firstPackedReg quarter + i) = some (probabilityDoubleWord values i)) ∧
        ∀ r, (r < firstPackScratch quarter + 2 * offset ∨
            firstPackScratch quarter + 2 * (offset + count) ≤ r) →
          (r < firstPackedReg quarter + offset ∨
            firstPackedReg quarter + (offset + count) ≤ r) → u.regs r = t.regs r := by
  intro count
  induction count with
  | zero =>
    intro offset t _ ht _
    exact ⟨t, rfl, by simpa only [Nat.add_zero] using ht,
      fun _ hlo hhi => (by omega : False).elim, fun _ _ _ => rfl⟩
  | succ count ih =>
    intro offset t hRange ht hInput
    have hQ := quarter.isLt
    obtain ⟨s, hs, hS, hVal, hFrame⟩ := firstPackWordRun quarter (show offset < 8 by omega)
      values ht hInput
    have hArgs (i : Nat) (hi : i < 32) :
        s.regs (firstHardwareOutput quarter + i) = some (.float .f32 (values i)) := by
      rw [hFrame]
      · exact hInput i hi
      all_goals simp only [firstHardwareOutput, firstPackScratch, firstPackedReg]; omega
    obtain ⟨u, hu, hU, hVals, hKeep⟩ := ih (offset + 1) s (by omega) hS hArgs
    have hSteps : 3 + 3 * count = 3 * (count + 1) := by omega
    have hLen : offset + 1 + count = offset + (count + 1) := by omega
    refine ⟨u, by simpa only [hSteps] using run_comp hs hu,
      by simpa only [hLen] using hU, ?_, ?_⟩
    · intro i hlo hhi
      by_cases h : i = offset
      · subst i
        rw [hKeep]
        · exact hVal
        · right
          unfold firstPackedReg firstPackScratch
          omega
        · exact .inl (by omega)
      · exact hVals i (by omega) (by omega)
    · intro r hSmall hPair
      have hSmall' : r < firstPackScratch quarter + 2 * (offset + 1) ∨
          firstPackScratch quarter + 2 * (offset + 1 + count) ≤ r := by
        rcases hSmall with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      have hPair' : r < firstPackedReg quarter + (offset + 1) ∨
          firstPackedReg quarter + (offset + 1 + count) ≤ r := by
        rcases hPair with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      rw [hKeep r hSmall' hPair']
      apply hFrame
      · rcases hSmall with h | h <;> omega
      · rcases hSmall with h | h <;> omega
      · rcases hPair with h | h <;> omega

/-- A complete first-round quarter computes 32 hardware exponents and its eight
double words, leaving the next quarter's scores and all earlier packed words intact. -/
theorem firstPackedQuarterRun {g : Nat} (quarter : Fin 4) {t : TState} {F : List (Nat × Value)}
    (raw : Nat → Value) (values : Nat → ℝ) (ht : At t (firstHardwarePc quarter) F)
    (hRaw : ∀ i < 32, t.regs (firstHardwareInput quarter + i) = some (raw i))
    (hEval : ∀ i < 32, ex2E true (raw i) = .ok (.float .f32 (values i))) :
    ∃ u, run kernel Assumptions.all l g 56 t = some u ∧
      At u (firstHardwarePc quarter + 56) [] ∧
      (∀ i < 8, u.regs (firstPackedReg quarter + i) = some (probabilityDoubleWord values i)) ∧
      (∀ i < 32, u.regs (firstHardwareOutput quarter + i) = some (fl (values i))) ∧
      ∀ r, (r < firstHardwareOutput quarter ∨ firstHardwareOutput quarter + 32 ≤ r) →
        (r < firstPackScratch quarter ∨ firstPackScratch quarter + 16 ≤ r) →
        (r < firstPackedReg quarter ∨ firstPackedReg quarter + 8 ≤ r) → u.regs r = t.regs r := by
  obtain ⟨s, hs, hS, hReg, hSFrame⟩ :=
    firstHardwareBlockRun (l := l) (g := g) quarter raw (fun i => .float .f32 (values i))
      ht hRaw hEval
  obtain ⟨u, hu, hU, hVal, hFrame⟩ := firstPackInterval (l := l) (g := g) quarter values
    8 0 s (by decide) (by simpa only [firstPackPc, Nat.mul_zero, Nat.add_zero] using hS) hReg
  refine ⟨u, run_comp hs hu, ?_, fun i hi => hVal i (Nat.zero_le _) hi, ?_, ?_⟩
  · simpa only [firstPackPc, Nat.zero_add, Nat.add_assoc] using hU
  · intro i hi
    rw [hFrame]
    · exact hReg i hi
    · left
      unfold firstHardwareOutput firstPackScratch
      omega
    · left
      unfold firstHardwareOutput firstPackedReg
      omega
  · intro r hExponent hScratch hPacked
    exact (hFrame r (by simpa only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] using hScratch)
      (by simpa only [Nat.zero_add, Nat.add_zero] using hPacked)).trans (hSFrame r hExponent)

private theorem firstPackGroups {g : Nat} (raw : Fin 4 → Nat → Value) (values : Fin 4 → Nat → ℝ)
    (hEval : ∀ q i, i < 32 → ex2E true (raw q i) = .ok (.float .f32 (values q i))) :
    ∀ (count offset : Nat) (t : TState), offset + count ≤ 4 →
      At t (4594 + 56 * offset) [] →
      (∀ q i, i < 32 → t.regs (firstHardwareInput q + i) = some (raw q i)) →
      ∃ u, run kernel Assumptions.all l g (56 * count) t = some u ∧
        At u (4594 + 56 * (offset + count)) [] ∧
        (∀ q : Fin 4, offset ≤ q.val → q.val < offset + count → ∀ i < 8,
          u.regs (firstPackedReg q + i) = some (probabilityDoubleWord (values q) i)) ∧
        (∀ q : Fin 4, offset ≤ q.val → q.val < offset + count → ∀ i < 32,
          u.regs (firstHardwareOutput q + i) = some (fl (values q i))) ∧
        ∀ r, (r < 1231 + 32 * offset ∨ 1231 + 32 * (offset + count) ≤ r) →
          (r < 3815 ∨ 3879 ≤ r) → (r < 8154 + 8 * offset ∨ 8154 + 8 * (offset + count) ≤ r) →
            u.regs r = t.regs r := by
  intro count
  induction count with
  | zero =>
    intro offset t _ ht _
    exact ⟨t, rfl, by simpa only [Nat.add_zero] using ht,
      fun _ hlo hhi _ _ => (by omega : False).elim,
      fun _ hlo hhi _ _ => (by omega : False).elim, fun _ _ _ _ => rfl⟩
  | succ count ih =>
    intro offset t hRange ht hRaw
    let q : Fin 4 := ⟨offset, by omega⟩
    have hq : q.val = offset := rfl
    obtain ⟨s, hs, hS, hPack, hExponent, hFrame⟩ := firstPackedQuarterRun (l := l) (g := g)
      q (raw q) (values q) ht (hRaw q) (hEval q)
    have hPc : firstHardwarePc q + 56 = 4594 + 56 * (offset + 1) := by
      simp only [firstHardwarePc, hq]
      omega
    have hArgs (k : Fin 4) (i : Nat) (hi : i < 32) :
        s.regs (firstHardwareInput k + i) = some (raw k i) := by
      have hK := k.isLt
      rw [hFrame]
      · exact hRaw k i hi
      · right
        simp only [firstHardwareInput, firstHardwareOutput, hq]
        omega
      · left
        simp only [firstHardwareInput, firstPackScratch, hq]
        omega
      · left
        simp only [firstHardwareInput, firstPackedReg, hq]
        omega
    obtain ⟨u, hu, hU, hVals, hExps, hKeep⟩ := ih (offset + 1) s (by omega) (hPc ▸ hS) hArgs
    have hSteps : 56 + 56 * count = 56 * (count + 1) := by omega
    have hLen : offset + 1 + count = offset + (count + 1) := by omega
    refine ⟨u, by simpa only [hSteps] using run_comp hs hu,
      by simpa only [hLen] using hU, ?_, ?_, ?_⟩
    · intro k hlo hhi i hi
      by_cases h : k.val = offset
      · have hK : k = q := Fin.ext h
        subst k
        rw [hKeep]
        · exact hPack i hi
        · right
          simp only [firstPackedReg, hq]
          omega
        · right
          simp only [firstPackedReg, hq]
          omega
        · left
          simp only [firstPackedReg, hq]
          omega
      · exact hVals k (by omega) (by omega) i hi
    · intro k hlo hhi i hi
      by_cases h : k.val = offset
      · have hk : k = q := Fin.ext h
        subst k
        rw [hKeep]
        · exact hExponent i hi
        · left
          simp only [firstHardwareOutput, hq]
          omega
        · left
          simp only [firstHardwareOutput, hq]
          have := q.isLt
          omega
        · left
          simp only [firstHardwareOutput, hq]
          omega
      · exact hExps k (by omega) (by omega) i hi
    · intro r he hs' hp
      have he' : r < 1231 + 32 * (offset + 1) ∨
          1231 + 32 * (offset + 1 + count) ≤ r := by omega
      have hp' : r < 8154 + 8 * (offset + 1) ∨ 8154 + 8 * (offset + 1 + count) ≤ r := by
        rcases hp with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      rw [hKeep r he' hs' hp']
      apply hFrame
      · simp only [firstHardwareOutput, hq]
        rcases he with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      · simp only [firstPackScratch, hq]
        rcases hs' with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      · simp only [firstPackedReg, hq]
        rcases hp with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)

/-- All first-round hardware exponentials and probability packs run without advancing the
actual thread's event cursor. The continuation is the first store's unpack sequence. -/
theorem firstPackExponentLocal {g : Nat} {t : TState} {F : List (Nat × Value)}
    (raw : Fin 4 → Nat → Value) (values : Fin 4 → Nat → ℝ)
    (hEval : ∀ q i, i < 32 → ex2E true (raw q i) = .ok (.float .f32 (values q i)))
    (ht : At t 4594 F) (hRaw : ∀ q i, i < 32 → t.regs (firstHardwareInput q + i) = some (raw q i)) :
    ∃ u, At u 4818 [] ∧
      (∀ q : Fin 4, ∀ i < 8,
        u.regs (firstPackedReg q + i) = some (probabilityDoubleWord (values q) i)) ∧
      (∀ q : Fin 4, ∀ i < 32,
        u.regs (firstHardwareOutput q + i) = some (fl (values q i))) ∧
      (∀ r, (r < 1231 ∨ 1359 ≤ r) → (r < 3815 ∨ 3879 ≤ r) →
        (r < 8154 ∨ 8186 ≤ r) → u.regs r = t.regs r) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨u, hu, hU, hVals, hExps, hKeep⟩ := firstPackGroups (l := l) (g := g)
    raw values hEval 4 0 t (by decide) (ht.mono trivial) hRaw
  exact ⟨u, hU, fun q i hi => hVals q (Nat.zero_le _) q.isLt i hi,
    fun q i hi => hExps q (Nat.zero_le _) q.isLt i hi,
    hKeep, run_rtg hu⟩

end

variable {l : Launch} {g j : Nat} {X : Execution} {t : TState} {F : List (Nat × Value)}
    (raw : Fin 4 → Nat → Value) (values : Fin 4 → Nat → ℝ)
    (hEval : ∀ q i, i < 32 → ex2E true (raw q i) = .ok (.float .f32 (values q i)))
    (ht : At t 4594 F) (hRaw : ∀ q i, i < 32 → t.regs (firstHardwareInput q + i) = some (raw q i))
include raw values hEval ht hRaw

end
end PTX.Kernels.TmlFa4Fwd.Softmax
