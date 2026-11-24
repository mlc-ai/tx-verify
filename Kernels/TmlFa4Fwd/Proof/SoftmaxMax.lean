-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxShift
public import Lemmas.Flow.ReadRun

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- Negative infinity is the identity for the row maximum, including an empty support. -/
def maxScore : Option ℝ → Option ℝ → Option ℝ
  | none, y => y
  | some x, none => some x
  | some x, some y => some (max x y)

theorem maxScore_real (x y : Option ℝ) :
    scoreReal (maxScore x y) = max (scoreReal x) (scoreReal y) := by
  cases x <;> cases y <;> simp [maxScore, scoreReal, coe_max]

theorem maxScore_assoc (x y z : Option ℝ) :
    maxScore (maxScore x y) z = maxScore x (maxScore y z) := by
  cases x <;> cases y <;> cases z <;> simp [maxScore, max_assoc]

theorem maxScore_append (x y : List Nat) (score : Nat → Option ℝ) :
    (x ++ y).foldr (fun r z => maxScore (score r) z) none =
      maxScore (x.foldr (fun r z => maxScore (score r) z) none)
        (y.foldr (fun r z => maxScore (score r) z) none) := by
  induction x with
  | nil => rfl
  | cons r x ih =>
    simp only [List.cons_append, List.foldr_cons, ih]
    rw [maxScore_assoc]

theorem maxScore_mem (xs : List Nat) (score : Nat → Option ℝ) (v : EReal) :
    scoreReal (xs.foldr (fun r z => maxScore (score r) z) none) ≤ v ↔
      ∀ r ∈ xs, scoreReal (score r) ≤ v := by
  induction xs with
  | nil => simp [scoreReal]
  | cons r xs ih => simp [maxScore_real, ih]

theorem maxEEq (x y : Option ℝ) (z : Option (Option ℝ)) :
    maxE (scoreValue x :: scoreValue y :: z.toList.map scoreValue) =
      .ok (scoreValue (z.elim (maxScore x y) (maxScore (maxScore x y)))) := by
  cases z <;> unfold maxE <;>
    simp [idealMax, readScoreValue, bindRead, pure, Except.pure, ← maxScore_real, scoreReal_value]

/-- The support records the original scalar registers consumed by a decoded maximum. -/
structure MaxItem where
  dst : Nat
  left : Nat
  right : Nat
  third : Option Nat

def MaxItem.item (i : MaxItem) : RItem := .fmax i.dst i.left i.right i.third

def MaxItem.support (i : MaxItem) (deps : Nat → List Nat) : Nat → List Nat :=
  fun r => if r = i.dst then
    (deps i.left ++ deps i.right) ++ i.third.toList.flatMap deps else deps r

def maxSupport (items : List MaxItem) (deps : Nat → List Nat) : Nat → List Nat :=
  items.foldl (fun ds i => i.support ds) deps

def supportValues (score : Nat → Option ℝ) (deps : Nat → List Nat) (r : Nat) : Value :=
  scoreValue ((deps r).foldr (fun j z => maxScore (score j) z) none)

private theorem maxItemValue (score : Nat → Option ℝ) (deps : Nat → List Nat) (i : MaxItem) :
    i.item.cond (supportValues score deps) ∧
      i.item.upd (supportValues score deps) = supportValues score (i.support deps) := by
  rcases i with ⟨d, a, b, c⟩
  let w (r : Nat) := (deps r).foldr (fun j z => maxScore (score j) z) none
  have he : maxE (RItem.maxSrcs (supportValues score deps) a b c) =
      .ok (scoreValue ((c.map w).elim (maxScore (w a) (w b))
        (maxScore (maxScore (w a) (w b))))) := by
    have h := maxEEq (w a) (w b) (c.map w)
    cases c <;> simpa [RItem.maxSrcs, supportValues, w] using h
  refine ⟨⟨_, he⟩, ?_⟩
  funext r
  by_cases hr : r = d
  · subst r
    cases c <;> simp [MaxItem.item, MaxItem.support, RItem.upd, RItem.vals, supportValues,
      he, okVal, maxScore_append, maxScore_assoc, w, -List.foldr_append]
  · simp [MaxItem.item, MaxItem.support, RItem.upd, RItem.vals, supportValues, hr]

private theorem maxRunValues (score : Nat → Option ℝ) :
    ∀ (items : List MaxItem) (deps : Nat → List Nat),
      let V := supportValues score deps
      let ops := items.map MaxItem.item
      rReq V ops = true ∧ rCond V ops ∧
        rFinal V ops = supportValues score (maxSupport items deps)
  | [], _ => ⟨rfl, trivial, rfl⟩
  | i :: items, deps => by
    obtain ⟨hc, hu⟩ := maxItemValue score deps i
    obtain ⟨hr, hcs, hf⟩ := maxRunValues score items (i.support deps)
    change (true && rReq (i.item.upd _) _) = true ∧
      (i.item.cond _ ∧ rCond (i.item.upd _) _) ∧ rFinal (i.item.upd _) _ = _
    rw [hu]
    exact ⟨hr, ⟨hc, hcs⟩, hf⟩

def firstMaxSlice : List Instr := Decoded.code135 ++ Decoded.code136 ++ Decoded.code137

def firstMaxKernel : Kernel := { kernel with code := firstMaxSlice }

private theorem firstMaxSlice_eq :
    (Decoded.kernel.code.drop 4320).take 96 = firstMaxSlice := by kernel_rfl

def maxInstr (K : Kernel) (pc : Nat) : Option MaxItem := do
  let some ⟨none, .float f⟩ := K.code[pc]? | none
  let .max := f.op | none
  let [some d] := f.dsts | none
  match f.srcs with
  | [.reg a, .reg b] => some ⟨d, a, b, none⟩
  | [.reg a, .reg b, .reg c] => some ⟨d, a, b, some c⟩
  | _ => none

def firstMaxItems : List MaxItem := (List.range 66).filterMap (fun i =>
  maxInstr firstMaxKernel (9 + i))

def firstMaxInputs : List Nat :=
  (firstMaxItems.map MaxItem.item).foldl (fun srcs i =>
    srcs ++ i.reads.filter (fun r => !((firstMaxItems.map MaxItem.item).any (fun j =>
      j.writes.contains r)))) []

private theorem firstMaxLength : firstMaxItems.length = 66 := by decide +kernel

private theorem firstMaxReads : rReadsB firstMaxInputs (firstMaxItems.map MaxItem.item) = true := by
  decide +kernel

private theorem firstMaxVarying : rVaryingB (firstMaxItems.map MaxItem.item) = true := by
  decide +kernel

private theorem maxCodeOfSlice (K K' : Kernel) :
    ∀ (items : List MaxItem) (pc pc' : Nat),
      (∀ n < items.length, K.code[pc + n]? = K'.code[pc' + n]?) →
      rCodeB K pc (items.map MaxItem.item) = rCodeB K' pc' (items.map MaxItem.item)
  | [], _, _, _ => rfl
  | i :: items, pc, pc', hc => by
    have h₀ : K.code[pc]? = K'.code[pc']? := by simpa using hc 0 (by simp)
    have hi : i.item.codeB K pc = i.item.codeB K' pc' := by
      cases i with
      | mk d a b c => cases c <;> simp [MaxItem.item, RItem.codeB, h₀]
    simp only [List.map_cons, rCodeB, hi]
    rw [maxCodeOfSlice K K' items (pc + 1) (pc' + 1)]
    intro n hn
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1 n]
    exact hc _ (by simp only [List.length_cons]; omega)

private theorem firstMaxCode : rCodeB kernel 4329 (firstMaxItems.map MaxItem.item) = true := by
  rw [maxCodeOfSlice kernel firstMaxKernel firstMaxItems 4329 9]
  · decide +kernel
  · intro n hn
    rw [firstMaxLength] at hn
    change Decoded.kernel.code[4329 + n]? = firstMaxSlice[9 + n]?
    rw [← firstMaxSlice_eq, List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop]
    congr 1
    omega

private theorem noMaxLocalRule (items : List MaxItem) :
    NoItemRule Assumptions.all (items.map MaxItem.item) := by
  intro it hi hm
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hi
  cases i
  cases hm

theorem maxSeg {pc : Nat} (hpc : pc ∉ Assumptions.swExp2Sites) :
    SegFreePc Assumptions.all pc := by
  intro a ha l g t ht
  rcases List.mem_append.mp ha with ha | hInput
  · rcases List.mem_append.mp ha with ha | ha
    · exact Assumptions.numeric_segSites.pc hpc a ha l g t ht
    · simp only [Assumptions.synchronization, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> rfl
  · obtain rfl := List.mem_singleton.mp hInput
    rfl

variable {l : Launch} {g : Nat} {t : TState}

theorem maxModel (hpc : t.pc ∉ Assumptions.swExp2Sites) :
    IdealAt Assumptions.all (.max .f32) l g t ∧ DeclineAt Assumptions.all (.max .f32) l g t := by
  have hSeg := (Assumptions.numeric_segSites.pc hpc)
  refine ⟨?_, ?_⟩
  · intro op hForm u hLocal
    rw [Assumptions.execLocalA_all_eq_numeric]
    exact (idealAt_head (by decide) hSeg.tail : IdealAt Assumptions.numeric (.max .f32) l g t)
      op hForm u hLocal
  · intro op hForm hd
    rw [Assumptions.execLocalA_all_eq_numeric]
    apply declineAt_head _ hSeg.tail op hForm hd
    intro a ha op hForm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · apply approxExact_localRule_none
      intro f hf
      rw [approxForm_none_of_max hForm] at hf
      cases hf
    · have hLog : Assumptions.lg2Operands op = none := by
        cases op <;> try rfl
        rename_i f
        cases h : f.op <;> simp [Assumptions.lg2Operands, h]
        simp [FloatForm.ofOp, h] at hForm
      simp [Assumptions.lg2, hLog]
    · cases op <;> try rfl
      rename_i c
      simp only [FloatForm.ofOp] at hForm
      split_ifs at hForm <;> cases hForm
    · rfl

private theorem firstMaxOff {n : Nat} (hn : n < 66) : 4329 + n ∉ Assumptions.swExp2Sites := by
  simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
  omega

def maxLeaves : List Nat := maxSupport firstMaxItems (fun r => [r]) 7256

private theorem firstMaxLeaves : maxLeaves.all firstMaxInputs.contains = true ∧
    firstMaxInputs.all maxLeaves.contains = true := by
  constructor <;> kernel_rfl

/-- The first row reduction runs all 66 maximum instructions in the frozen program.
Register 7256 bounds the 128 incoming masked score registers, with equality to their maximum. -/
theorem firstMaxLocal (score : Nat → Option ℝ) (ht : At t 4329 [])
    (hIn : ∀ r ∈ firstMaxInputs, t.regs r = some (scoreValue (score r))) :
    ∃ (u : TState) (mx : Option ℝ), At u 4395 [(7256, scoreValue mx)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ v : EReal, scoreReal mx ≤ v ↔ ∀ r ∈ firstMaxInputs, scoreReal (score r) ≤ v) ∧
      ∀ r, r ∉ rWrites (firstMaxItems.map MaxItem.item) → u.regs r = t.regs r := by
  let ops := firstMaxItems.map MaxItem.item
  have hLen : ops.length = 66 := by simp [ops, firstMaxLength]
  have off (n) (hn : n < ops.length) : t.pc + n ∉ Assumptions.swExp2Sites := by
    rw [ht.1]
    exact firstMaxOff (by rwa [hLen] at hn)
  obtain ⟨hReq, hCond, hVal⟩ := maxRunValues score firstMaxItems (fun r => [r])
  obtain ⟨u, hRun, hPc, hSub, hAcc, hFault, hFrame, hRegs⟩ :=
    (rRun (K := kernel) (A := Assumptions.all) (L := l) (g := g) ops
      (supportValues score (fun r => [r])) firstMaxInputs t (ht.1 ▸ firstMaxCode) ht.2.2.2.1
      (fun r hm => by cases hs : score r <;> simpa [supportValues, maxScore, hs] using hIn r hm)
      firstMaxReads hReq firstMaxVarying (noMaxLocalRule firstMaxItems)
      (fun n hn => maxSeg (off n hn))
      (fun n hn s hs => (maxModel (hs ▸ off n hn)).1)
      (fun n hn s hs => (maxModel (hs ▸ off n hn)).2)).1 hCond
  let mx := maxLeaves.foldr (fun r z => maxScore (score r) z) none
  have hResult := hRegs 7256 (List.mem_append_left _ (by decide +kernel : 7256 ∈ rWrites ops))
  change u.regs 7256 = some (rFinal _ (firstMaxItems.map MaxItem.item) 7256) at hResult
  rw [hVal] at hResult
  refine ⟨u, mx, ⟨by rw [hPc, ht.1, hLen], hSub.trans ht.2.1, hAcc.trans ht.2.2.1,
    hFault.trans ht.2.2.2.1, hResult, trivial⟩, run_rtg hRun, ?_, hFrame⟩
  intro v
  rw [maxScore_mem]
  exact ⟨fun h r hm => h r (by
      simpa only [List.contains_eq_mem, decide_eq_true_eq] using
        List.all_eq_true.mp firstMaxLeaves.2 r hm), fun h r hm => h r (by
      simpa only [List.contains_eq_mem, decide_eq_true_eq] using
        List.all_eq_true.mp firstMaxLeaves.1 r hm)⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
