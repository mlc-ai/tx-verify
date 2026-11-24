-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreNumeric
public import Lemmas.Flow.ContinuingEvent
public import Tactics.KernelRfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Assumption

noncomputable section

/-- Consecutive affine score instructions in the first, biased and unbiased rounds. -/
structure ShiftLayout where
  sliceStart : Nat
  sliceLength : Nat
  offset : Nat
  width : Nat
  scaleReg : Nat
  addReg : Nat

def shiftLayout : Fin 3 → ShiftLayout :=
  ![⟨4352, 256, 51, 191, 8026, 8024⟩, ⟨5664, 160, 23, 128, 8445, 8444⟩,
    ⟨6880, 160, 14, 128, 8692, 8691⟩]

def shiftStart (round : Fin 3) : Nat :=
  (shiftLayout round).sliceStart + (shiftLayout round).offset

def shiftEnd (round : Fin 3) : Nat := shiftStart round + (shiftLayout round).width

def shiftSlice (round : Fin 3) : List Instr :=
  ![Decoded.code136 ++ Decoded.code137 ++ Decoded.code138 ++ Decoded.code139 ++
      Decoded.code140 ++ Decoded.code141 ++ Decoded.code142 ++ Decoded.code143,
    Decoded.code177 ++ Decoded.code178 ++ Decoded.code179 ++ Decoded.code180 ++ Decoded.code181,
    Decoded.code215 ++ Decoded.code216 ++ Decoded.code217 ++
      Decoded.code218 ++ Decoded.code219] round

private theorem shiftSlice_eq (round : Fin 3) :
    (Decoded.kernel.code.drop (shiftLayout round).sliceStart).take
      (shiftLayout round).sliceLength = shiftSlice round := by
  fin_cases round <;> kernel_rfl

def shiftKernel (round : Fin 3) : Kernel :=
  { Decoded.kernel with code :=
      ((shiftSlice round).drop (shiftLayout round).offset).take (shiftLayout round).width }

def shiftItemAt (K : Kernel) (pc : Nat) (hasPack : Bool) : Option FmaItem := do
  let pk ← if hasPack then do
    let some ⟨none, .move ⟨.pack, .int .b 64, [some _], [.reg lo, .reg hi]⟩⟩ :=
      K.code[pc]? | none
    pure (some (lo, hi))
    else pure none
  let atFma := pc + if hasPack then 1 else 0
  let some ⟨none, .float f⟩ := K.code[atFma]? | none
  let [some q] := f.dsts | none
  let [.reg a, _, _] := f.srcs | none
  let some ⟨none, .move ⟨.unpack, .int .b 64, [some x, some y], [.reg _]⟩⟩ :=
    K.code[atFma + 1]? | none
  return ⟨pk, a, q, x, y⟩

/-- Each round has 64 pairs. The repeated rounds receive already packed operands. -/
def shiftItems (round : Fin 3) : List FmaItem :=
  (List.range 64).filterMap fun i =>
    let hasPack := round.val == 0 && i != 0
    let pc := if hasPack then 2 + 3 * (i - 1) else 2 * i
    shiftItemAt (shiftKernel round) pc hasPack

theorem shiftLength (round : Fin 3) : (shiftItems round).length = 64 := by
  fin_cases round <;> decide +kernel

private theorem shiftFuel (round : Fin 3) :
    fmaLen (shiftItems round) = (shiftLayout round).width := by
  fin_cases round <;> decide +kernel

private theorem codeB_congr {K K' : Kernel} {c z pc pc' : Nat} {it : FmaItem}
    (h : ∀ i < it.len, K.code[pc + i]? = K'.code[pc' + i]?) :
    it.codeB K c z pc = it.codeB K' c z pc' := by
  have hp : 2 ≤ it.len := by unfold FmaItem.len; split <;> decide
  have he₀ : K.code[pc]? = K'.code[pc']? := by simpa using h 0 (by omega)
  unfold FmaItem.codeB
  rw [he₀, h _ (by omega), h _ (by omega)]

private theorem fmaCodeB_congr {K K' : Kernel} {c z : Nat} :
    ∀ (items : List FmaItem) (pc pc' : Nat),
      (∀ i < fmaLen items, K.code[pc + i]? = K'.code[pc' + i]?) →
      fmaCodeB K c z pc items = fmaCodeB K' c z pc' items
  | [], _, _, _ => rfl
  | it :: items, pc, pc', h => by
    simp only [fmaCodeB]
    rw [codeB_congr (fun i hi => h i (by simp only [fmaLen]; omega))]
    rw [fmaCodeB_congr items (pc + it.len) (pc' + it.len) (fun i hi => by
      rw [Nat.add_assoc, Nat.add_assoc]
      exact h _ (by simp only [fmaLen]; omega))]

private theorem shiftCode (round : Fin 3) :
    fmaCodeB kernel (shiftLayout round).scaleReg (shiftLayout round).addReg
      (shiftStart round) (shiftItems round) = true := by
  have hBound : (shiftLayout round).offset + (shiftLayout round).width ≤
      (shiftLayout round).sliceLength := by fin_cases round <;> decide
  have h (i : Nat) (hi : i < fmaLen (shiftItems round)) :
      kernel.code[shiftStart round + i]? = (shiftKernel round).code[0 + i]? := by
    rw [shiftFuel] at hi
    change Decoded.kernel.code[shiftStart round + i]? =
      (((shiftSlice round).drop (shiftLayout round).offset).take (shiftLayout round).width)[0 + i]?
    rw [Nat.zero_add, List.getElem?_take, ite_eq_left hi, List.getElem?_drop,
      ← shiftSlice_eq, List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop]
    simp only [shiftStart, Nat.add_assoc]
  rw [fmaCodeB_congr (shiftItems round) (shiftStart round) 0 h]
  fin_cases round <;> decide +kernel

private theorem shiftNoOverwrite (round : Fin 3) :
    ((shiftItems round).flatMap FmaItem.writes).Nodup := by
  fin_cases round <;> decide +kernel

private theorem shiftDisjoint (round : Fin 3) :
    ((shiftItems round).flatMap FmaItem.writes).all
      (fun w => w != (shiftLayout round).scaleReg && w != (shiftLayout round).addReg &&
        !((shiftItems round).flatMap FmaItem.reads).contains w) = true := by
  fin_cases round <;> decide +kernel

private theorem shiftSourcesApart (round : Fin 3) :
    (shiftItems round).all (fun it => it.a != (shiftLayout round).scaleReg &&
      it.a != (shiftLayout round).addReg) = true := by
  fin_cases round <;> decide +kernel

variable {l : Launch} {g : Nat} {t : TState}

/-- The decoded affine shifts preserve both score masks and shift each finite score by the
supplied scale and reference offset. The continuation is the same thread trace. -/
theorem shiftTraceOfSplitLocal {scale offset : ℝ} (round : Fin 3) (hs : 0 < scale) (v : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) (hPc : t.pc = shiftStart round) (hf : t.fault = none)
    (hRead : ∀ it ∈ shiftItems round, ∀ r ∈ it.reads, t.regs r = some (v r))
    (hSource : ∀ it ∈ shiftItems round, it.packOk v = true ∧
      splitValue 64 (it.src v) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hScale : readERealPair l g t (.reg (shiftLayout round).scaleReg) =
      some (.ok ((scale : EReal), (scale : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout round).addReg) =
      some (.ok ((offset : EReal), (offset : EReal)))) :
    ∃ u, u.pc = shiftEnd round ∧ u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ r ∉ (shiftItems round).flatMap FmaItem.writes, u.regs r = t.regs r) ∧
      ∀ it ∈ shiftItems round,
        u.regs it.x = some (scoreValue (affineScore scale offset (scores it).1)) ∧
        u.regs it.y = some (scoreValue (affineScore scale offset (scores it).2)) := by
  have hDis (it : FmaItem) (hit : it ∈ shiftItems round) (r : Nat) (hw : r ∈ it.writes) :
      r ≠ (shiftLayout round).scaleReg ∧ r ≠ (shiftLayout round).addReg ∧
        ∀ other ∈ shiftItems round, r ∉ other.reads := by
    have h := List.all_eq_true.mp (shiftDisjoint round) r (List.mem_flatMap.mpr ⟨it, hit, hw⟩)
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact ⟨h.1.1, h.1.2, fun j hj hRead => h.2 (List.mem_flatMap.mpr ⟨j, hj, hRead⟩)⟩
  have hApart (it : FmaItem) (hit : it ∈ shiftItems round) :
      it.a ≠ (shiftLayout round).scaleReg ∧ it.a ≠ (shiftLayout round).addReg := by
    simpa only [Bool.and_eq_true, bne_iff_ne] using
      List.all_eq_true.mp (shiftSourcesApart round) it hit
  have hLocal (n : Nat) (hn : n < fmaLen (shiftItems round)) :
      t.pc + n ∉ Assumptions.swExp2Sites := by
    rw [hPc]
    rw [shiftFuel] at hn
    fin_cases round
    · change n < 191 at hn
      change 4403 + n ∉ Assumptions.swExp2Sites
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · change n < 128 at hn
      change 5687 + n ∉ Assumptions.swExp2Sites
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · change n < 128 at hn
      change 6894 + n ∉ Assumptions.swExp2Sites
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
  obtain ⟨u, hu, hU, hUF, hSub, hAcc, hFrame, hOut⟩ :=
    maskedFmaRunOfSplit hs v scores (shiftItems round) t (hPc ▸ shiftCode round) hf hRead hSource
      hScale hOffset hDis hApart (shiftNoOverwrite round) hLocal
  rw [hPc, shiftFuel] at hU
  exact ⟨u, hU, hUF, hSub, hAcc, run_rtg hu, hFrame, hOut⟩

theorem shiftTraceOfSplitInPrefix {es : List Event} {ending : Option TState} {scale offset : ℝ}
    (round : Fin 3) (hs : 0 < scale) (v : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ)
    (hPc : t.pc = shiftStart round) (hf : t.fault = none)
    (hRead : ∀ it ∈ shiftItems round, ∀ r ∈ it.reads, t.regs r = some (v r))
    (hSource : ∀ it ∈ shiftItems round, it.packOk v = true ∧
      splitValue 64 (it.src v) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hScale : readERealPair l g t (.reg (shiftLayout round).scaleReg) =
      some (.ok ((scale : EReal), (scale : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout round).addReg) =
      some (.ok ((offset : EReal), (offset : EReal))))
    (hr : Run kernel Assumptions.all l g t es ending) (hne : es ≠ []) :
    ∃ u, u.pc = shiftEnd round ∧ u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      Run kernel Assumptions.all l g u es ending ∧
      (∀ r ∉ (shiftItems round).flatMap FmaItem.writes, u.regs r = t.regs r) ∧
      ∀ it ∈ shiftItems round,
        u.regs it.x = some (scoreValue (affineScore scale offset (scores it).1)) ∧
        u.regs it.y = some (scoreValue (affineScore scale offset (scores it).2)) := by
  obtain ⟨u,hU,hF,hSub,hAcc,hLocal,hFrame,hOut⟩ :=
    shiftTraceOfSplitLocal round hs v scores hPc hf hRead hSource hScale hOffset
  exact ⟨u,hU,hF,hSub,hAcc,hr.after_local_nonempty hLocal hne,hFrame,hOut⟩

theorem shiftTraceOfSplit {es : List Event} {scale offset : ℝ} (round : Fin 3) (hs : 0 < scale)
    (v : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ) (hPc : t.pc = shiftStart round)
    (hf : t.fault = none) (hRead : ∀ it ∈ shiftItems round, ∀ r ∈ it.reads, t.regs r = some (v r))
    (hSource : ∀ it ∈ shiftItems round, it.packOk v = true ∧
      splitValue 64 (it.src v) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hScale : readERealPair l g t (.reg (shiftLayout round).scaleReg) =
      some (.ok ((scale : EReal), (scale : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout round).addReg) =
      some (.ok ((offset : EReal), (offset : EReal))))
    (hr : Run kernel Assumptions.all l g t es none) :
    ∃ u, u.pc = shiftEnd round ∧ u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      Run kernel Assumptions.all l g u es none ∧
      (∀ r ∉ (shiftItems round).flatMap FmaItem.writes, u.regs r = t.regs r) ∧
      ∀ it ∈ shiftItems round,
        u.regs it.x = some (scoreValue (affineScore scale offset (scores it).1)) ∧
        u.regs it.y = some (scoreValue (affineScore scale offset (scores it).2)) := by
  apply shiftTraceOfSplitInPrefix round hs v scores hPc hf hRead hSource hScale hOffset hr
  intro hEmpty
  rw [hEmpty] at hr
  cases hr

theorem shiftTraceLocal {scale offset : ℝ} (round : Fin 3) (hs : 0 < scale) (v : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) (hPc : t.pc = shiftStart round) (hf : t.fault = none)
    (hRead : ∀ it ∈ shiftItems round, ∀ r ∈ it.reads, t.regs r = some (v r))
    (hSource : ∀ it ∈ shiftItems round, it.packOk v = true ∧
      it.src v = joinValue (scoreValue (scores it).1) (scoreValue (scores it).2))
    (hScale : readERealPair l g t (.reg (shiftLayout round).scaleReg) =
      some (.ok ((scale : EReal), (scale : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout round).addReg) =
      some (.ok ((offset : EReal), (offset : EReal)))) :
    ∃ u, u.pc = shiftEnd round ∧ u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ r ∉ (shiftItems round).flatMap FmaItem.writes, u.regs r = t.regs r) ∧
      ∀ it ∈ shiftItems round,
        u.regs it.x = some (scoreValue (affineScore scale offset (scores it).1)) ∧
        u.regs it.y = some (scoreValue (affineScore scale offset (scores it).2)) :=
  shiftTraceOfSplitLocal round hs v scores hPc hf hRead (fun it hi =>
      ⟨(hSource it hi).1,by rw [(hSource it hi).2]; exact splitScorePair _ _⟩) hScale hOffset

theorem shiftTraceInPrefix {es : List Event} {ending : Option TState} {scale offset : ℝ}
    (round : Fin 3) (hs : 0 < scale) (v : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ)
    (hPc : t.pc = shiftStart round) (hf : t.fault = none)
    (hRead : ∀ it ∈ shiftItems round, ∀ r ∈ it.reads, t.regs r = some (v r))
    (hSource : ∀ it ∈ shiftItems round, it.packOk v = true ∧
      it.src v = joinValue (scoreValue (scores it).1) (scoreValue (scores it).2))
    (hScale : readERealPair l g t (.reg (shiftLayout round).scaleReg) =
      some (.ok ((scale : EReal), (scale : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout round).addReg) =
      some (.ok ((offset : EReal), (offset : EReal))))
    (hr : Run kernel Assumptions.all l g t es ending) (hne : es ≠ []) :
    ∃ u, u.pc = shiftEnd round ∧ u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      Run kernel Assumptions.all l g u es ending ∧
      (∀ r ∉ (shiftItems round).flatMap FmaItem.writes, u.regs r = t.regs r) ∧
      ∀ it ∈ shiftItems round,
        u.regs it.x = some (scoreValue (affineScore scale offset (scores it).1)) ∧
        u.regs it.y = some (scoreValue (affineScore scale offset (scores it).2)) :=
  shiftTraceOfSplitInPrefix round hs v scores hPc hf hRead (fun it hi =>
      ⟨(hSource it hi).1,by rw [(hSource it hi).2]; exact splitScorePair _ _⟩) hScale hOffset hr hne

theorem shiftTrace {es : List Event} {scale offset : ℝ} (round : Fin 3) (hs : 0 < scale)
    (v : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ) (hPc : t.pc = shiftStart round)
    (hf : t.fault = none) (hRead : ∀ it ∈ shiftItems round, ∀ r ∈ it.reads, t.regs r = some (v r))
    (hSource : ∀ it ∈ shiftItems round, it.packOk v = true ∧
      it.src v = joinValue (scoreValue (scores it).1) (scoreValue (scores it).2))
    (hScale : readERealPair l g t (.reg (shiftLayout round).scaleReg) =
      some (.ok ((scale : EReal), (scale : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout round).addReg) =
      some (.ok ((offset : EReal), (offset : EReal))))
    (hr : Run kernel Assumptions.all l g t es none) :
    ∃ u, u.pc = shiftEnd round ∧ u.fault = none ∧ u.sub = t.sub ∧ u.acc = t.acc ∧
      Run kernel Assumptions.all l g u es none ∧
      (∀ r ∉ (shiftItems round).flatMap FmaItem.writes, u.regs r = t.regs r) ∧
      ∀ it ∈ shiftItems round,
        u.regs it.x = some (scoreValue (affineScore scale offset (scores it).1)) ∧
        u.regs it.y = some (scoreValue (affineScore scale offset (scores it).2)) :=
  shiftTraceOfSplit round hs v scores hPc hf hRead (fun it hi =>
      ⟨(hSource it hi).1,by rw [(hSource it hi).2]; exact splitScorePair _ _⟩) hScale hOffset hr

end
end PTX.Kernels.TmlFa4Fwd.Softmax
