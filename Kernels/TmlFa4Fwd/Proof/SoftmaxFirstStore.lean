-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstPack
public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
public import Lemmas.Flow.FmaRun

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

def firstUnpackPc (quarter : Fin 4) : Nat :=
  (#v[4818, 4827, 4836, 4848] : Vector Nat 4)[quarter]

def firstUnpackBase (quarter : Fin 4) : Nat :=
  3879 + 16 * quarter.val + if quarter.val = 3 then 1 else 0

private def unpackSrc (quarter : Fin 4) (word : Nat) : Nat :=
  firstPackedReg quarter + (7 - word)

private def unpackDst (quarter : Fin 4) (word : Nat) : Nat :=
  firstUnpackBase quarter + 2 * word

private def unpackInstr (quarter : Fin 4) (word : Nat) : MoveInstr :=
  ⟨.unpack, .int .b 64, [some (unpackDst quarter word), some (unpackDst quarter word + 1)],
    [.reg (unpackSrc quarter word)]⟩

private def unpackCheck (quarter : Fin 4) (word : Nat) : Bool :=
  match kernel.code[firstUnpackPc quarter + word]? with
  | some ⟨none, .move m⟩ => decide (m = unpackInstr quarter word)
  | _ => false

set_option maxRecDepth 100000 in
private theorem unpackTable (quarter : Fin 4) :
    (List.range 8).all (unpackCheck quarter) = true := by
  fin_cases quarter <;> kernel_rfl

private theorem unpackCode (quarter : Fin 4) (word : Fin 8) :
    kernel.code[firstUnpackPc quarter + word.val]? =
      some ⟨none, .move (unpackInstr quarter word.val)⟩ := by
  have h := List.all_eq_true.mp (unpackTable quarter) word.val (List.mem_range.mpr word.isLt)
  unfold unpackCheck at h
  split at h
  · rename_i m hm
    rw [hm, of_decide_eq_true h]
  · cases h

private theorem unpackPcBound (quarter : Fin 4) : firstUnpackPc quarter ≤ 4848 := by
  fin_cases quarter <;> decide

private theorem unpackBaseBound (quarter : Fin 4) : firstUnpackBase quarter ≤ 3928 := by
  fin_cases quarter <;> decide

private theorem unpackEnd (quarter : Fin 4) :
    firstUnpackPc quarter + 8 = probabilityPc .first quarter := by
  fin_cases quarter <;> decide

private theorem firstUnpackInterval {l : Launch} {g : Nat}
    (quarter : Fin 4) (exponents : Nat → ℝ) :
    ∀ (count offset : Nat) (t : TState), offset + count ≤ 8 →
      At t (firstUnpackPc quarter + offset) [] →
      (∀ j < 8, t.regs (firstPackedReg quarter + j) = some (probabilityDoubleWord exponents j)) →
      ∃ u, run kernel Assumptions.all l g count t = some u ∧
        At u (firstUnpackPc quarter + (offset + count)) [] ∧
        (∀ j, offset ≤ j → j < offset + count →
          u.regs (unpackDst quarter j) = some (probabilityWord exponents (2 * (7 - j))) ∧
          u.regs (unpackDst quarter j + 1) = some (probabilityWord exponents (2 * (7 - j) + 1))) ∧
        ∀ r, r < unpackDst quarter offset ∨ unpackDst quarter (offset + count) ≤ r →
          u.regs r = t.regs r := by
  intro count
  induction count with
  | zero =>
    intro offset t _ ht _
    exact ⟨t, rfl, by simpa only [Nat.add_zero] using ht,
      fun _ hlo hhi => (by omega : False).elim, fun _ _ => rfl⟩
  | succ count ih =>
    intro offset t hRange ht hInput
    have hOffset : offset < 8 := by omega
    have hPC := unpackPcBound quarter
    have hBase := unpackBaseBound quarter
    let low := probabilityWord exponents (2 * (7 - offset))
    let high := probabilityWord exponents (2 * (7 - offset) + 1)
    let s := next (setReg (setReg t (unpackDst quarter offset) low)
      (unpackDst quarter offset + 1) high)
    have hSrc : t.regs (unpackSrc quarter offset) = some (.pair low high) :=
      hInput (7 - offset) (by omega)
    have hOff : t.pc ∉ Assumptions.swExp2Sites := by
      rw [ht.1]
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hs : run kernel Assumptions.all l g 1 t = some s := by
      apply run_local (unpackCode quarter ⟨offset, hOffset⟩) rfl ht
      rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
      exact exec_unpack64 (A := []) hSrc rfl rfl SegFreePc.nil (by simp [NoUnpack64])
    have hState : At s (firstUnpackPc quarter + (offset + 1)) [] := by
      refine ⟨?_, ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
      change t.pc + 1 = _
      rw [ht.1]
      omega
    have hFrame (r : Nat) (h0 : r ≠ unpackDst quarter offset)
        (h1 : r ≠ unpackDst quarter offset + 1) :
        s.regs r = t.regs r := by
      simp only [s, next, setReg, Function.update_of_ne h0, Function.update_of_ne h1]
    have hArgs (j : Nat) (hj : j < 8) :
        s.regs (firstPackedReg quarter + j) = some (probabilityDoubleWord exponents j) := by
      rw [hFrame]
      · exact hInput j hj
      all_goals unfold unpackDst firstPackedReg; omega
    obtain ⟨u, hu, hU, hOut, hKeep⟩ := ih (offset + 1) s (by omega) hState hArgs
    have hLen : offset + 1 + count = offset + (count + 1) := by omega
    refine ⟨u, by simpa only [Nat.add_comm 1 count] using run_comp hs hu,
      by simpa only [hLen] using hU, ?_, ?_⟩
    · intro j hlo hhi
      by_cases h : j = offset
      · subst j
        have hLow : s.regs (unpackDst quarter offset) = some low := by
          simp [s, next, setReg]
        have hHigh : s.regs (unpackDst quarter offset + 1) = some high := Function.update_self ..
        exact ⟨(hKeep _ (.inl (by unfold unpackDst; omega))).trans hLow,
          (hKeep _ (.inl (by unfold unpackDst; omega))).trans hHigh⟩
      · exact hOut j (by omega) (by omega)
    · intro r hR
      have hRest : r < unpackDst quarter (offset + 1) ∨
          unpackDst quarter (offset + 1 + count) ≤ r := by
        unfold unpackDst at *
        rcases hR with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      have hn0 : r ≠ unpackDst quarter offset := by unfold unpackDst at *; omega
      have hn1 : r ≠ unpackDst quarter offset + 1 := by unfold unpackDst at *; omega
      exact (hKeep r hRest).trans (hFrame r hn0 hn1)

private def firstPStoreWords (quarter : Fin 4) : List Opnd :=
  (List.range 16).map fun word => .reg (unpackDst quarter (7 - word / 2) + word % 2)

private theorem firstPStoreCode (quarter : Fin 4) :
    kernel.code[probabilityPc .first quarter]? = some
      ⟨none, .tcSt (probabilityReg .first quarter) (firstPStoreWords quarter) .s32x32b⟩ := by
  fin_cases quarter
  · exact Flow.code_4826
  · exact Flow.code_4835
  · exact Flow.code_4844
  · exact Flow.code_4856

private theorem storeWordsRead {l : Launch} {g : Nat} {t : TState}
    (quarter : Fin 4) (exponents : Nat → ℝ)
    (h : ∀ j < 8,
      t.regs (unpackDst quarter j) = some (probabilityWord exponents (2 * (7 - j))) ∧
      t.regs (unpackDst quarter j + 1) = some (probabilityWord exponents (2 * (7 - j) + 1))) :
    (firstPStoreWords quarter).mapM (readValue l g t 32) =
      .ok ((List.range 16).map (probabilityWord exponents)) := by
  unfold firstPStoreWords
  rw [List.mapM_map]
  let eval := fun word => readValue l g t 32 (.reg (unpackDst quarter (7 - word / 2) + word % 2))
  have hWord (word : Nat) (hw : word ∈ List.range 16) :
      eval word = .ok (probabilityWord exponents word) := by
    have hLimit := List.mem_range.mp hw
    have hIndex : 7 - word / 2 < 8 := by omega
    obtain ⟨h0, h1⟩ := h _ hIndex
    have hEq : 7 - (7 - word / 2) = word / 2 := by omega
    rw [hEq] at h0 h1
    have hMod : word % 2 = 0 ∨ word % 2 = 1 := by omega
    rcases hMod with hM | hM
    · have hE : 2 * (word / 2) = word := by omega
      simp [eval, hM, readValue, readReg, h0, hE, pure, Except.pure]
    · have hE : 2 * (word / 2) + 1 = word := by omega
      simp [eval, hM, readValue, readReg, h1, hE, pure, Except.pure]
  change (List.range 16).mapM eval = _
  generalize hh : List.range 16 = words at hWord ⊢
  clear hh
  induction words with
  | nil => rfl
  | cons word rest ih =>
    rw [List.mapM_cons, hWord word (by simp), List.map_cons]
    have hh := ih (fun w hw => hWord w (by simp [hw]))
    change ((rest.mapM eval).bind fun ws => .ok (probabilityWord exponents word :: ws)) = _
    rw [hh]
    rfl

/-- The eight unpack instructions are a local prefix of the first probability store. -/
theorem probabilityUnpackLocal {l : Launch} {g : Nat} {t : TState} (quarter : Fin 4)
    (exponents : Nat → ℝ) (ht : At t (firstUnpackPc quarter) [])
    (hPacked : ∀ word < 8, t.regs (firstPackedReg quarter+word) =
      some (probabilityDoubleWord exponents word)) :
    ∃ u, At u (probabilityPc .first quarter) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ j < 8,
        u.regs (firstUnpackBase quarter+2*j) = some (probabilityWord exponents (2*(7-j))) ∧
        u.regs (firstUnpackBase quarter+2*j+1) = some (probabilityWord exponents (2*(7-j)+1))) ∧
      ∀ r, r < firstUnpackBase quarter ∨ firstUnpackBase quarter+16 ≤ r → u.regs r = t.regs r := by
  obtain ⟨u,hRun,hU,hWords,hFrame⟩ :=
    firstUnpackInterval (l := l) (g := g) quarter exponents 8 0 t (by decide) ht hPacked
  exact ⟨u,unpackEnd quarter ▸ hU,run_rtg hRun,fun j hj => hWords j (Nat.zero_le j) hj,hFrame⟩

/-- The unpacked probability words determine the concrete Tensor Memory store event. -/
theorem packedProbabilityStoreTemplate {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (stage : Fin 2) (quarter : Fin 4) {g : Nat} {t : TState}
    (values : Nat → ℝ) (hPc : t.pc = probabilityPc .first quarter) (hFault : t.fault = none)
    (hSub : t.sub = if delayedProbability .first quarter then 1 else 0)
    (hAddr : t.regs (probabilityReg .first quarter) =
      some (b32 (probabilityAddress l g stage quarter)))
    (hWords : ∀ j < 8,
      t.regs (firstUnpackBase quarter+2*j) = some (probabilityWord values (2*(7-j))) ∧
      t.regs (firstUnpackBase quarter+2*j+1) = some (probabilityWord values (2*(7-j)+1))) :
    out kernel Assumptions.all l g t =
      .ev (.tc (.st (probabilityAddress l g stage quarter)
        ((List.range 16).map (probabilityWord values)) .s32x32b) (next {t with sub := 0})) := by
  apply probabilityStoreTemplate hp .first quarter stage hPc hFault hSub (firstPStoreCode quarter)
    hAddr (storeWordsRead quarter values hWords)
  apply List.all_eq_true.mpr
  intro word hw
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hw
  rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (stage : Fin 2)
include hp stage

/-- Every first-round P store unpacks eight double words in reverse register visit order,
and writes the 16 resulting probability words in ascending score-column order. -/
theorem packedQuarterStoreTrace (quarter : Fin 4) {g j : Nat} {t : TState} (exponents : Nat → ℝ)
    (ht : At t (firstUnpackPc quarter) [])
    (hPacked : ∀ word < 8, t.regs (firstPackedReg quarter + word) =
      some (probabilityDoubleWord exponents word))
    (hAddr : t.regs (probabilityReg .first quarter) =
      some (b32 (probabilityAddress l g stage quarter)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pc := probabilityPc .first quarter
    let k := if delayedProbability .first quarter then j + 1 else j
    ∃ u, (delayedProbability .first quarter = true → X.get (g, j) = some ⟨pc, .tc .waitLd⟩) ∧
      X.get (g, k) = some ⟨pc, .tc (.st (probabilityAddress l g stage quarter)
          ((List.range 16).map (probabilityWord exponents)) .s32x32b)⟩ ∧
      At u (pc + 1) [] ∧
      (∀ r, r < firstUnpackBase quarter ∨ firstUnpackBase quarter + 16 ≤ r → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (k + 1)) none := by
  obtain ⟨u, hu, hU, hOut, hFrame⟩ := firstUnpackInterval (l := l) (g := g)
    quarter exponents 8 0 t (by decide) ht hPacked
  have hRead := storeWordsRead (l := l) (g := g) quarter exponents
    (fun w hw => hOut w (Nat.zero_le _) hw)
  have hWidth : ((List.range 16).map (probabilityWord exponents)).all (·.bytes = 4) = true := by
    apply List.all_eq_true.mpr
    intro value hValue
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hValue
    rfl
  have hSmall : probabilityReg .first quarter < unpackDst quarter 0 := by
    fin_cases quarter <;> decide
  have hr : u.regs (probabilityReg .first quarter) =
      some (b32 (probabilityAddress l g stage quarter)) :=
    (hFrame _ (.inl hSmall)).trans hAddr
  have hU' : At u (probabilityPc .first quarter) [] := unpackEnd quarter ▸ hU
  obtain ⟨hWait, hStore, hTail⟩ := probabilityTrace hp .first quarter stage
    hU'.1 hU'.2.2.2.1 hU'.2.1 (firstPStoreCode quarter) hr hRead hWidth
      (hRun.after_local (run_rtg hu))
  exact ⟨next u, by simpa only [hU'.1] using hWait, by simpa only [hU'.1] using hStore,
    hU'.next, hFrame, hTail⟩

/-- Every first-round P store unpacks eight double words in reverse register visit order,
and writes the 16 resulting probability words in ascending score-column order. -/
theorem packedQuarterStoreInPrefix (quarter : Fin 4) {g j : Nat} {t : TState}
    {ending : Option TState} (exponents : Nat → ℝ) (ht : At t (firstUnpackPc quarter) [])
    (hPacked : ∀ word < 8, t.regs (firstPackedReg quarter + word) =
      some (probabilityDoubleWord exponents word))
    (hAddr : t.regs (probabilityReg .first quarter) =
      some (b32 (probabilityAddress l g stage quarter)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hRecorded : (if delayedProbability .first quarter then j+1 else j) < (X.tr g).length) :
    let pc := probabilityPc .first quarter
    let k := if delayedProbability .first quarter then j + 1 else j
    ∃ u, (delayedProbability .first quarter = true → X.get (g, j) = some ⟨pc, .tc .waitLd⟩) ∧
      X.get (g, k) = some ⟨pc, .tc (.st (probabilityAddress l g stage quarter)
          ((List.range 16).map (probabilityWord exponents)) .s32x32b)⟩ ∧
      At u (pc + 1) [] ∧
      (∀ r, r < firstUnpackBase quarter ∨ firstUnpackBase quarter + 16 ≤ r → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (k + 1)) ending := by
  obtain ⟨u, hu, hU, hOut, hFrame⟩ := firstUnpackInterval (l := l) (g := g)
    quarter exponents 8 0 t (by decide) ht hPacked
  have hRead := storeWordsRead (l := l) (g := g) quarter exponents
    (fun w hw => hOut w (Nat.zero_le _) hw)
  have hWidth : ((List.range 16).map (probabilityWord exponents)).all (·.bytes = 4) = true := by
    apply List.all_eq_true.mpr
    intro value hValue
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hValue
    rfl
  have hSmall : probabilityReg .first quarter < unpackDst quarter 0 := by
    fin_cases quarter <;> decide
  have hr : u.regs (probabilityReg .first quarter) =
      some (b32 (probabilityAddress l g stage quarter)) :=
    (hFrame _ (.inl hSmall)).trans hAddr
  have hU' : At u (probabilityPc .first quarter) [] := unpackEnd quarter ▸ hU
  have hNonempty : (X.tr g).drop j ≠ [] := by
    have hLen : j < (X.tr g).length := by split at hRecorded <;> omega
    intro hEmpty
    have hZero := congrArg List.length hEmpty
    simp only [List.length_drop,List.length_nil] at hZero
    omega
  obtain ⟨hWait, hStore, hTail⟩ := probabilityTraceInPrefix hp .first quarter stage
    hU'.1 hU'.2.2.2.1 hU'.2.1 (firstPStoreCode quarter) hr hRead hWidth
      (hRun.after_local_nonempty (run_rtg hu) hNonempty) hRecorded
  exact ⟨next u, by simpa only [hU'.1] using hWait, by simpa only [hU'.1] using hStore,
    hU'.next, hFrame, hTail⟩

/-- The first P pack's actual unpack sequence feeds the real delayed-wait store. Its 16 words
carry the exponent values in ascending score-column order. -/
theorem firstPackedStoreTrace {g j : Nat} {t : TState} (exponents : Nat → ℝ) (ht : At t 4818 [])
    (hPacked : ∀ word < 8, t.regs (8154 + word) = some (probabilityDoubleWord exponents word))
    (hAddr : t.regs 3223 = some (b32 (probabilityAddress l g stage 0)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, X.get (g, j) = some ⟨4826, .tc .waitLd⟩ ∧
      X.get (g, j + 1) = some ⟨4826,
        .tc (.st (probabilityAddress l g stage 0)
          ((List.range 16).map (probabilityWord exponents)) .s32x32b)⟩ ∧
      At u 4827 [] ∧ (∀ r, r < 3879 ∨ 3895 ≤ r → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 2)) none := by
  obtain ⟨u, hWait, hStore, hU, hFrame, hTail⟩ :=
    packedQuarterStoreTrace hp stage 0 exponents ht hPacked hAddr hRun
  have hDelay : delayedProbability .first 0 = true := rfl
  exact ⟨u, hWait hDelay, hStore, hU, hFrame, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
