-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRead
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.Widen

import Lemmas.Flow.ReturningPrefix
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

def biasReadSubstate (t : TState) (words : Nat → Value) (k : Nat) : TState :=
  { t with sub := k, acc := (List.range k).map words }

/-- The four observations of one shared vector, in the order its destinations use. -/
def BiasWordReads (l : Launch) (X : Execution) (repeated : Bool) (i : Fin 16)
    (g j base : Nat) (words : Nat → Value) : Prop :=
  ∀ k < 4, ∃ bs, X.get (g, j+k) = some
    ⟨biasReadPc repeated i, .rd (biasReadAcc l g base repeated i k) bs⟩ ∧
    rebuild 3 bs = .ok (words k)

section
variable {l : Launch}

private theorem biasReadSubstep {X : Execution} (repeated : Bool) (i : Fin 16) {g j base k : Nat}
    {t : TState} {ending : Option TState} (words : Nat → Value) (hk : k < 4)
    (hpc : t.pc = biasReadPc repeated i) (hf : t.fault = none)
    (hr : t.regs (biasReadSite repeated i).base = some (b32 base))
    (hAddr : base + (biasReadSite repeated i).offset < 2 ^ 32)
    (hAlign : (base + (biasReadSite repeated i).offset) % 16 = 0)
    (hValue : ∀ bs, X.get (g, j+k) = some
      ⟨biasReadPc repeated i, .rd (biasReadAcc l g base repeated i k) bs⟩ →
        rebuild 3 bs = .ok (words k))
    (hRun : Run kernel Assumptions.all l g (biasReadSubstate t words k)
      ((X.tr g).drop (j+k)) ending) (hMore : (X.tr g).drop (j+k) ≠ []) :
    ∃ bs, X.get (g, j+k) = some
        ⟨biasReadPc repeated i, .rd (biasReadAcc l g base repeated i k) bs⟩ ∧
      rebuild 3 bs = .ok (words k) ∧
      Run kernel Assumptions.all l g
        (if k + 1 < 4 then biasReadSubstate t words (k+1)
          else setRegs { t with pc := t.pc+1, sub := 0, acc := [] }
            (biasReadRegs repeated i) ((List.range 4).map words))
        ((X.tr g).drop (j+k+1)) ending ∧
      EStep kernel Assumptions.all l g (biasReadSubstate t words k)
        ⟨biasReadPc repeated i,.rd (biasReadAcc l g base repeated i k) bs⟩
        (some (if k+1 < 4 then biasReadSubstate t words (k+1)
          else setRegs { t with pc := t.pc+1,sub := 0,acc := [] }
            (biasReadRegs repeated i) ((List.range 4).map words))) := by
  obtain ⟨bs,he,htail,hStep⟩ :=
    biasReadElementStepInPrefix repeated i (t := biasReadSubstate t words k) (j := j+k)
      hpc hf hr hAddr hAlign hRun hMore
  have hWord := hValue bs he
  refine ⟨bs, he, hWord, ?_⟩
  have hLen : (biasReadRegs repeated i).length = 4 := rfl
  by_cases hm : k+1 < 4
  · rw [ite_eq_left hm]
    have hs : (biasReadSubstate t words k).sub + 1 < (biasReadRegs repeated i).length := by
      simpa only [biasReadSubstate, hLen] using hm
    rw [afterLoad_mid hWord hs] at htail hStep
    simpa only [biasReadSubstate, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      using And.intro htail hStep
  · rw [ite_eq_right hm]
    have hs : ¬ (biasReadSubstate t words k).sub + 1 < (biasReadRegs repeated i).length := by
      simpa only [biasReadSubstate, hLen] using hm
    have hEnd : k = 3 := by omega
    subst k
    rw [afterLoad_last hWord hs] at htail hStep
    exact ⟨htail,hStep⟩

private theorem biasVectorWordsCursorTrace {X : Execution} (repeated : Bool) (i : Fin 16)
    {g j base : Nat} {t : TState} {ending : Option TState} (words : Nat → Value)
    (ht : At t (biasReadPc repeated i) [((biasReadSite repeated i).base, b32 base)])
    (hAddr : base + (biasReadSite repeated i).offset < 2 ^ 32)
    (hAlign : (base + (biasReadSite repeated i).offset) % 16 = 0) {cursor : Nat → Prop}
    (hCursor : cursor j)
    (hValue : ∀ k < 4, cursor (j+k) → ∀ bs, X.get (g, j+k) = some
      ⟨biasReadPc repeated i, .rd (biasReadAcc l g base repeated i k) bs⟩ →
        rebuild 3 bs = .ok (words k))
    (hAdvance : ∀ k < 4, ∀ bs, X.get (g,j+k) = some
      ⟨biasReadPc repeated i,.rd (biasReadAcc l g base repeated i k) bs⟩ →
      cursor (j+k) → cursor (j+k+1))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hPresent : ∀ k ≤ 4, cursor (j+k) → ending = none ∨ j+k < (X.tr g).length) :
    let ds := biasReadRegs repeated i
    let u := setRegs { t with pc := t.pc+1, sub := 0, acc := [] } ds
      ((List.range 4).map words)
    BiasWordReads l X repeated i g j base words ∧
      At u (biasReadPc repeated i+1) [] ∧
      (∀ k < 4, u.regs ((biasReadSite repeated i).firstReg+k) = some (words k)) ∧
      (∀ r, r ∉ ds → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+4)) ending ∧ cursor (j+4) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 4) u := by
  have hInitial : biasReadSubstate t words 0 = t := by
    cases t
    simp [biasReadSubstate] at ht ⊢
    exact ⟨ht.2.1.symm, ht.2.2.1⟩
  have hStep (k : Nat) (hk : k < 4) (hc : cursor (j+k))
      (hR : Run kernel Assumptions.all l g (biasReadSubstate t words k)
        ((X.tr g).drop (j+k)) ending) := by
    apply biasReadSubstep repeated i words hk ht.1 ht.2.2.2.1
      ht.2.2.2.2.1 hAddr hAlign (hValue k hk hc) hR
    intro hEmpty
    rw [hEmpty] at hR
    cases hR
    have hLen := List.drop_eq_nil_iff.mp hEmpty
    exact (hPresent k (by omega) hc).elim (by simp) (fun h => by omega)
  have hC0 : cursor (j+0) := hCursor
  obtain ⟨bs0, he0, hw0, hr0, hp0⟩ := hStep 0 (by decide) hC0 (hInitial.symm ▸ hRun)
  have hC1 : cursor (j+1) := hAdvance 0 (by decide) bs0 he0 hC0
  obtain ⟨bs1, he1, hw1, hr1, hp1⟩ := hStep 1 (by decide) hC1 hr0
  have hC2 : cursor (j+2) := hAdvance 1 (by decide) bs1 he1 hC1
  obtain ⟨bs2, he2, hw2, hr2, hp2⟩ := hStep 2 (by decide) hC2 hr1
  have hC3 : cursor (j+3) := hAdvance 2 (by decide) bs2 he2 hC2
  obtain ⟨bs3, he3, hw3, hr3, hp3⟩ := hStep 3 (by decide) hC3 hr2
  have hC4 : cursor (j+4) := hAdvance 3 (by decide) bs3 he3 hC3
  dsimp only
  have hs := setRegs_skel { t with pc := t.pc+1, sub := 0, acc := [] }
    (biasReadRegs repeated i) ((List.range 4).map words)
  have hsAt : At (setRegs { t with pc := t.pc+1, sub := 0, acc := [] }
      (biasReadRegs repeated i) ((List.range 4).map words))
      (biasReadPc repeated i+1) [] :=
    ⟨hs.1.trans (congrArg (· + 1) ht.1), hs.2.1, hs.2.2.1,
      hs.2.2.2.trans ht.2.2.2.1, trivial⟩
  refine ⟨?_, hsAt, ?_, fun r hr => setRegs_other _ _ _ r hr, hr3, hC4, ?_⟩
  · intro k hk
    interval_cases k
    · exact ⟨bs0, he0, hw0⟩
    · exact ⟨bs1, he1, hw1⟩
    · exact ⟨bs2, he2, hw2⟩
    · exact ⟨bs3, he3, hw3⟩
  · intro k hk
    have hNodup : (biasReadRegs repeated i).Nodup := by
      cases repeated <;> fin_cases i <;> decide
    apply setRegs_get _ _ _ k _ _ hNodup
    · interval_cases k <;> rfl
    · simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some]
  · change (X.tr g)[j+0]? = some _ at he0
    change (X.tr g)[j+1]? = some _ at he1
    change (X.tr g)[j+2]? = some _ at he2
    change (X.tr g)[j+3]? = some _ at he3
    simp only [List.take_add_one,List.getElem?_drop,he0,he1,he2,he3,
      List.take_zero,Option.toList,List.nil_append,List.cons_append]
    exact .event (hInitial ▸ hp0) (.event hp1 (.event hp2 (.event hp3 (.refl _))))

/-- The largest BF16 destination register in a decoded bias vector. -/
def biasUnpackTop (repeated : Bool) (i : Fin 16) : Nat :=
  (if repeated then 921 else 793) + 8*i.val

/-- BF16 registers written by the decoded unpack of one shared bias word. -/
def biasUnpackRegs (repeated : Bool) (i : Fin 16) (word : Nat) : Nat × Nat :=
  (biasUnpackTop repeated i - 2*word, biasUnpackTop repeated i - 2*word - 1)

private def biasUnpackInstr (repeated : Bool) (i : Fin 16) (word : Nat) : Instr :=
  let ds := biasUnpackRegs repeated i word
  ⟨none, .move ⟨.unpack, .int .b 32, [some ds.1, some ds.2],
    [.reg ((biasReadSite repeated i).firstReg+word)]⟩⟩

private theorem biasUnpackSlice (repeated : Bool) (i : Fin 16) :
    ((kernel.code.drop (biasReadPc repeated i+1)).take 4) =
      (List.range 4).map (fun k => biasUnpackInstr repeated i (3-k)) := by
  cases repeated <;> fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem biasUnpackCode (repeated : Bool) (i : Fin 16) {word : Nat} (hWord : word < 4) :
    kernel.code[biasReadPc repeated i+1+(3-word)]? = some (biasUnpackInstr repeated i word) := by
  have hn : 3-word < 4 := by omega
  have h := congrArg (fun codes : List Instr => codes[3-word]?) (biasUnpackSlice repeated i)
  rw [List.getElem?_take_of_lt hn, List.getElem?_drop, List.getElem?_map,
    List.getElem?_range hn, Option.map_some, show 3-(3-word) = word by omega] at h
  exact h

private theorem biasUnpackOff (repeated : Bool) (i : Fin 16) {word : Nat} (hWord : word < 4) :
    biasReadPc repeated i+1+(3-word) ∉ Assumptions.swExp2Sites := by
  have hI := i.isLt
  cases repeated <;> simp only [biasReadPc, Bool.false_eq_true, ↓reduceIte, Assumptions.swExp2Sites,
    List.mem_cons, List.not_mem_nil, or_false] <;> omega

private theorem biasUnpackBounds (repeated : Bool) (i : Fin 16) :
    793 ≤ biasUnpackTop repeated i ∧
      biasUnpackTop repeated i < (biasReadSite repeated i).firstReg := by
  cases repeated <;> fin_cases i <;> decide

/-- The decoded unpack accepts a four-byte word containing two BF16-sized halves. -/
def BiasWordShape (word : Value) : Prop :=
  word.bytes = 4 ∧ (splitValue 32 word).1.bytes = 2 ∧ (splitValue 32 word).2.bytes = 2

theorem biasUnpackRun {g : Nat} (repeated : Bool) (i : Fin 16) {n : Nat} (hn : n ≤ 4)
    (words : Nat → Value) (hShape : ∀ k < 4, BiasWordShape (words k)) {t : TState}
    (ht : At t (biasReadPc repeated i+1+(4-n)) [])
    (hWords : ∀ k < 4, t.regs ((biasReadSite repeated i).firstReg+k) = some (words k)) :
    ∃ u, run kernel Assumptions.all l g n t = some u ∧ At u (biasReadPc repeated i+5) [] ∧
      (∀ k < n, u.regs (biasUnpackRegs repeated i k).1 =
          some (splitValue 32 (words k)).1 ∧
        u.regs (biasUnpackRegs repeated i k).2 = some (splitValue 32 (words k)).2) ∧
      ∀ r, r < biasUnpackTop repeated i+1-2*n ∨ biasUnpackTop repeated i < r →
        u.regs r = t.regs r := by
  induction n generalizing t with
  | zero =>
    exact ⟨t, rfl, ⟨by rw [ht.1], ht.2⟩, fun k hk => (Nat.not_lt_zero _ hk).elim, fun _ _ => rfl⟩
  | succ n ih =>
    have hn' : n < 4 := by omega
    have hB := biasUnpackBounds repeated i
    let lo := (biasUnpackRegs repeated i n).1
    let hi := (biasUnpackRegs repeated i n).2
    let parts := splitValue 32 (words n)
    let v := next (setReg (setReg t lo parts.1) hi parts.2)
    have hLo : lo = biasUnpackTop repeated i - 2*n := rfl
    have hHi : hi = lo-1 := rfl
    have hPC : biasReadPc repeated i+1+(4-(n+1)) = biasReadPc repeated i+1+(3-n) := by omega
    have hv : run kernel Assumptions.all l g 1 t = some v := by
      apply run_local (biasUnpackCode repeated i hn') rfl (hPC ▸ ht)
      rw [Assumptions.execLocalA_all_eq_numeric,
        Assumptions.execLocalA_eq_nil ((hPC ▸ ht).1.symm ▸ biasUnpackOff repeated i hn') rfl]
      have he := exec_unpack (A := []) (L := l) (g := g) (lo := lo) (hi := hi)
        (by simp [NoUnpack]) (hWords n hn') Assumption.SegFreePc.nil
      obtain ⟨h4, hHalves⟩ := hShape n hn'
      simpa only [ite_eq_left h4, ite_eq_left hHalves, v, parts] using he
    have hV : At v (biasReadPc repeated i+1+(4-n)) [] := by
      refine ⟨?_, ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
      change t.pc+1 = _
      rw [ht.1]
      omega
    have hBack (r : Nat) (hl : r ≠ lo) (hh : r ≠ hi) : v.regs r = t.regs r := by
      simp only [v, next, setReg, Function.update_of_ne hl, Function.update_of_ne hh]
    have hVL : v.regs lo = some parts.1 := by
      simp only [v, next, setReg, Function.update_of_ne (show lo ≠ hi by omega),
        Function.update_self]
    have hVH : v.regs hi = some parts.2 := Function.update_self ..
    obtain ⟨u, hu, huAt, hBits, hFrame⟩ := ih (by omega) hV (by
      intro k hk
      refine (hBack _ (by omega) (by omega)).trans (hWords k hk))
    refine ⟨u, by simpa only [Nat.one_add] using run_comp hv hu, huAt, ?_, ?_⟩
    · intro k hk
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · exact ⟨(hFrame lo (.inl (by omega))).trans hVL, (hFrame hi (.inl (by omega))).trans hVH⟩
      · exact hBits k hlt
    · intro r hr
      refine (hFrame r ?_).trans (hBack r (by omega) (by omega))
      omega

private theorem biasVectorCursorTrace {X : Execution} (repeated : Bool) (i : Fin 16)
    {g j base : Nat} {t : TState} {ending : Option TState} (words : Nat → Value)
    (hShape : ∀ k < 4, BiasWordShape (words k))
    (ht : At t (biasReadPc repeated i) [((biasReadSite repeated i).base, b32 base)])
    (hAddr : base + (biasReadSite repeated i).offset < 2 ^ 32)
    (hAlign : (base + (biasReadSite repeated i).offset) % 16 = 0) {cursor : Nat → Prop}
    (hCursor : cursor j)
    (hValue : ∀ k < 4, cursor (j+k) → ∀ bs, X.get (g, j+k) = some
      ⟨biasReadPc repeated i, .rd (biasReadAcc l g base repeated i k) bs⟩ →
        rebuild 3 bs = .ok (words k))
    (hAdvance : ∀ k < 4, ∀ bs, X.get (g,j+k) = some
      ⟨biasReadPc repeated i,.rd (biasReadAcc l g base repeated i k) bs⟩ →
      cursor (j+k) → cursor (j+k+1))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hPresent : ∀ k ≤ 4, cursor (j+k) → ending = none ∨ j+k < (X.tr g).length) :
    ∃ u, BiasWordReads l X repeated i g j base words ∧
      At u (biasReadPc repeated i+5) [] ∧
      (∀ k < 4, u.regs (biasUnpackRegs repeated i k).1 =
          some (splitValue 32 (words k)).1 ∧
        u.regs (biasUnpackRegs repeated i k).2 = some (splitValue 32 (words k)).2) ∧
      (∀ r, r ∉ biasReadRegs repeated i →
        (r < (biasUnpackRegs repeated i 3).2 ∨ (biasUnpackRegs repeated i 0).1 < r) →
        u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+4)) ending ∧ cursor (j+4) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 4) u := by
  obtain ⟨hRead,hLoaded,hWords,hKeep,hTail,hNext,hPath⟩ :=
    biasVectorWordsCursorTrace repeated i words ht hAddr hAlign hCursor hValue hAdvance hr hPresent
  obtain ⟨u, hu, hU, hBits, hFrame⟩ :=
    biasUnpackRun repeated i (Nat.le_refl 4) words hShape hLoaded hWords
  have hMore : (X.tr g).drop (j+4) ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hTail
    cases hTail
    exact (hPresent 4 le_rfl hNext).elim (by simp)
      (fun h => (Nat.not_lt_of_ge (List.drop_eq_nil_iff.mp hEmpty)) h)
  refine ⟨u,hRead,hU,hBits,?_,hTail.after_local_nonempty (run_rtg hu) hMore,hNext,?_⟩
  · intro r hn hR
    have hB := (biasUnpackBounds repeated i).1
    have hBounds : r < biasUnpackTop repeated i+1-2*4 ∨ biasUnpackTop repeated i < r := by
      unfold biasUnpackRegs at hR
      dsimp only at hR
      omega
    exact (hFrame r hBounds).trans (hKeep r hn)
  · simpa only [List.append_nil] using hPath.append (TraceReach.of_local (run_rtg hu))

private theorem biasReadFirstReg (repeated : Bool) (i : Fin 16) :
    (biasReadSite repeated i).firstReg = (if repeated then 4171 else 3011)+4*i.val := by
  cases repeated <;> fin_cases i <;> rfl

/-- Registers that a particular decoded bias vector and its unpack leave intact. -/
def biasVectorKeeps (repeated : Bool) (i : Fin 16) (r : Nat) : Prop :=
  r ∉ biasReadRegs repeated i ∧
    (r < (biasUnpackRegs repeated i 3).2 ∨ (biasUnpackRegs repeated i 0).1 < r)

private theorem biasVectorKeepAddress (repeated : Bool) (i q : Fin 16) :
    biasVectorKeeps repeated i (biasReadSite repeated q).base := by
  have hQ := q.isLt
  have hI := i.isLt
  have hBF : 2784 ≤ (biasReadSite false q).base ∧ (biasReadSite false q).base ≤ 2846 := by
    fin_cases q <;> decide
  have hBT : 3982 ≤ (biasReadSite true q).base ∧ (biasReadSite true q).base ≤ 4170 := by
    fin_cases q <;> decide
  unfold biasVectorKeeps biasReadRegs biasUnpackRegs biasUnpackTop
  rw [biasReadFirstReg]
  cases repeated <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] <;>
    omega

theorem biasVectorKeepPrevious (repeated : Bool) (i q : Fin 16) {word r : Nat}
    (hOrder : i.val < q.val) (hWord : word < 4)
    (hDst : r = (biasUnpackRegs repeated i word).1 ∨ r = (biasUnpackRegs repeated i word).2) :
    biasVectorKeeps repeated q r := by
  have hI := i.isLt
  have hQ := q.isLt
  unfold biasUnpackRegs biasUnpackTop at hDst
  unfold biasVectorKeeps biasReadRegs biasUnpackRegs biasUnpackTop
  rw [biasReadFirstReg]
  cases repeated <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at * <;>
    omega

/-- All eight BF16 operands of a bias vector, in decoded load and unpack order. -/
def BiasUnpacked (repeated : Bool) (i : Fin 16) (u : TState) (words : Nat → Value) : Prop :=
  ∀ k < 4, u.regs (biasUnpackRegs repeated i k).1 = some (splitValue 32 (words k)).1 ∧
    u.regs (biasUnpackRegs repeated i k).2 = some (splitValue 32 (words k)).2

private theorem biasVectorSequence {X : Execution} (repeated : Bool) {g j : Nat}
    (base : Fin 16 → Nat) (words : Fin 16 → Nat → Value)
    (hShape : ∀ i k, k < 4 → BiasWordShape (words i k))
    (hAddr : ∀ i, base i + (biasReadSite repeated i).offset < 2^32)
    (hAlign : ∀ i, (base i + (biasReadSite repeated i).offset) % 16 = 0) {cursor : Nat → Prop}
    (hValue : ∀ i k, k < 4 → cursor (j+4*i.val+k) → ∀ bs,
      X.get (g, j+4*i.val+k) = some
        ⟨biasReadPc repeated i, .rd (biasReadAcc l g (base i) repeated i k) bs⟩ →
          rebuild 3 bs = .ok (words i k))
    (hAdvance : ∀ i k, k < 4 → ∀ bs, X.get (g,j+4*i.val+k) = some
      ⟨biasReadPc repeated i,.rd (biasReadAcc l g (base i) repeated i k) bs⟩ →
      cursor (j+4*i.val+k) → cursor (j+4*i.val+k+1)) {n : Nat} (hn : n ≤ 16) {t : TState}
    {ending : Option TState} (ht : At t ((biasReadPc repeated 0)+5*(16-n)) [])
    (hBases : ∀ i : Fin 16, 16-n ≤ i.val →
      t.regs (biasReadSite repeated i).base = some (b32 (base i))) (hCursor : cursor (j+4*(16-n)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop (j+4*(16-n))) ending)
    (hPresent : ∀ k, j ≤ k → k ≤ j+64 → cursor k → ending = none ∨ k < (X.tr g).length) :
    ∃ u, At u ((biasReadPc repeated 0)+80) [] ∧
      (∀ i : Fin 16, 16-n ≤ i.val →
        BiasWordReads l X repeated i g (j+4*i.val) (base i) (words i) ∧
        BiasUnpacked repeated i u (words i)) ∧
      (∀ r, (∀ i : Fin 16, 16-n ≤ i.val → biasVectorKeeps repeated i r) →
        u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+64)) ending ∧ cursor (j+64) ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop (j+4*(16-n))).take (4*n)) u := by
  induction n generalizing t with
  | zero =>
    exact ⟨t,ht,fun i hi => by have := i.isLt; omega,fun _ _ => rfl,hr,hCursor,
      by simp; exact .refl _⟩
  | succ n ih =>
    let i : Fin 16 := ⟨16-(n+1), by omega⟩
    have hI : i.val = 16-(n+1) := rfl
    have hPc : biasReadPc repeated i = biasReadPc repeated 0+5*(16-(n+1)) := rfl
    have hNext : biasReadPc repeated i+5 = biasReadPc repeated 0+5*(16-n) := by
      rw [hPc]
      omega
    have hIndex : j+4*i.val+4 = j+4*(16-n) := by omega
    have hAt : At t (biasReadPc repeated i) [((biasReadSite repeated i).base, b32 (base i))] :=
      (hPc.symm ▸ ht).mono ⟨hBases i (by omega), trivial⟩
    obtain ⟨v,hReads,hvAt,hBits,hF,hvRun,hC,hPath⟩ :=
      biasVectorCursorTrace repeated i (words i) (hShape i) hAt (hAddr i) (hAlign i)
        hCursor (hValue i) (hAdvance i) hr
        (fun k hk hC => hPresent _ (by omega) (by have := i.isLt; omega) hC)
    have hKeep (r : Nat) (hR : biasVectorKeeps repeated i r) : v.regs r = t.regs r :=
      hF r hR.1 hR.2
    obtain ⟨u,huAt,huWords,huFrame,huRun,huCursor,hTailPath⟩ := ih (by omega) (hNext ▸ hvAt)
      (fun q hq => (hKeep _ (biasVectorKeepAddress repeated i q)).trans (hBases q (by omega)))
      (hIndex ▸ hC) (hIndex ▸ hvRun)
    refine ⟨u,huAt,?_,?_,huRun,huCursor,?_⟩
    · intro q hq
      by_cases hq' : 16-n ≤ q.val
      · exact huWords q hq'
      · have heq : q = i := Fin.ext (by omega)
        subst q
        refine ⟨hReads, fun k hk => ?_⟩
        have hPair := hBits k hk
        have hFrame (r : Nat)
            (hR : r = (biasUnpackRegs repeated i k).1 ∨ r = (biasUnpackRegs repeated i k).2) :=
          huFrame r (fun q hq => biasVectorKeepPrevious repeated i q (by omega) hk hR)
        exact ⟨(hFrame _ (.inl rfl)).trans hPair.1, (hFrame _ (.inr rfl)).trans hPair.2⟩
    · intro r hR
      exact (huFrame r (fun q hq => hR q (by omega))).trans (hKeep _ (hR i (by omega)))
    · have hList : (((X.tr g).drop (j+4*(16-(n+1)))).take (4*(n+1))) =
          (((X.tr g).drop (j+4*i.val)).take 4) ++
            (((X.tr g).drop (j+4*(16-n))).take (4*n)) := by
        rw [show 4*(n+1) = 4+4*n by omega,List.take_add,List.drop_drop,← hIndex,hI]
      rw [hList]
      exact hPath.append hTailPath

end

section
variable {l : Launch} {X : Execution} (repeated : Bool) {g j : Nat} (base : Fin 16 → Nat)
    (words : Fin 16 → Nat → Value) {t : TState} {ending : Option TState}
    (hShape : ∀ i k, k < 4 → BiasWordShape (words i k)) (ht : At t (biasReadPc repeated 0) [])
    (hBases : ∀ i, t.regs (biasReadSite repeated i).base = some (b32 (base i)))
    (hAddr : ∀ i, base i + (biasReadSite repeated i).offset < 2^32)
    (hAlign : ∀ i, (base i + (biasReadSite repeated i).offset) % 16 = 0) {cursor : Nat → Prop}
    (hCursor : cursor j)
    (hValue : ∀ i k, k < 4 → cursor (j+4*i.val+k) → ∀ bs,
      X.get (g, j+4*i.val+k) = some
        ⟨biasReadPc repeated i, .rd (biasReadAcc l g (base i) repeated i k) bs⟩ →
          rebuild 3 bs = .ok (words i k))
    (hAdvance : ∀ i k, k < 4 → ∀ bs, X.get (g,j+4*i.val+k) = some
      ⟨biasReadPc repeated i,.rd (biasReadAcc l g (base i) repeated i k) bs⟩ →
      cursor (j+4*i.val+k) → cursor (j+4*i.val+k+1))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
include repeated base words hShape ht hBases hAddr hAlign hCursor hValue hAdvance hr

/-- Replay all sixteen actual Bias vectors while carrying an observation on the
lane's trace index across each decoded read. -/
theorem biasVectorsTraceWithPathGuarded
    (hPresent : ∀ k, j ≤ k → k ≤ j+64 → cursor k → ending = none ∨ k < (X.tr g).length) :
    ∃ u, At u ((biasReadPc repeated 0)+80) [] ∧
      (∀ i, BiasWordReads l X repeated i g (j+4*i.val) (base i) (words i) ∧
        BiasUnpacked repeated i u (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps repeated i r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+64)) ending ∧ cursor (j+64) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 64) u := by
  obtain ⟨u,hu,hWords,hFrame,huRun,huCursor,hPath⟩ :=
    biasVectorSequence repeated base words hShape hAddr hAlign hValue hAdvance (Nat.le_refl 16)
      ht (fun i _ => hBases i) hCursor hr hPresent
  exact ⟨u,hu,fun i => hWords i (Nat.zero_le _),fun r hR => hFrame r (fun i _ => hR i),
    huRun,huCursor,hPath⟩

theorem biasVectorsTraceWithCursorGuarded
    (hPresent : ∀ k, j ≤ k → k ≤ j+64 → cursor k → ending = none ∨ k < (X.tr g).length) :
    ∃ u, At u ((biasReadPc repeated 0)+80) [] ∧
      (∀ i, BiasWordReads l X repeated i g (j+4*i.val) (base i) (words i) ∧
        BiasUnpacked repeated i u (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps repeated i r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+64)) ending ∧ cursor (j+64) := by
  obtain ⟨u,hu,hWords,hFrame,huRun,huCursor,_⟩ :=
    biasVectorsTraceWithPathGuarded repeated base words hShape ht hBases hAddr hAlign
      hCursor hValue hAdvance hr hPresent
  exact ⟨u,hu,hWords,hFrame,huRun,huCursor⟩

theorem biasVectorsTraceWithCursorInPrefix (hPresent : ending = none ∨ j+64 < (X.tr g).length) :
    ∃ u, At u ((biasReadPc repeated 0)+80) [] ∧
      (∀ i, BiasWordReads l X repeated i g (j+4*i.val) (base i) (words i) ∧
        BiasUnpacked repeated i u (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps repeated i r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+64)) ending ∧ cursor (j+64) := by
  exact biasVectorsTraceWithCursorGuarded repeated base words hShape ht hBases hAddr hAlign
    hCursor hValue hAdvance hr (fun k _ hk _ => hPresent.imp_right (Nat.lt_of_le_of_lt hk))
end

section
variable {l : Launch} {X : Execution} (repeated : Bool) {g j : Nat} (base : Fin 16 → Nat)
    (words : Fin 16 → Nat → Value) {t : TState} (hShape : ∀ i k, k < 4 → BiasWordShape (words i k))
    (ht : At t (biasReadPc repeated 0) [])
    (hBases : ∀ i, t.regs (biasReadSite repeated i).base = some (b32 (base i)))
    (hAddr : ∀ i, base i + (biasReadSite repeated i).offset < 2^32)
    (hAlign : ∀ i, (base i + (biasReadSite repeated i).offset) % 16 = 0)
include repeated base words hShape ht hBases hAddr hAlign

theorem biasVectorsTraceWithCursor {cursor : Nat → Prop} (hCursor : cursor j)
    (hValue : ∀ i k, k < 4 → cursor (j+4*i.val+k) → ∀ bs,
      X.get (g, j+4*i.val+k) = some
        ⟨biasReadPc repeated i, .rd (biasReadAcc l g (base i) repeated i k) bs⟩ →
          rebuild 3 bs = .ok (words i k))
    (hAdvance : ∀ i k, k < 4 → ∀ bs, X.get (g,j+4*i.val+k) = some
      ⟨biasReadPc repeated i,.rd (biasReadAcc l g (base i) repeated i k) bs⟩ →
      cursor (j+4*i.val+k) → cursor (j+4*i.val+k+1))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, At u ((biasReadPc repeated 0)+80) [] ∧
      (∀ i, BiasWordReads l X repeated i g (j+4*i.val) (base i) (words i) ∧
        BiasUnpacked repeated i u (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps repeated i r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+64)) none ∧ cursor (j+64) := by
  exact biasVectorsTraceWithCursorInPrefix repeated base words hShape ht hBases hAddr hAlign
    hCursor hValue hAdvance hr (.inl rfl)

/-- The actual Bias load sequence observes sixteen shared vectors and retains all 128
BF16 operands before the post-load proxy fence. -/
theorem biasVectorsTrace
    (hValue : ∀ i k, k < 4 → ∀ bs, X.get (g, j+4*i.val+k) = some
      ⟨biasReadPc repeated i, .rd (biasReadAcc l g (base i) repeated i k) bs⟩ →
        rebuild 3 bs = .ok (words i k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, At u ((biasReadPc repeated 0)+80) [] ∧
      (∀ i, BiasWordReads l X repeated i g (j+4*i.val) (base i) (words i) ∧
        BiasUnpacked repeated i u (words i)) ∧
      (∀ r, (∀ i, biasVectorKeeps repeated i r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+64)) none := by
  obtain ⟨u,hu,hWords,hFrame,huRun,_⟩ :=
    biasVectorsTraceWithCursor repeated base words hShape ht hBases hAddr hAlign
      (cursor := fun _ => True) trivial (fun i k hk _ => hValue i k hk)
      (fun _ _ _ _ _ _ => trivial) hr
  exact ⟨u,hu,hWords,hFrame,huRun⟩
end

/-- The first Bias-full wait feeds all sixteen actual vectors and reaches the proxy fence.
The supplied values are the four-byte words recovered from the observed shared bytes. -/
theorem firstBiasTileTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t 3498 F)
    (hBarrier : (2771, b32 (waitLoc l g stage 2).addr) ∈ F)
    (hPhase : (2770, b32 0) ∈ F)
    (hKeep : ∀ x ∈ F, x.1 ≠ 9752 ∧ ∀ i, biasVectorKeeps false i x.1)
    (base : Fin 16 → Nat) (words : Fin 16 → Nat → Value)
    (hShape : ∀ i k, k < 4 → BiasWordShape (words i k))
    (hBases : ∀ i, ((biasReadSite false i).base, b32 (base i)) ∈ F)
    (hAddr : ∀ i, base i + (biasReadSite false i).offset < 2^32)
    (hAlign : ∀ i, (base i + (biasReadSite false i).offset) % 16 = 0)
    (hValue : ∀ wait, X.get (g, wait) =
      some ⟨3498, .wait (waitLoc l g stage 2) 0 true true .cta⟩ →
      ∀ i k, k < 4 → ∀ bs, X.get (g, wait + 1 + 4 * i.val + k) = some
        ⟨biasReadPc false i, .rd (biasReadAcc l g (base i) false i k) bs⟩ →
          rebuild 3 bs = .ok (words i k))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ fails u, let start := j+fails+1
      (X.tr g).drop j =
        List.replicate fails ⟨3498, .wait (waitLoc l g stage 2) 0 false true .cta⟩ ++
          ⟨3498, .wait (waitLoc l g stage 2) 0 true true .cta⟩ :: (X.tr g).drop start ∧
      At u 3581 F ∧
      (∀ i, BiasWordReads l X false i g (start+4*i.val) (base i) (words i) ∧
        BiasUnpacked false i u (words i)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+64)) none := by
  obtain ⟨fails, v, hEvents, hvAt, hv⟩ :=
    waitTraceAt hp stage 2 g 0 (by decide) hBarrier hPhase (fun x hx => (hKeep x hx).1) ht hRun
  have hSuccess : X.get (g, j + fails) =
      some ⟨3498, .wait (waitLoc l g stage 2) 0 true true .cta⟩ := by
    change (X.tr g)[j + fails]? = _
    rw [← List.getElem?_drop, hEvents, List.getElem?_append_right (by simp),
      List.length_replicate, Nat.sub_self]
    rfl
  obtain ⟨u, huAt, hu, hFrame, hTail⟩ :=
    biasVectorsTrace false base words hShape (hvAt.mono trivial)
            (fun i => holds_mem hvAt.2.2.2.2 (hBases i)) hAddr hAlign
      (hValue (j + fails) hSuccess) hv
  refine ⟨fails, u, hEvents, huAt.mono ?_, hu, hTail⟩
  have keep {facts : List (Nat × Value)} (hFacts : Holds v.regs facts)
      (hStable : ∀ x ∈ facts, ∀ i, biasVectorKeeps false i x.1) : Holds u.regs facts := by
    induction facts with
    | nil => trivial
    | cons x xs ih =>
      obtain ⟨r, w⟩ := x
      exact ⟨(hFrame r (hStable (r, w) (by simp))).trans hFacts.1,
        ih hFacts.2 (fun y hy => hStable y (List.mem_cons_of_mem _ hy))⟩
  exact keep hvAt.2.2.2.2 (fun x hx => (hKeep x hx).2)

end PTX.Kernels.TmlFa4Fwd.Softmax
