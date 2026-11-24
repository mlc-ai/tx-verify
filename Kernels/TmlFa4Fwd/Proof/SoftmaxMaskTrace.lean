-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxCausalMask
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMaskSetup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The first visit masks keys beyond the current row's suffix-causal extent. -/
def firstMaskedValue (p : Params) (batch row blocks : Nat) (score : Nat → Option ℝ)
    (col : Nat) : Option ℝ :=
  if visitKey blocks 0 col < p.keyCount batch row then score col else none

def firstMaskInputs (t : TState) (score : Nat → Option ℝ) : Prop :=
  ∀ (group : Fin 4) (pair : Nat), pair < 16 →
    t.regs (firstMaskPairRegs group pair).packed =
      some (Value.pair (scoreValue (score (32 * group + 2 * pair)))
        (scoreValue (score (32 * group + 2 * pair + 1))))

def firstMaskOutputs (t : TState) (group : Nat) (score : Nat → Option ℝ) : Prop :=
  ∀ pair < 16, t.regs (firstMaskPairRegs group pair).low =
    some (scoreValue (score (32 * group + 2 * pair))) ∧
    t.regs (firstMaskPairRegs group pair).high =
      some (scoreValue (score (32 * group + 2 * pair + 1)))

private theorem noMaskGapOutput (group : Fin 4) (pair : Nat) (hj : pair < 16) :
    (firstMaskPairRegs group pair).low ∉ firstMaskSetupWrites ∧
    (firstMaskPairRegs group pair).high ∉ firstMaskSetupWrites := by
  have hg := group.isLt
  unfold firstMaskSetupWrites firstMaskPairRegs maskScratch
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false, not_or]
  by_cases hLast : pair = 15 <;> simp only [hLast, ite_true, ite_false] <;> omega

private theorem noMaskPacked (group : Fin 4) (pair : Nat) (hj : pair < 16) :
    (firstMaskPairRegs group pair).packed ∉ firstMaskSetupWrites ∧
    ∀ other : Fin 4, ¬ firstMaskGroupWrites other (firstMaskPairRegs group pair).packed := by
  have hg := group.isLt
  constructor
  · unfold firstMaskSetupWrites firstMaskPairRegs
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    omega
  · intro other
    have ho := other.isLt
    unfold firstMaskGroupWrites firstMaskPairRegs maskScratch maskPred
    dsimp
    omega

private theorem noMaskEarlier (group other : Fin 4) (hEarlier : group.val < other.val)
    (pair : Nat) (hj : pair < 16) :
    ¬ firstMaskGroupWrites other (firstMaskPairRegs group pair).low ∧
    ¬ firstMaskGroupWrites other (firstMaskPairRegs group pair).high := by
  have hg := group.isLt
  have ho := other.isLt
  unfold firstMaskGroupWrites firstMaskPairRegs maskScratch maskPred
  dsimp
  split <;> omega

private theorem groupStartGap (site : Fin 3) :
    firstMaskGroupStart site.val + 111 = maskGap site ∧
    maskGap site + 3 = firstMaskGroupStart (site.val + 1) ∧
    maskGapWord site = firstMaskWordReg (site.val + 1) := by
  fin_cases site <;> exact ⟨rfl, rfl, rfl⟩

variable {l : Launch} {g : Nat} {t : TState}

private theorem firstMaskGroups (p : Params) (batch row blocks : Nat) (score : Nat → Option ℝ)
    (hLo : -2^31 + 128 < firstActive p batch row blocks)
    (hHi : firstActive p batch row blocks < 2^31)
    (ht : At t 3876
      [(3079, b32 (maskWord 0 (firstActive p batch row blocks).toNat)),
        (3235, maskSigned (firstActive p batch row blocks)), (3080, maskSigned (-1))])
    (hscores : firstMaskInputs t score) (n : Nat) (hn : n ≤ 4) :
    ∃ u, At u (firstMaskGroupStart 0 + min (114 * n) 453) [] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ group : Fin 4, group.val < n →
        firstMaskOutputs u group (firstMaskedValue p batch row blocks score)) ∧
      (n < 4 → u.regs (firstMaskWordReg n) =
        some (b32 (maskWord n (firstActive p batch row blocks).toNat))) ∧
      u.regs 3235 = some (maskSigned (firstActive p batch row blocks)) ∧
      u.regs 3080 = some (maskSigned (-1)) ∧
      ∀ r ∉ firstMaskSetupWrites, (∀ group : Fin 4, ¬ firstMaskGroupWrites group r) →
        u.regs r = t.regs r := by
  induction n with
  | zero =>
    exact ⟨t, ht.mono trivial, .refl, fun _ h => (Nat.not_lt_zero _ h).elim,
      fun _ => ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, fun _ _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨s, hs, hRun, hPrev, hWord, hActive, hOnes, hOldFrame⟩ := ih (by omega)
    let group : Fin 4 := ⟨n, by omega⟩
    have hp : At s (firstMaskGroupStart group) [] := by
      have he : firstMaskGroupStart 0 + min (114 * n) 453 = firstMaskGroupStart group := by
        unfold firstMaskGroupStart
        dsimp [group]
        omega
      exact he ▸ hs
    have hInput : firstMaskInputs s score := by
      intro other j hj
      obtain ⟨hN, hG⟩ := noMaskPacked other j hj
      rw [hOldFrame _ hN hG]
      exact hscores other j hj
    obtain ⟨v, hv, hVR, hvOut, hvFrame⟩ :=
      firstMaskGroupLocal p batch row blocks group score hp (hWord (by omega))
        (hInput group)
    have hVActive : v.regs 3235 = some (maskSigned (firstActive p batch row blocks)) := by
      rw [hvFrame 3235 (by unfold firstMaskGroupWrites maskPred maskScratch; omega), hActive]
    have hVOnes : v.regs 3080 = some (maskSigned (-1)) := by
      rw [hvFrame 3080 (by unfold firstMaskGroupWrites maskPred maskScratch; omega), hOnes]
    have hAll (other : Fin 4) (ho : other.val < n+1) :
        firstMaskOutputs v other (firstMaskedValue p batch row blocks score) := by
      by_cases he : other.val = n
      · have hEq : other = group := Fin.ext he
        subst other
        exact hvOut
      · have hlt : other.val < group.val := by dsimp [group]; omega
        intro j hj
        obtain ⟨hLoOut, hHiOut⟩ := hPrev other (by omega) j hj
        obtain ⟨hNotLo, hNotHi⟩ := noMaskEarlier other group hlt j hj
        exact ⟨(hvFrame _ hNotLo).trans hLoOut, (hvFrame _ hNotHi).trans hHiOut⟩
    by_cases hMore : n < 3
    · let site : Fin 3 := ⟨n, hMore⟩
      obtain ⟨hInPc, hOutPc, hOutReg⟩ := groupStartGap site
      have hIn : At v (maskGap site)
          [(3235, maskSigned (firstActive p batch row blocks)), (3080, maskSigned (-1))] :=
        ⟨hv.1.trans hInPc, hv.2.1, hv.2.2.1, hv.2.2.2.1, hVActive, hVOnes, trivial⟩
      obtain ⟨u, hLocal, hu⟩ := (nextMaskWord site l g hLo hHi).apply hIn
      have hFrame := nextMaskSetupFrame site hIn.1 hLocal
      have hPc : u.pc = firstMaskGroupStart 0 + min (114 * (n+1)) 453 := by
        rw [hu.1, hOutPc]
        unfold firstMaskGroupStart
        dsimp [site]
        omega
      refine ⟨u, ⟨hPc, hu.2.1, hu.2.2.1, hu.2.2.2.1, trivial⟩,
        (hRun.trans hVR).trans (run_rtg hLocal), ?_, ?_, hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1, ?_⟩
      · intro other ho j hj
        obtain ⟨hNotLo, hNotHi⟩ := noMaskGapOutput other j hj
        obtain ⟨hOutLo, hOutHi⟩ := hAll other ho j hj
        exact ⟨(hFrame _ hNotLo).trans hOutLo, (hFrame _ hNotHi).trans hOutHi⟩
      · intro _
        rw [← hOutReg]
        exact hu.2.2.2.2.1
      · intro r hN hG
        exact (hFrame r hN).trans ((hvFrame r (hG group)).trans (hOldFrame r hN hG))
    · have hPc : v.pc = firstMaskGroupStart 0 + min (114 * (n+1)) 453 := by
        rw [hv.1]
        unfold firstMaskGroupStart
        dsimp [group]
        omega
      exact ⟨v, ⟨hPc, hv.2⟩, hRun.trans hVR, hAll, fun h => (hMore (by omega)).elim,
        hVActive, hVOnes, fun r hN hG => (hvFrame r (hG group)).trans (hOldFrame r hN hG)⟩

/-- The real first causal-mask path derives its active key count and takes all four groups
to the reduction at PC 4329. Its inputs are the affine score pairs and the fetched row geometry. -/
theorem firstCausalMaskLocal (p : Params) (batch tid base blocks : Nat) (score : Nat → Option ℝ)
    (htid : tid < 2^32) (hLengths : p.qLength batch ≤ p.kLength batch)
    (hK : p.kLength batch + 256 < 2^31) (hQ : 128 * base + tid % 128 < p.qLength batch + 256)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch)
    (ht : At t 3863
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (3219, b32 tid), (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    (hscores : firstMaskInputs t score) :
    let row := 128 * base + tid % 128
    ∃ u, At u 4329 [] ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ group : Fin 4, firstMaskOutputs u group (firstMaskedValue p batch row blocks score)) ∧
      ∀ r ∉ firstMaskSetupWrites, (∀ group : Fin 4, ¬ firstMaskGroupWrites group r) →
        u.regs r = t.regs r := by
  let row := 128 * base + tid % 128
  have hActiveLen : firstActive p batch row blocks < 2^31 := by
    unfold firstActive Params.keyCount
    omega
  have hActiveLo : -2^31 + 128 < firstActive p batch row blocks := by
    unfold firstActive Params.keyCount
    omega
  obtain ⟨s, hsRun, hs⟩ :=
    (firstActiveSegment p l g batch tid base blocks htid hLengths hK hQ hBlocks).apply ht
  obtain ⟨v, hvRun, hv⟩ := (firstMaskInitialWord l g hActiveLo hActiveLen).apply hs
  have hBoth := run_comp hsRun hvRun
  have hFrame := firstMaskSetupFrame ht.1.ge (by rw [ht.1]) hBoth
  obtain ⟨u, hu, huRun, hScores, _, _, _, hKeep⟩ :=
    firstMaskGroups p batch row blocks score hActiveLo hActiveLen hv (by
      intro group j hj
      exact (hFrame _ (noMaskPacked group j hj).1).trans (hscores group j hj))
      4 (by decide)
  exact ⟨u, hu, (run_rtg hBoth).trans huRun, fun group => hScores group group.isLt,
    fun r hN hG => (hKeep r hN hG).trans (hFrame r hN)⟩

/-- The local replay continues a fully recorded lane trace. -/
theorem firstCausalMaskInPrefix {es : List Event} {ending : Option TState} (p : Params)
    (batch tid base blocks : Nat) (score : Nat → Option ℝ) (htid : tid < 2^32)
    (hLengths : p.qLength batch ≤ p.kLength batch) (hK : p.kLength batch + 256 < 2^31)
    (hQ : 128 * base + tid % 128 < p.qLength batch + 256)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch)
    (ht : At t 3863
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (3219, b32 tid), (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    (hscores : firstMaskInputs t score) (hr : Run kernel Assumptions.all l g t es ending)
    (hne : es ≠ []) :
    let row := 128 * base + tid % 128
    ∃ u, At u 4329 [] ∧ Run kernel Assumptions.all l g u es ending ∧
      (∀ group : Fin 4, firstMaskOutputs u group (firstMaskedValue p batch row blocks score)) ∧
      ∀ r ∉ firstMaskSetupWrites, (∀ group : Fin 4, ¬ firstMaskGroupWrites group r) →
        u.regs r = t.regs r := by
  obtain ⟨u,hU,hLocal,hOut,hFrame⟩ :=
    firstCausalMaskLocal p batch tid base blocks score htid hLengths hK hQ hBlocks ht hscores
  exact ⟨u,hU,hr.after_local_nonempty hLocal hne,hOut,hFrame⟩

/-- The local replay continues a fully recorded lane trace. -/
theorem firstCausalMaskTrace {es : List Event} (p : Params) (batch tid base blocks : Nat)
    (score : Nat → Option ℝ) (htid : tid < 2^32) (hLengths : p.qLength batch ≤ p.kLength batch)
    (hK : p.kLength batch + 256 < 2^31) (hQ : 128 * base + tid % 128 < p.qLength batch + 256)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch)
    (ht : At t 3863
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (3219, b32 tid), (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    (hscores : firstMaskInputs t score) (hr : Run kernel Assumptions.all l g t es none) :
    let row := 128 * base + tid % 128
    ∃ u, At u 4329 [] ∧ Run kernel Assumptions.all l g u es none ∧
      (∀ group : Fin 4, firstMaskOutputs u group (firstMaskedValue p batch row blocks score)) ∧
      ∀ r ∉ firstMaskSetupWrites, (∀ group : Fin 4, ¬ firstMaskGroupWrites group r) →
        u.regs r = t.regs r := by
  obtain ⟨u,hU,hLocal,hOut,hFrame⟩ :=
    firstCausalMaskLocal p batch tid base blocks score htid hLengths hK hQ hBlocks ht hscores
  exact ⟨u,hU,hr.after_local hLocal,hOut,hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
