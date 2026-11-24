-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionVectorProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeChunk
import all Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeChunk

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Epilogue Prologue

/-- Both normalized vectors are recorded after the chunk wait. The successor
retains the last vector's address and all caller registers. -/
theorem normalizedChunkWritesOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 12)
    (stage : Fin 2) (chunk : Fin 16) (old : Nat → ℝ) (reciprocal : ℝ)
    {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (finalizeLoadPc stage chunk+10)
      (finalizeProductFacts stage chunk old reciprocal ++
        (normalizeStoreFacts l g stage chunk ++ F)))
    (hFrame : ∀ r ∈ F.map Prod.fst,
      (∀ half, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
      (chunk.val < 4 → r ≠ outputStoreAddrReg stage (finalizeVector chunk 1))) :
    (∀ half : Fin 2, ∀ j : Fin 4, X.get (g,c.pos+4*half.val+j.val) = some
      ⟨outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half),
        .wr {
          loc := (outputChunkLoc l g stage (finalizeSubset chunk) (rowOf l g)
            (finalizeVector chunk half).val).at (4*j.val)
          size := 4
          elem := j.val } (fl (old (4*half.val+j.val)*reciprocal)).toBytes⟩) ∧
    ∃ d : OpeningTripCursor l X g (outputStorePc stage (finalizeSubset chunk)
        (finalizeVector chunk 1)+1)
        ((outputStoreAddrReg stage (finalizeVector chunk 1),
          b32 (finalizeVectorAddress l g stage chunk 1)) :: F),
      d.pos = c.pos+8 ∧ d.ending = c.ending := by
  let facts := normalizeStoreFacts l g stage chunk
  let pairs := finalizeProductFacts stage chunk old reciprocal
  have hSPairs := (holds_append _ _ _).1 c.checkpoint.2.2.2.2
  have hS : At c.ready (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 0) - 2)
      (pairs ++ ((pairs ++ facts) ++ F)) := by
    rw [← firstVectorPc]
    have hP : Holds c.ready.regs (pairs ++ facts) :=
      (holds_append _ _ _).2 ⟨hSPairs.1,((holds_append _ _ _).1 hSPairs.2).1⟩
    exact c.checkpoint.mono ((holds_append _ _ _).2
      ⟨hSPairs.1,(holds_append _ _ _).2 ⟨hP,((holds_append _ _ _).1 hSPairs.2).2⟩⟩)
  have hA0 : c.ready.regs (outputStoreAddrReg stage (finalizeVector chunk 0)) =
      some (b32 (finalizeVectorAddress l g stage chunk 0)) :=
    ((holds_append _ _ _).1 hSPairs.2).1.1
  let first : OpeningTripCursor l X g
      (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 0)-2)
      (pairs ++ ((pairs ++ facts) ++ F)) :=
    ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,hS,
      c.recorded,c.remaining,c.localSteps⟩
  have hFresh := normalizeFirstFacts_preserved l g stage chunk old reciprocal
  obtain ⟨hFirst,v,hVPos,hVEnd⟩ := normalizedVectorOfMaximal hp hMax hg hw stage chunk 0
    old reciprocal first hA0 (by
      intro r hm
      rw [List.map_append,List.mem_append] at hm
      exact hm.elim (hFresh.1 r) (fun h => (hFrame r h).1 0))
  have hVFacts : Holds v.ready.regs facts :=
    ((holds_append _ _ _).1 ((holds_append _ _ _).1 v.checkpoint.2.2.2.2).1).2
  have hOther : if chunk.val < 4 then v.ready.regs 6500 = some (b32 (finalizeVectorDelta l g))
      else v.ready.regs (outputStoreAddrReg stage (finalizeVector chunk 1)) =
        some (b32 (finalizeVectorAddress l g stage chunk 1)) := by
    by_cases hc : chunk.val < 4
    · rw [ite_eq_left hc]
      exact holds_mem hVFacts (by simp [facts,normalizeStoreFacts,hc])
    · rw [ite_eq_right hc]
      exact holds_mem hVFacts (by simp [facts,normalizeStoreFacts,hc])
  obtain ⟨w,hA1,hW,hLocal⟩ := advanceFinalizeVectorLocal hp (g := g) stage chunk
    v.checkpoint hVFacts.1 hOther (by
      intro hc hm
      rw [List.map_append,List.mem_append] at hm
      exact hm.elim (hFresh.2 hc) (fun h => (hFrame _ h).2 hc rfl))
  let addr := (outputStoreAddrReg stage (finalizeVector chunk 1),
    b32 (finalizeVectorAddress l g stage chunk 1))
  have hSaved := (holds_append _ _ _).1 hW.2.2.2.2
  have hW' : At w (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1) - 2)
      (pairs ++ addr :: F) := hW.mono
        ((holds_append _ _ _).2 ⟨((holds_append _ _ _).1 hSaved.1).1,hA1,hSaved.2⟩)
  let second : OpeningTripCursor l X g
      (outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk 1)-2)
      (pairs ++ addr :: F) :=
    ⟨v.pos,v.before,w,v.ending,v.positive,v.bounded,v.released,hW',
      v.recorded,v.remaining,v.localSteps.trans hLocal⟩
  have hAddrKeep : ∀ q ∈ finalizeUnpacks stage chunk 1,
      q.2.1 ≠ addr.1 ∧ q.2.2 ≠ addr.1 := by
    dsimp only [addr]
    fin_cases stage <;> fin_cases chunk <;> decide
  obtain ⟨hSecond,u,hUPos,hUEnd⟩ := normalizedVectorOfMaximal hp hMax hg hw stage chunk 1
    old reciprocal second hA1 (by
      intro r hm
      rw [List.map_cons,List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact hAddrKeep
      · exact (hFrame r hm).1 1)
  refine ⟨?_,u,?_,hUEnd.trans hVEnd⟩
  · intro half j
    fin_cases half
    · exact hFirst j
    · simpa [second,first,hVPos] using hSecond j
  · simpa [second,first,hVPos] using hUPos

end PTX.Kernels.TmlFa4Fwd.Correction
