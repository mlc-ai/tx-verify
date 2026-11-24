-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Snoc.SnocWaiting
public import Lemmas.Snoc.SnocMemory
public import Lemmas.Snoc.Collectives
public import Lemmas.Step.SetMaxNReg

@[expose] public section

namespace PTX
noncomputable section

/-- Instructions in the non-async fragment cannot introduce these resource operations, fences,
lane-value collectives or matrix instances. The existing history provenance is preserved by
source-trace extension. An appended read-modify-write changes the atomic operations, so the
atomicity of the extension is a premise. -/
theorem noAsync_snoc_obligations {L : Launch} {X : Execution} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}
    (hX : Consistent L K A mem0 X) (hn : X.NoTma) (hk : e.kind.isTma = false)
    (hatomic : AtomicOk L (X.snoc g e r)) :
    ExtensionObligations L A (X.snoc g e r) := by
  let Y := X.snoc g e r
  have hny : Y.NoTma := hn.snoc hk
  have hy := snoc_emptyAsync (g := g) (e := e) (r := r) (hn.emptyAsync hX)
  have le : X.le Y := le_snoc
  have hhist : ∀ cta, Y.tmemHistory cta = [] := hn.emptyHistory hX.tmemPair
  have hpairing : Y.tmemPairing = [] := hn.emptyPairing hX.tmemPair
  change ExtensionObligations L A Y
  have hsc : ∀ v s, ¬ Y.ThreadFence v .sc s := by
    rintro v s ⟨pc, hv⟩
    cases hny _ _ _ hv
  refine {
    ctaBar := hX.ctaBar.snoc, cluster := hX.cluster.preserving le rfl,
    elect := ?_, vote := ?_, warpValue := ?_,
    warpBar := ?_, matrix := matrixOk_of_none L ?_, clc := ?_, tensor := ?_,
    store := ?_, atomic := hatomic, fenceSc := fenceScOk_of_noSc hsc, tmemPair := ?_,
    tmemPairResult := ?_, tcCommit := ?_,
    tmemPairCompletion := Tmem.Pair.completionClosed_of_growth le rfl rfl hX.tmemPair
      hX.tmemPairCompletion,
    mmaCompletion := TcMma.completionClosed_of_growth le rfl hX.tma.2.1 hX.mmaCompletion,
    tcRead := ?_,
    reduce := hX.reduce.snoc fun s h => by rw [h] at hk; cases hk }
  · refine ⟨?_,?_,?_⟩
    · intro i pc mask inst leader hi; cases hny _ _ _ hi
    · intro i j pc pc' mask mask' inst leader leader' hi; cases hny _ _ _ hi
    · intro i j pc pc' mask inst inst' leader leader' hi; cases hny _ _ _ hi
  · intro g' i n pc mask a ballot hget; cases hny _ _ _ hget
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro g' i pc mode mask a r' n hget; cases hny _ _ _ hget
    · intro g' i pc op signed mask a r' n hget; cases hny _ _ _ hget
    · intro g' i pc all wide mask a r' p n hget; cases hny _ _ _ hget
    · intro g' i pc r' hget; cases hny _ _ _ hget
  · constructor
    · intro i mask inst ⟨pc,hi⟩; cases hny _ _ _ hi
    · intro i j mask mask' inst ⟨pc,hi⟩; cases hny _ _ _ hi
  · intro v ev hv
    obtain ⟨pc, k⟩ := ev
    have := hny _ _ _ hv
    cases k <;> simp_all [isMatrix, Kind.isTma]
  · refine ⟨hX.clc.1, ?_, ?_, ?_, ?_⟩
    · intro request answer hr
      obtain ⟨i,s,targets,hid,hi⟩ := hX.clc.2.1 request answer hr
      exact ⟨i,s,targets,hid,(snoc_clcIssue hk).mpr hi⟩
    · intro i hi
      obtain ⟨s,targets,hi⟩ := hX.clc.2.2.1 i hi
      exact ⟨s,targets,(snoc_clcIssue hk).mpr hi⟩
    · intro i s targets ⟨pc,hi⟩; cases hny _ _ _ hi
    · rintro ⟨i,s,targets,pc,hi⟩; cases hny _ _ _ hi
  · intro i obs hi
    have hh := (hy.2.2 i).1
    rw [hh] at hi; cases hi
  · intro i obs hi
    have hh := (hy.2.2 i).2.1
    rw [hh] at hi; cases hi
  · simp [Tmem.Pair.HistoriesOk, Tmem.Pair.RequestHistory, Tmem.Pair.runRequests,hhist,hpairing]
  · exact hny.noTc.pairResult
  · intro i rank hi
    have hh := (hy.2.2 i).2.2.2
    rw [hh] at hi; cases hi
  · refine ⟨fun i address vals sh j source cell value ⟨pc, hi⟩ => ?_,
      fun i _ _ _ _ _ _ hs => ?_⟩
    · cases hny _ _ _ hi
    · obtain ⟨_, _, _, _, ⟨pc, hi⟩, _⟩ := hs
      cases hny _ _ _ hi

end
end PTX
