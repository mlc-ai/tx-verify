-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasVectorProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SelectedOpeningBiasAcquire
public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedBiasValues

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof Epilogue Prologue Thread.Scores

noncomputable section

/-- Two BF16 values of the selected row share each opening Bias vector word. -/
def openingBiasWord (p : Params) (l : Launch) (g batch : Nat) (stage : Fin 2)
    (i : Fin 16) (word : Nat) : Value :=
  let coords := assignedCoordinates p batch (g/l.block)
  let row := 128 * (2 * coords.1 + stage.val) + (g % l.block) % 128
  let bias := firstVisitBiasValue p batch row coords.2
  biasLoadWord (bias (8*i.val+2*word)) (bias (8*i.val+2*word+1))

/-- The actual opening Bias reads have delivered the selected row at the proxy fence. -/
structure OpeningBiasReadLane (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) (stage : Fin 2) (wait : Nat) where
  opening : OpeningBiasLane p l X g batch stage wait
  cursor : OpeningLaneCursor l X g 3581
    (openingScoreReturnedFacts p l g batch (assignedCoordinates p batch (g/l.block)).1
      opening.warp) opening.ending
  position : cursor.pos = wait+65
  words : ∀ i, BiasWordReads l X false i g (wait+1+4*i.val)
    (biasVectorBase l g stage false i) (openingBiasWord p l g batch stage i)
  unpacked : ∀ i, BiasUnpacked false i cursor.ready (openingBiasWord p l g batch stage i)
  scores : OpeningScoreBeforeBias l X g stage cursor.ready

/-- The actual first Bias bytes suffice for every vector load and unpack, even on an
unfinished maximal prefix and with later writes to the same physical Bias buffers. -/
theorem OpeningBiasLane.readsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hCuQ : DrainCuQProtected p X)
    {g batch wait : Nat} {stage : Fin 2} (hWait : FirstBiasAcquire l X g wait stage)
    (opening : OpeningBiasLane p l X g batch stage wait) (hg : g < l.threads)
    (hWarp : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) :
    Nonempty (OpeningBiasReadLane p l X g batch stage wait) := by
  let words := openingBiasWord p l g batch stage
  obtain ⟨after,hPos,hReads,hFrame⟩ := openingBiasVectorsOfMaximal hp hMax hGuard hg opening.warp
    opening.cursor opening.position words (fun _ _ _ => biasLoadWordShape _ _)
    (fun i k hk bs he => by
      rw [opening.selectedStage] at he
      exact firstBiasValuesInPrefix hp hMax.1 hCuQ hb hLo hHi hWarp writes hWait i k hk bs he)
  have hScoreRegs (q : Fin 4) (k : Nat) (hk : k < 16) (i : Fin 16) :
      biasVectorKeeps false i (firstScorePairReg q k) := by
    constructor
    · have hBound : ∀ i : Fin 16, ∀ r ∈ biasReadRegs false i, r < 3075 := by decide
      intro hm
      have h := hBound i _ hm
      unfold firstScorePairReg at h
      omega
    · right
      have hI := i.isLt
      simp only [biasUnpackRegs,biasUnpackTop,Bool.false_eq_true,ite_false,firstScorePairReg]
      omega
  refine ⟨⟨opening,after,hPos,?_,fun i => (hReads i).2,?_⟩⟩
  · intro i
    simpa only [opening.selectedStage] using (hReads i).1
  · exact opening.scores.withFrame (fun q k hk => hFrame _ (hScoreRegs q k hk))

end
end PTX.Kernels.TmlFa4Fwd.Softmax
