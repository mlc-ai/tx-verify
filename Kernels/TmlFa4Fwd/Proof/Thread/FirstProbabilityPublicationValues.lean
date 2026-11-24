-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilityOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityStoreOfCredit
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstPublication
import Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityScoreCount
import Kernels.TmlFa4Fwd.Proof.TmemGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.TcMma Thread.Scores Prologue

/-- The recorded first-round P stores form the actual packed tile of their row
and score visit, including when the lane continues to subsequent visits. -/
theorem firstProbabilityTileOfPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g j barInst electInst leader : Nat}
    (hStage : warpIndex l g/4 = stage.val) (weights : Nat → ℝ)
    (hEvents : ∀ i : Fin 10, X.get (g,j+i.val) =
      (firstPublicationEvents l g stage (fun q k => weights (32*q.val+k))
        barInst electInst leader)[i.val]?) :
    ObservedProbabilityTile l X g stage 0 weights := by
  intro q word
  let values (q : Fin 4) (k : Nat) := weights (32*q.val+k)
  let events := firstPublicationEvents l g stage values barInst electInst leader
  let offset := probabilityTraceIndex q
  let cut := if q = 3 then 8 else 5
  have hCut : cut < events.length := by fin_cases q <;> simp [cut,events,firstPublicationEvents]
  have hEnds : offset < cut := by fin_cases q <;> decide
  have hCutSite : events[cut].pc = probabilityPublicationEnd .first q := by
    fin_cases q <;> rfl
  have hGet (n : Nat) (hn : n < events.length) : X.get (g,j+n) = some events[n] := by
    have hn' : n < 10 := hn
    have h := hEvents ⟨n,hn'⟩
    change X.get (g,j+n) = events[n]? at h
    rwa [List.getElem?_eq_getElem hn] at h
  have hStore : X.get (g,j+offset) = some (firstStoreEvent l g stage q (values q)) := by
    fin_cases q
    · exact hEvents 1
    · exact hEvents 2
    · exact hEvents 3
    · exact hEvents 6
  have hSuffix : ProbabilityStoreVisitSuffix X g q (j+offset) (j+cut) := by
    apply ProbabilityStoreVisitSuffix.ofEvents q events hGet (by omega) (by omega)
    intro n hn hL hR later a vals shape he
    have hBefore : offset < n := by omega
    have hAfter : n < cut := by omega
    have hPc := congrArg Event.pc he
    fin_cases q <;> cases later <;>
      simp [offset,cut,probabilityTraceIndex] at hBefore hAfter <;>
      interval_cases n <;>
      simp [events,firstPublicationEvents,firstStoreEvent,probabilityPc] at hPc
  have hCol : probabilityColumn stage+16*q.val < 512 := by
    have := probabilityColumn_range stage
    have := scoreColumn_range stage
    have := q.isLt
    omega
  have hWord : PublishedProbabilityWord l X (g,j+offset)
      (tcDataCell l g .s32x32b (probabilityAddress l g stage q) word.val) stage := by
    rw [probabilityAddress,tcDataCell_warp32 l g word.val hCol]
    exact hSuffix.publishedWord hp hX .first q word hStage hStore (hGet cut hCut)
      hCutSite (by omega)
  exact ⟨j+offset,hWord,firstProbabilityScoreCount hp hX stage hStage q hStore,⟨_,hStore⟩⟩

/-- The actual first-round numeric replay supplies the packed tile given to PV,
independently of the number of later score visits. -/
theorem FirstRoundProgress.observedProbabilityTile {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {warp : Fin 8} {g j batch head row blocks biasCap pastTile : Nat}
    (hWarp : warp.val = warpIndex l g)
    (hRound : FirstRoundProgress p l X warp g j batch head row blocks biasCap pastTile) :
    let weights := fun col => shiftedWeight p batch head row (visitKey blocks 0 col)
      (firstReference p batch head row blocks)
    ObservedProbabilityTile l X g (stageOf warp) 0 weights := by
  have hStage : warpIndex l g/4 = (stageOf warp).val := by
    change warpIndex l g/4 = warp.val/4
    rw [hWarp]
  obtain ⟨_,_,_,_,_,_,hEvents,_⟩ := hRound
  exact firstProbabilityTileOfPublication hp hX (stageOf warp) hStage _ hEvents

end PTX.Kernels.TmlFa4Fwd.Softmax
