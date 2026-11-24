-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedPublicationPositions
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityStoreOfCredit
import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreCompletion
import Kernels.TmlFa4Fwd.Proof.TmemGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.TcMma Thread Thread.Scores Prologue

/-- A repeated round's actual probability store words on the producing lane. -/
theorem Repeated.publishedProbabilityWord {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (r : Repeated) (stage : Fin 2) {g j inst : Nat} (hStage : warpIndex l g/4 = stage.val)
    {weights : Nat → ℝ}
    (hEvents : ∀ i : Fin (r.probabilityEvents l g stage weights).length,
      X.get (g,j+i.val) = (r.probabilityEvents l g stage weights)[i.val]?)
    (hBar : X.get (g,j+r.probabilityTailBarrierOffset) =
      some ⟨probabilityWaitPc r.round true+1,.warpBar (2^32-1) inst⟩)
    (q : Fin 4) (word : Fin 16) :
    PublishedProbabilityWord l X (g,j+r.probabilityStoreOffset q)
      (tcDataCell l g .s32x32b (probabilityAddress l g stage q) word.val) stage := by
  let events := r.probabilityEvents l g stage weights
  let offset := r.probabilityStoreOffset q
  have hStore := r.probabilityStoreOfRound stage hEvents q
  have hCol : probabilityColumn stage+16*q.val < 512 := by
    have := probabilityColumn_range stage
    have := scoreColumn_range stage
    have := q.isLt
    omega
  rw [probabilityAddress,tcDataCell_warp32 l g word.val hCol]
  by_cases hQ : q = 3
  · subst q
    have hTerminal : r.probabilityStoreOffset 3 + 1 = events.length := by cases r <;> rfl
    have hBarPos := r.probabilityTailBarrierOffset_eq l g stage weights
    change r.probabilityTailBarrierOffset = events.length+1 at hBarPos
    obtain ⟨k,⟨site,hWait⟩,hK,hLast⟩ :=
      probabilityTailWaitBeforeWarpBarrier hp hX r.round r.round hStore hBar
        (by omega)
    have hKPos : k = j+events.length := by omega
    rw [hKPos] at hWait
    let full := events ++ [⟨site,.tc .waitSt⟩]
    have hFull : ∀ n (hn : n < full.length), X.get (g,j+n) = some full[n] := by
      intro n hn
      by_cases hN : n < events.length
      · have hAt := hEvents ⟨n,hN⟩
        change X.get (g,j+n) = events[n]? at hAt
        rw [hAt,List.getElem?_eq_getElem hN,List.getElem_append_left hN]
      · have hLen : n = events.length := by simp [full] at hn; omega
        subst n
        simpa [full] using hWait
    have hSuffix : ProbabilityStoreVisitSuffix X g 3 (j+r.probabilityStoreOffset 3)
        (j+r.probabilityTailBarrierOffset) := by
      apply ProbabilityStoreVisitSuffix.ofEvents 3 full hFull (by omega)
      · simp [full,hBarPos]
      · intro n hn hL hR later a values shape he
        have hN : n = events.length := by omega
        subst n
        have hGap : full[events.length] = ⟨site,.tc .waitSt⟩ := by simp [full]
        rw [hGap] at he
        cases congrArg Event.kind he
    exact hSuffix.publishedWord hp hX r.round 3 word hStage hStore hBar
      (by simp [probabilityPublicationEnd]) (by omega)
  · have hCredit := r.probabilityCreditOfRound stage hEvents
    have hLength : r.probabilityCreditOffset < events.length := by
      cases r <;> simp [events,Repeated.probabilityEvents,Repeated.probabilityCreditOffset]
    have hEnd : offset < r.probabilityCreditOffset := by
      cases r <;> fin_cases q <;> simp [offset,Repeated.probabilityCreditOffset,
        Repeated.probabilityStoreOffset] at hQ ⊢
    have hGet : ∀ n (hn : n < events.length), X.get (g,j+n) = some events[n] := by
      intro n hn
      have hAt := hEvents ⟨n,hn⟩
      change X.get (g,j+n) = events[n]? at hAt
      simpa only [List.getElem?_eq_getElem hn] using hAt
    have hSuffix : ProbabilityStoreVisitSuffix X g q (j+offset)
        (j+r.probabilityCreditOffset) := by
      apply ProbabilityStoreVisitSuffix.ofEvents q events hGet (by omega) (by omega)
      intro n hn hL hR later a values shape he
      have hEarlier : offset < n := by omega
      have hLater : n < r.probabilityCreditOffset := by omega
      have hPc := congrArg Event.pc he
      cases r <;> fin_cases q <;> cases later <;>
        simp [offset,Repeated.probabilityCreditOffset,
          Repeated.probabilityStoreOffset] at hEarlier hLater <;>
        interval_cases n <;>
        simp [events,Repeated.probabilityEvents,repeatedStoreEvent,Repeated.round,
          probabilityPc] at hPc
    exact hSuffix.publishedWord hp hX r.round q word hStage hStore hCredit
      (by cases r <;> simp [probabilityPublicationEnd,hQ,Repeated.round] <;> rfl)
      (by omega)

private theorem localProbabilityWords (weights : Nat → ℝ) (q : Fin 4) :
    (List.range' (16*q.val) 16).map (probabilityWord weights) =
      (List.range 16).map (probabilityWord (fun i => weights (32*q.val+i))) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 16
  · rw [List.getElem?_map,List.getElem?_map,List.getElem?_range' hk,
      List.getElem?_range hk]
    simp only [Option.map_some,probabilityWord]
    congr 4 <;> omega
  · have hK : 16 ≤ k := by omega
    rw [List.getElem?_map,List.getElem?_map]
    have hLeft : (List.range' (16*q.val) 16)[k]? = none := by
      apply List.getElem?_eq_none
      simpa using hK
    have hRight : (List.range 16)[k]? = none := by
      apply List.getElem?_eq_none
      simpa using hK
    simp [hLeft,hRight]

/-- The observed stores and their score count identify the packed tile of an
actual repeated visit, including the quarter after the early publication. -/
theorem Repeated.observedProbabilityTile {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (r : Repeated) (stage : Fin 2) {g j inst visit : Nat}
    (hStage : warpIndex l g/4 = stage.val) {weights : Nat → ℝ}
    (hEvents : ∀ i : Fin (r.probabilityEvents l g stage weights).length,
      X.get (g,j+i.val) = (r.probabilityEvents l g stage weights)[i.val]?)
    (hBar : X.get (g,j+r.probabilityTailBarrierOffset) =
      some ⟨probabilityWaitPc r.round true+1,.warpBar (2^32-1) inst⟩)
    (hCount : ∀ q : Fin 4, okPolls (scoreReadyObject l (g/l.block) stage)
      ((X.tr g).take (j+r.probabilityStoreOffset q)) = visit+1) :
    ObservedProbabilityTile l X g stage visit weights := by
  intro q word
  refine ⟨j+r.probabilityStoreOffset q,
    r.publishedProbabilityWord hp hX stage hStage hEvents hBar q word,hCount q,?_⟩
  refine ⟨probabilityPc r.round q,?_⟩
  have hStore := r.probabilityStoreOfRound stage hEvents q
  simpa only [repeatedStoreEvent,localProbabilityWords weights q] using hStore

end PTX.Kernels.TmlFa4Fwd.Softmax
