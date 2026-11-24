-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilityOrder
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitCorrectionWrites
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.Proof Prologue Epilogue

private theorem probabilityCellOverlap {l : Launch} (g h : Nat)
    (stage writtenStage : Fin 2) (q writtenQuarter : Fin 4) {word k : Nat}
    (hWord : word < 16) (hk : k < 16)
    (he : tcDataCell l g .s32x32b (probabilityAddress l g stage q) word =
      tcDataCell l h .s32x32b (probabilityAddress l h writtenStage writtenQuarter) k) :
    g/l.block = h/l.block ∧ tmemRow l g = tmemRow l h ∧
      stage = writtenStage ∧ q = writtenQuarter := by
  have hAddr (s : Fin 2) (q : Fin 4) : probabilityColumn s+16*q.val < 512 := by
    have hCol := scoreColumn_range s
    have hP := probabilityColumn_range s
    have hQ := q.isLt
    omega
  rw [probabilityAddress,probabilityAddress,tcDataCell_warp32 l g word (hAddr stage q),
    tcDataCell_warp32 l h k (hAddr writtenStage writtenQuarter)] at he
  refine ⟨congrArg Cell.cta he,Fin.ext (congrArg Cell.lane he),?_,?_⟩
  all_goals
    have hCol := congrArg Cell.column he
    change probabilityColumn stage+16*q.val+word =
      probabilityColumn writtenStage+16*writtenQuarter.val+k at hCol
    have hQ := q.isLt
    have hQ' := writtenQuarter.isLt
    unfold probabilityColumn scoreColumn at hCol
    exact Fin.ext (by omega)

/-- A valid row's single-visit publication gives the only explicit store to each of its
packed probability cells. MMA writers to those cells are handled separately. -/
theorem singleVisitProbabilityStoreUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {warp : Fin 8} {g j batch head row cap past : Nat}
    (hg : g < l.threads) (hw : warp.val = warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hCap : 0 < cap) (hBound : cap < 2^31) (hPast : past+256 < 2^31)
    (hRound : FirstRoundProgress p l X warp g j batch head row 1 cap past)
    (q : Fin 4) {word : Nat} (hWord : word < 16) {other : EvId}
    (hWrite : StoreCell l X other (tcDataCell l g .s32x32b
      (probabilityAddress l g (stageOf warp) q) word)) :
    other = (g,j+1+probabilityTraceIndex q) := by
  obtain ⟨h,index⟩ := other
  obtain ⟨a,vals,shape,k,⟨pc,he⟩,hk,hCell⟩ := hWrite
  rcases Thread.tensorStoreSite hX he with ⟨round,q',rfl⟩ | ⟨s,chunk,rfl⟩
  · obtain ⟨w,hw',rfl,hLen,rfl⟩ := Thread.Scores.probabilityStoreAddress hp hX round q' he
    obtain ⟨hCta,hRow,hStage,hQuarter⟩ :=
      probabilityCellOverlap g h (stageOf warp) (stageOf w) q q' hWord (hLen ▸ hk) hCell
    have hG : g % l.block / 128 = (stageOf warp).val := by
      change g % l.block / 128 = warp.val / 4
      rw [hw]
      simp only [warpIndex,Nat.div_div_eq_div_mul,show 32*4 = 128 by decide]
    have hH : h % l.block / 128 = (stageOf w).val := by
      change h % l.block / 128 = w.val / 4
      rw [hw']
      simp only [warpIndex,Nat.div_div_eq_div_mul,show 32*4 = 128 by decide]
    have hLane := scoreSameLane ⟨hg,event_thread_lt hX he,hCta⟩
      (hG.trans ((congrArg Fin.val hStage).trans hH.symm)) hRow
    change g = h at hLane
    subst h
    subst q'
    have hId := (firstProbabilityStoresUnique hp hX hCap hBound hPast hRound q he).2
    exact congrArg (fun n => (g,n)) hId
  · have hCta : g/l.block = h/l.block := by
      simpa only [tcDataCell_cta] using congrArg Cell.cta hCell
    exact (singleVisitNoCorrectionStore hp hX hFrame (i := (h,index)) hb
      (hCta ▸ hLo) (hCta ▸ hHi) (hCta ▸ hTrip) s chunk he).elim

end PTX.Kernels.TmlFa4Fwd.Softmax
