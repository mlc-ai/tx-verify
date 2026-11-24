-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMaskCursor
import Kernels.TmlFa4Fwd.Proof.SoftmaxMaskMaximum
import Kernels.TmlFa4Fwd.Proof.SoftmaxReference
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

/-- The opening maximum at the observed statistics notification includes all padded rows.
The mask and reduction both replay before the same lane's actual notification. -/
theorem OpeningAffineLane.maximumOfPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch wait : Nat} {stage : Fin 2}
    (lane : OpeningAffineLane p l X g batch stage wait)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hMore : lane.entry.pos < (X.tr g).length) :
    ∃ (u : TState) (mx : Option ℝ), At u (statsPc (some .first)) [(7256,scoreValue mx)] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop lane.entry.pos)
        lane.entry.arrival.loaded.opening.ending ∧
      X.get (g,lane.entry.pos) = some
        ⟨statsPc (some .first),.bar (3+lane.entry.arrival.loaded.opening.warp.val)
          (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g (next u) ((X.tr g).drop (lane.entry.pos+1))
        lane.entry.arrival.loaded.opening.ending ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take lane.entry.pos) u := by
  let entry := lane.entry
  let warp := entry.arrival.loaded.opening.warp
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let base := 2*tile+stage.val
  let blocks := Mma.trips p batch tile
  let row := 128*base+(g%l.block)%128
  let raw := firstBiasLogit (abiFloat p.invScaleBits)
    (firstBiasRegisterValue (openingBiasColumns p l g batch stage)) (firstQkRegisterValue lane.dot)
  let columns := firstMaskedValue p batch row blocks raw
  let mx := scoreMax columns (List.range 128)
  obtain ⟨t,ht,_,hRaw,_,hBar,hReach⟩ := lane.maskCursor hp
  have hLive : (X.tr g).drop entry.pos ≠ [] := by
    intro hEmpty
    change entry.pos < (X.tr g).length at hMore
    have hZero := congrArg List.length hEmpty
    simp only [List.length_drop,List.length_nil] at hZero
    omega
  have hMeta := hp.lengths batch hb
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hBound := (Mma.trips_bounds hp hb hTile).2.1
  have hBlocks : 128*(blocks-1) ≤ p.kLength batch := by
    change blocks ≤ (p.kLength batch+127)/128 at hBound
    omega
  have hTid : g%l.block < 2^32 := by
    rw [hp.block]
    have := Nat.mod_lt g (by decide : 0 < 512)
    omega
  have hRow : row < p.qLength batch+256 := by
    have hStage := stage.isLt
    have hLane := Nat.mod_lt (g%l.block) (by decide : 0 < 128)
    dsimp only [row,base]
    omega
  obtain ⟨v,hv,hMaskLocal,hScores,hMask⟩ :=
    firstCausalMaskLocal (g := g) p batch (g%l.block) base blocks raw hTid hMeta.2.1 hMeta.2.2
      hRow hBlocks ht hRaw
  obtain ⟨w,hw,hMaxLocal,_,hMax⟩ := firstMaskedMaxLocal (g := g) columns hv hScores
  obtain ⟨u,hu,hRefLocal,hReference⟩ :=
    finiteReferenceLocal (g := g) .first mx (hw.mono trivial) hw.2.2.2.2.1
  have hLocal := hReach.trans (hMaskLocal.trans (hMaxLocal.trans hRefLocal))
  have hEnd := entry.continuation.after_local_nonempty hLocal hLive
  have hSignal : u.regs 5127 = some (b32 (3+warp.val)) := by
    refine (hReference _ (by decide)).trans ((hMax _ (by decide +kernel)).trans ?_)
    refine (hMask _ (by decide +kernel) (fun group => ?_)).trans hBar
    have hGroup := group.isLt
    unfold firstMaskGroupWrites maskScratch maskPred
    omega
  have hMaxReg : u.regs 7256 = some (scoreValue mx) :=
    (hReference _ (by decide)).trans hw.2.2.2.2.1
  obtain ⟨hEvent,hAfter⟩ := statsTracePrefix hp.block (some .first) warp hu.1 hu.2.2.2.1
    hSignal hEnd hLive
  refine ⟨u,mx,hu.mono ⟨hMaxReg,trivial⟩,hEnd,hEvent,hAfter,?_⟩
  simpa only [List.append_nil] using entry.recorded.returning_reach.append (.of_local hLocal)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
