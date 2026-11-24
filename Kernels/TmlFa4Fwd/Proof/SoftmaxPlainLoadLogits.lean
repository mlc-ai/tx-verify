-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainVisitExtent
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainScoreEntry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedPlainScore

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.TcMma Prologue Epilogue Thread Thread.Scores

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hX hFrame

/-- On a supplied plain score cursor, the decoded loads and packs produce the masked
launch logits for its actual visit, preserving the other numerical registers. -/
theorem plainPackedLogitsFromLoadsOfFootprint (hCuQ : DrainCuQProtected p X) (warp : Fin 8)
    {g start last pc batch : Nat} {t : TState} (hWarp : warp.val = warpIndex l g)
    (ht : At t (scorePc .unbiased 0) [])
    (hAddr : ∀ q : Fin 4, t.regs (scoreReg .unbiased q) =
      some (b32 (scoreAddress l g (stageOf warp) q)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop start) none)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : let tile := (assignedCoordinates p batch (g/l.block)).1
      256*tile+128*(warpIndex l g/4)+(g%l.block)%128 < p.qLength batch) :
    ∃ u, let stage := stageOf warp
      let co := assignedCoordinates p batch (g/l.block)
      let trips := Mma.trips p batch co.1
      let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,start)
      let row := 256*co.1+128*stage.val+(g%l.block)%128
      let logit := fun c => maskedLogit p batch co.2 row (visitKey trips visit c)
      At u (repeatedMaxStart false) [] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+8)) none ∧
      (∀ q : Fin 4, X.get (g,start+2*q.val+1) = some ⟨scorePc .unbiased q,.tc .waitLd⟩) ∧
      (∀ q : Fin 4, ∃ values, X.get (g,start+2*q.val) = some
        ⟨scorePc .unbiased q,.tc (.ld (scoreAddress l g stage q) values .s32x32b)⟩) ∧
      (∀ n, (∀ q : Fin 4,
        (n < repeatedScoreWordBase .unbiased q ∨ repeatedScoreWordBase .unbiased q+32 ≤ n) ∧
        ∀ i : Fin 16, n ≠ repeatedScorePairReg .unbiased q i.val) → u.regs n = t.regs n) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop start).take 8) u ∧
      ∀ (q : Fin 4) (k : Fin 16),
        u.regs (repeatedScorePairReg .unbiased q k.val) =
          some (.pair (scoreValue (logit (32*q.val+2*k.val)))
            (scoreValue (logit (32*q.val+(2*k.val+1))))) := by
  obtain ⟨u,hAt,hTail,hWait,hKeep,hReads,hReach,hDots⟩ :=
    plainPackedDotsFromLoadsOfFootprint hp hX hCuQ hFrame warp hWarp ht hAddr hRun hb
      hLo hHi
  let stage := stageOf warp
  have hw : warpIndex l g < 8 := hWarp ▸ warp.isLt
  have hs : warpIndex l g/4 = stage.val := by rw [← hWarp]; rfl
  have hLive : let tile := (assignedCoordinates p batch (g/l.block)).1
      256*tile+128*stage.val+(g%l.block)%128 < p.qLength batch := by
    rw [← hs]
    exact hRow
  obtain ⟨words,hRead⟩ := hReads 0
  have hRead' : X.get (g,start) = some
      ⟨scorePc .unbiased 0,.tc (.ld (scoreAddress l g stage 0) words .s32x32b)⟩ := hRead
  obtain ⟨hPlain,hTrips⟩ := plainScoreVisitBounds hp hX hFrame hCuQ hw hs 0 hRead' hExit hb hLo hHi
  refine ⟨u,hAt,hTail,hWait,hReads,hKeep,hReach,?_⟩
  intro q k
  let lo : Fin 32 := ⟨2*k.val,by have := k.isLt; omega⟩
  let hi : Fin 32 := ⟨2*k.val+1,by have := k.isLt; omega⟩
  let head := (assignedCoordinates p batch (g/l.block)).2
  have hLow := plainVisitScoreDot hp stage (head := head) q lo hb hLive hTrips hPlain
  have hHigh := plainVisitScoreDot hp stage (head := head) q hi hb hLive hTrips hPlain
  simp only [firstScoreColumn,lo,hi] at hLow hHigh
  dsimp only
  rw [hLow,hHigh]
  exact hDots q k

end
end PTX.Kernels.TmlFa4Fwd.Softmax
