-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFirstStageStaging
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFirstStageStaging

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Prologue Epilogue

private theorem FirstOutputLoadIssued.surfaceCursor {p : Params} {l : Launch}
    {Y X : Execution} (hTrace : Y.tr = X.tr) {g batch lane : Nat}
    (c : FirstOutputLoadIssued p l Y g batch lane) :
    Nonempty (OpeningTripCursor l X (warpLane l g lane) (finalizeSurfacePc 0 0)
      (finalizeSurfaceFrame l (warpLane l g lane) 0 0
        (firstChunkFrame p l g batch lane c.acquired.sum c.acquired.maximum))) := by
  let thread := warpLane l g lane
  let F := firstChunkFrame p l g batch lane c.acquired.sum c.acquired.maximum
  have hVec : finalizeVectorFact l thread 0 0 ∈ F := by
    simp [F,thread,firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts]
  have hAt : At c.loadCursor.ready (finalizeSurfacePc 0 0)
      (finalizeSurfaceFrame l thread 0 0 F) := by
    have held : Holds c.loadCursor.ready.regs F := c.loadCursor.checkpoint.2.2.2.2
    exact c.loadCursor.checkpoint.mono ⟨holds_mem held hVec,held⟩
  have inside : c.loadCursor.pos < (X.tr thread).length := by
    rw [← hTrace]
    exact len_of_get c.issued
  exact ⟨⟨c.loadCursor.pos,c.loadCursor.before,c.loadCursor.ready,c.loadCursor.ending,
    c.loadCursor.positive,inside.le,fun eq => (inside.ne eq).elim,hAt,
    by simpa only [hTrace] using c.loadCursor.recorded,
    by simpa only [hTrace] using c.loadCursor.remaining,c.loadCursor.localSteps⟩⟩

/-- From the recorded first load for each row, the whole warp stages all sixteen
chunks and reaches the first stage's publication boundary. -/
theorem firstStageStagingOfIssuedLoads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : OutputFootprint p X) (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {lead batch : Nat} (hRole : 8 ≤ warpIndex l lead ∧ warpIndex l lead < 12)
    (hFirst : ∀ g, SameWarp l lead g → ∃ Y, Y.tr = X.tr ∧
      Nonempty (FirstOutputLoadIssued p l Y g batch (laneOf l g))) :
    ∀ g, SameWarp l lead g → Nonempty (FirstStageStagingDone p l X g batch) := by
  classical
  let c g hw := Classical.choice (Classical.choose_spec (hFirst g hw)).2
  let total (g : Nat) := if hw : SameWarp l lead g then (c g hw).acquired.sum else 0
  let maximum (g : Nat) :=
    if hw : SameWarp l lead g then (c g hw).acquired.maximum else none
  let r (g : Nat) := 1 / (if total g = 0 then 1 else total g)
  let F (g : Nat) := firstChunkFrame p l g batch (laneOf l g) (total g) (maximum g)
  have hSelf (g : Nat) (hw : SameWarp l lead g) : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hw.1.2.1,hw.1.2.1,rfl⟩,rfl⟩
  have hF (g : Nat) (hw : SameWarp l lead g) : FinalizeSurfaceRegisters l g 0 (r g) (F g) := by
    simpa only [hSelf g hw] using
      firstChunkSurfaceRegisters p l g batch (laneOf l g) (total g) (maximum g)
  have hEntry (g : Nat) (hw : SameWarp l lead g) :
      Nonempty (OpeningTripCursor l X g (finalizeSurfacePc 0 0)
        (finalizeSurfaceFrame l g 0 0 (F g))) := by
    have h := FirstOutputLoadIssued.surfaceCursor (Classical.choose_spec (hFirst g hw)).1 (c g hw)
    simpa only [F,total,maximum,dite_eq_left hw,hSelf g hw] using h
  intro g hw
  obtain ⟨after,_,_⟩ := surfaceWarpThroughAfterRescale hp hMax hOutputs hValues hRole
    0 r hF 0 (fun q hq => Classical.choice (hEntry q hq)) 16 (by decide)
    g hw
  have hValid : Softmax.DenominatorValid (total g) (maximum g) := by
    simpa only [total,maximum,dite_eq_left hw] using (c g hw).acquired.valid
  exact ⟨⟨total g,maximum g,hValid,after⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
