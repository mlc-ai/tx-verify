-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFirstStagedChunk
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSurfaceWarpProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Prologue Epilogue

private def firstChunkKeys : List Nat :=
  [9259,6496,6515,739,6513,6512,6498,6508,6511,6500,6502,6504,7134,1636,5967,1634,1635,
    1625,1626,1627,1628,1629,1633,1630,1631,1632,7131,7287,723,7277,7276,9605,784,1615,
    5868,1614,1613,1612,1072,1062,2535,1063,1064,1065,1066,1067,1068,6495,2390,1069,
    1070,6497,1071,1,7492,7493,7494,7495,1663,1664,7496,7497,7498,7499,7500,7501,7502,
    7503,7504,7505,7291,7290,7289,7506,7292,7293,7294,7295,1665]

private theorem firstChunkKeeps (chunk : Fin 16) :
    ∀ r ∈ firstChunkKeys,
      r ∉ finalizeDataRegs 0 chunk ∧
      (∀ q ∈ finalizePacks 0 chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls 0 chunk, q.1 ≠ r) ∧
      (∀ half, ∀ q ∈ finalizeUnpacks 0 chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
      (chunk.val < 4 → r ≠ outputStoreAddrReg 0 (finalizeVector chunk 1)) := by
  fin_cases chunk <;> decide +kernel

private theorem firstChunkTmemFresh (chunk : Fin 16) :
    0 < chunk.val → finalizeAddressReg 0 chunk ∉ firstChunkKeys := by
  fin_cases chunk <;> decide +kernel

private theorem firstChunkEvenFresh (chunk : Fin 16) :
    0 < chunk.val → chunk.val < 4 →
      outputStoreAddrReg 0 (finalizeVector chunk 0) ∉ firstChunkKeys := by
  fin_cases chunk <;> decide +kernel

private theorem firstChunkSurfaceRegisters (p : Params) (l : Launch) (g batch lane : Nat)
    (sum : ℝ) (maximum : Option ℝ) :
    FinalizeSurfaceRegisters l (warpLane l g lane) 0 (1 / (if sum = 0 then 1 else sum))
      (firstChunkFrame p l g batch lane sum maximum) := by
  let thread := warpLane l g lane
  let F := firstChunkFrame p l g batch lane sum maximum
  have hBase : (1629,b32 (outputAddress l thread 0 0)) ∈ F := by
    simp [F,thread,firstChunkFrame,firstTerminalReciprocalFrame,correctionBeforeRescale,
      tileSetupFrame,correctionTileGeometryFacts]
  have hKeys : F.map Prod.fst = firstChunkKeys := rfl
  refine ⟨hBase,hBase,?_,?_,.head _,?_,?_,?_⟩
  · simp [firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts,finalizeDeltas]
  · intro chunk hn hc
    have h : chunk.val = 1 ∨ chunk.val = 2 ∨ chunk.val = 3 := by omega
    rcases h with h | h | h
    · have he : chunk = 1 := Fin.ext h
      subst chunk
      simp [firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts,
        finalizeDeltas,finalizeEvenDeltaReg]
    · have he : chunk = 2 := Fin.ext h
      subst chunk
      simp [firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts,
        finalizeDeltas,finalizeEvenDeltaReg]
    · have he : chunk = 3 := Fin.ext h
      subst chunk
      have hd : finalizeEvenDelta l thread 3 = finalizeEvenDelta l thread 1 := rfl
      simp [thread,firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts,
        finalizeDeltas,finalizeEvenDeltaReg,hd]
  · intro chunk hn rv hr he
    exact firstChunkTmemFresh chunk hn (hKeys ▸ he ▸ List.mem_map_of_mem hr)
  · intro chunk hn hc rv hr he
    exact firstChunkEvenFresh chunk hn hc (hKeys ▸ he ▸ List.mem_map_of_mem hr)
  · intro chunk r hr
    have hKey : r ∈ F.map Prod.fst := hr
    rw [hKeys] at hKey
    exact firstChunkKeeps chunk r hKey

private theorem FirstStagedChunk.surfaceCursor {p : Params} {l : Launch}
    {Y X : Execution} (hTrace : Y.tr = X.tr) {g batch lane : Nat}
    (c : FirstStagedChunk p l Y g batch lane) :
    Nonempty (OpeningTripCursor l X (warpLane l g lane) (finalizeSurfacePc 0 1)
      (finalizeSurfaceFrame l (warpLane l g lane) 0 1
        (firstChunkFrame p l g batch lane c.source.source.acquired.sum
          c.source.source.acquired.maximum))) := by
  let thread := warpLane l g lane
  let F := firstChunkFrame p l g batch lane c.source.source.acquired.sum
    c.source.source.acquired.maximum
  have hVec : finalizeVectorFact l thread 0 0 ∈ F := by
    simp [F,thread,firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts]
  have hAt : At c.cursor.ready (finalizeSurfacePc 0 1)
      (finalizeSurfaceFrame l thread 0 1 F) := by
    have hFrame := c.cursor.checkpoint.2.2.2.2
    apply c.cursor.checkpoint.mono
    change Holds c.cursor.ready.regs
      (finalizeVectorFact l thread 0 0::finalizeVectorFact l thread 0 1::F)
    exact ⟨holds_mem hFrame.2 hVec,hFrame⟩
  have hRelease (hLast : c.cursor.pos = (X.tr thread).length) : Step.Released l X thread := by
    obtain ⟨stage,subbox,chunk,he⟩ := (c.written 1 3).decoded
    let j := c.source.source.loadCursor.pos+9
    simp only [Execution.get,hTrace] at he
    have hEnd : j+1 = (X.tr thread).length := by
      rw [c.position] at hLast
      omega
    exact releasedIfLast (X := X) (g := thread) (n := j) he (by simp [Kind.resume]) hEnd
  exact ⟨⟨c.cursor.pos,c.cursor.before,c.cursor.ready,c.cursor.ending,c.cursor.positive,
    by simpa only [hTrace] using c.cursor.bounded,hRelease,hAt,
    by simpa only [hTrace] using c.cursor.recorded,by simpa only [hTrace] using c.cursor.remaining,
    c.cursor.localSteps⟩⟩

/-- The complete first stage's normalized staging surface is populated, and
the real lane is ready to publish its staging writes. -/
structure FirstStageStagingDone (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  sum : ℝ
  maximum : Option ℝ
  valid : Softmax.DenominatorValid sum maximum
  cursor : OpeningTripCursor l X g (outputFencePc 0)
    (finalizeSurfaceFrame l g 0 16 (firstChunkFrame p l g batch (laneOf l g) sum maximum))

/-- Given the real first chunk for each row, the whole warp stages all sixteen
chunks and reaches the first stage's publication boundary. -/
theorem firstStageStagingAfterRescale {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : OutputFootprint p X) (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {lead batch : Nat} (hRole : 8 ≤ warpIndex l lead ∧ warpIndex l lead < 12)
    (hFirst : ∀ g, SameWarp l lead g → ∃ Y, Y.tr = X.tr ∧
      Nonempty (FirstStagedChunk p l Y g batch (laneOf l g))) :
    ∀ g, SameWarp l lead g → Nonempty (FirstStageStagingDone p l X g batch) := by
  classical
  let c g hw := Classical.choice (Classical.choose_spec (hFirst g hw)).2
  let total (g : Nat) := if hw : SameWarp l lead g then (c g hw).source.source.acquired.sum else 0
  let maximum (g : Nat) :=
    if hw : SameWarp l lead g then (c g hw).source.source.acquired.maximum else none
  let r (g : Nat) := 1 / (if total g = 0 then 1 else total g)
  let F (g : Nat) := firstChunkFrame p l g batch (laneOf l g) (total g) (maximum g)
  have hSelf (g : Nat) (hw : SameWarp l lead g) : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hw.1.2.1,hw.1.2.1,rfl⟩,rfl⟩
  have hF (g : Nat) (hw : SameWarp l lead g) : FinalizeSurfaceRegisters l g 0 (r g) (F g) := by
    simpa only [hSelf g hw] using
      firstChunkSurfaceRegisters p l g batch (laneOf l g) (total g) (maximum g)
  have hEntry (g : Nat) (hw : SameWarp l lead g) :
      Nonempty (OpeningTripCursor l X g (finalizeSurfacePc 0 1)
        (finalizeSurfaceFrame l g 0 1 (F g))) := by
    have h := FirstStagedChunk.surfaceCursor (Classical.choose_spec (hFirst g hw)).1 (c g hw)
    simpa only [F,total,maximum,dite_eq_left hw,hSelf g hw] using h
  intro g hw
  obtain ⟨after,_,_⟩ := surfaceWarpThroughAfterRescale hp hMax hOutputs hValues hRole
    0 r hF 1 (fun q hq => Classical.choice (hEntry q hq)) 15 (by decide)
    g hw
  have hValid : Softmax.DenominatorValid (total g) (maximum g) := by
    simpa only [total,maximum,dite_eq_left hw] using (c g hw).source.source.acquired.valid
  exact ⟨⟨total g,maximum g,hValid,after⟩⟩

theorem firstStageStagingOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : OutputFootprint p X) (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {lead batch : Nat} (hRole : 8 ≤ warpIndex l lead ∧ warpIndex l lead < 12)
    (_hb : batch < p.batch) (_hLo : tilePrefix p batch*p.heads ≤ lead/l.block)
    (_hHi : lead/l.block < tilePrefix p (batch+1)*p.heads)
    (_hSingle : Mma.trips p batch (assignedCoordinates p batch (lead/l.block)).1 = 1)
    (hFirst : ∀ g, SameWarp l lead g → ∃ Y, Y.tr = X.tr ∧
      Nonempty (FirstStagedChunk p l Y g batch (laneOf l g))) :
    ∀ g, SameWarp l lead g → Nonempty (FirstStageStagingDone p l X g batch) := by
  exact firstStageStagingAfterRescale hp hMax hOutputs hValues hRole hFirst

end PTX.Kernels.TmlFa4Fwd.Correction
