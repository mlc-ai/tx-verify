-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionChunkComputeProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionNormalizedChunkProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeSurface
import all Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeChunk

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Prologue

abbrev chunkVectors (l : Launch) (g : Nat) (stage : Fin 2) (chunk : Fin 16)
    (F : List (Nat × Value)) := finalizeVectorFrame l g stage (2*chunk.val+1) ++ F

abbrev chunkFrame (l : Launch) (g : Nat) (stage : Fin 2) (chunk : Fin 16)
    (F : List (Nat × Value)) :=
  normalizeStoreFacts l g stage chunk ++ chunkVectors l g stage chunk F

/-- A chunk with its decoded addresses prepared and load recorded, retaining the lane frame. -/
structure SurfaceLoadReached (l : Launch) (X : Execution) (g : Nat)
    (stage : Fin 2) (chunk : Fin 16) (F : List (Nat × Value)) where
  cursor : OpeningTripCursor l X g (finalizeLoadPc stage chunk) (chunkFrame l g stage chunk F)
  keeps : ∀ r ∈ (chunkVectors l g stage chunk F).map Prod.fst,
    r ∉ finalizeDataRegs stage chunk ∧
    (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
    (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) ∧
    (∀ half, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
    (chunk.val < 4 → r ≠ outputStoreAddrReg stage (finalizeVector chunk 1))
  destinations : List Nat
  words : List Value
  wordCount : words.length = 8
  decoded : kernel.code[finalizeLoadPc stage chunk]? =
    some ⟨none,.tcLd destinations (finalizeAddressReg stage chunk) .s32x32b none⟩
  load : X.get (g,cursor.pos) = some ⟨finalizeLoadPc stage chunk,
    .tc (.ld (outputAddress l g stage (8*chunk.val)) words .s32x32b)⟩
  returned : Run kernel Assumptions.all l g {} ((X.tr g).take (cursor.pos+1))
    (some (setRegs (next cursor.ready) destinations words))
  remaining : Run kernel Assumptions.all l g (setRegs (next cursor.ready) destinations words)
    ((X.tr g).drop (cursor.pos+1)) cursor.ending

theorem surfaceLoadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : LayoutInjective X)
    {g : Nat} (hg : g < l.threads) (stage : Fin 2) (chunk : Fin 16) (reciprocal : ℝ)
    {F : List (Nat × Value)} (hFrame : FinalizeSurfaceRegisters l g stage reciprocal F)
    (c : OpeningTripCursor l X g (finalizeSurfacePc stage chunk.val)
      (finalizeSurfaceFrame l g stage chunk.val F)) :
    ∃ d : SurfaceLoadReached l X g stage chunk F, d.cursor.pos = c.pos ∧
      d.cursor.ending = c.ending := by
  obtain ⟨s,hLocal,hs,hAddr,hKeeps⟩ := prepareFinalizeSurface hp stage chunk reciprocal hFrame
    c.checkpoint
  let F' := chunkFrame l g stage chunk F
  let addr := (finalizeAddressReg stage chunk,b32 (outputAddress l g stage (8*chunk.val)))
  let d : OpeningTripCursor l X g (finalizeLoadPc stage chunk) F' :=
    ⟨c.pos,c.before,s,c.ending,c.positive,c.bounded,c.released,hs,c.recorded,
      c.remaining,c.localSteps.trans hLocal⟩
  let withAddress : OpeningTripCursor l X g (finalizeLoadPc stage chunk) (addr::F') :=
    ⟨c.pos,c.before,s,c.ending,c.positive,c.bounded,c.released,
      hs.mono ⟨hAddr,hs.2.2.2.2⟩,c.recorded,c.remaining,c.localSteps.trans hLocal⟩
  obtain ⟨ds,words,_,hWords,hCode,he,hReturn,hRemaining⟩ :=
    finalizeLoadOfMaximal hp hMax hGuard hLayout hg stage chunk withAddress (.head _)
  exact ⟨⟨d,hKeeps,ds,words,hWords,hCode,he,hReturn,hRemaining⟩,rfl,rfl⟩

theorem SurfaceLoadReached.productsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    (hValues : ∀ i, CompletedValues l Assumptions.all X i) {g : Nat} (hg : g < l.threads)
    {stage : Fin 2} {chunk : Fin 16} {reciprocal : ℝ} {F : List (Nat × Value)}
    (c : SurfaceLoadReached l X g stage chunk F)
    (hFrame : FinalizeSurfaceRegisters l g stage reciprocal F)
    (hRelease : c.cursor.pos+1 = (X.tr g).length → Step.Released l X g) :
    Nonempty (ChunkProductsReached l X g c.cursor.pos stage chunk reciprocal
      (chunkFrame l g stage chunk F) c.cursor.ending) := by
  apply chunkProductsOfMaximal hp hMax hCuQ hValues hg stage chunk c.cursor c.wordCount c.decoded
    c.load c.returned c.remaining hRelease reciprocal
  · apply List.mem_append_right
    apply List.mem_append_right
    exact hFrame.recip
  · intro r hr
    change r ∈ (normalizeStoreFacts l g stage chunk ++ chunkVectors l g stage chunk F).map
      Prod.fst at hr
    rw [List.map_append,List.mem_append] at hr
    rcases hr with h | h
    · exact normalizeFacts_preserved l g stage chunk r h
    · have hK := c.keeps r h
      exact ⟨hK.1,hK.2.1,hK.2.2.1⟩

theorem SurfaceLoadReached.writesOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 12)
    {stage : Fin 2} {chunk : Fin 16} {reciprocal : ℝ} {F : List (Nat × Value)}
    (c : SurfaceLoadReached l X g stage chunk F)
    (d : ChunkProductsReached l X g c.cursor.pos stage chunk reciprocal
      (chunkFrame l g stage chunk F) c.cursor.ending)
    (hRelease : c.cursor.pos+2 = (X.tr g).length → Step.Released l X g) :
    ∃ after : OpeningTripCursor l X g (finalizeSurfacePc stage (chunk.val+1))
        (finalizeSurfaceFrame l g stage (chunk.val+1) F),
      after.pos = c.cursor.pos+10 ∧ after.ending = c.cursor.ending := by
  let G := chunkVectors l g stage chunk F
  let cur : OpeningTripCursor l X g (finalizeLoadPc stage chunk+10)
      (finalizeProductFacts stage chunk d.values reciprocal ++
        (normalizeStoreFacts l g stage chunk ++ G)) :=
    ⟨c.cursor.pos+2,d.before,d.ready,c.cursor.ending,by omega,len_of_get d.wait,
      hRelease,d.checkpoint,d.returned,d.remaining,d.localSteps⟩
  obtain ⟨_,u,hPos,hEnd⟩ := normalizedChunkWritesOfMaximal hp hMax hg hw stage chunk d.values
    reciprocal cur (fun r hr => (c.keeps r hr).2.2.2)
  have hAt := advanceFinalizeSurface stage chunk u.checkpoint
  exact ⟨⟨u.pos,u.before,u.ready,u.ending,u.positive,u.bounded,u.released,hAt,
    u.recorded,u.remaining,u.localSteps⟩,hPos,hEnd⟩

end PTX.Kernels.TmlFa4Fwd.Correction
