-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedFinalizationLoad
public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitNormalization
public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalPublishedWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.TcMma Epilogue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Protocol (PvVisit)

noncomputable section

/-- The actual final computation normalizes the terminal PV numerator using
the sum read from the matching final statistics publication. -/
theorem normalizedStageOfTerminalRow {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g pos batch : Nat} (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : stageRow (assignedCoordinates p batch (g/l.block)).1 stage+rowOf l g <
      p.qLength batch)
    {t : TState} {F : List (Nat × Value)}
    (ht : At t (statsBarrierPc stage false) F)
    (hFrame : ∀ sum maximum, FinalStageFrame l g stage sum maximum F)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none)
    (ref : Nat → Option ℝ) (sums : Nat → ℝ) (acc : Nat → Nat → ℝ) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row : Fin 128 := ⟨rowOf l g,Nat.mod_lt _ (by decide)⟩
    let qrow := stageRow coords.1 stage+row.val
    let blocks := trips p batch coords.1
    let last := blocks-1
    let old := fun (chunk : Fin 16) (k : Nat) => acc last (8*chunk.val+k)
    SoftmaxRun p batch coords.2 qrow blocks ref sums acc →
    (CorrectionWaits X (g,pos) .terminal stage → pos+1 < (X.tr g).length →
      ∃ pub maximum,
        TerminalPublishedWords l X g stage pub (fl (sums last)) (fl maximum) ∧
        TerminalGeneration l X g stage (pub-2) pos) →
    (∀ (col : Fin 128) (source : EvId),
      source.1/l.block = g/l.block →
      X.async.mmaDone source = true →
      PvVisit l X source.1 (firstPvBlock false stage) (2*blocks-1) row col source.2 →
      TcMma.Result l Assumptions.all X source ⟨g/l.block,row.val,outputColumn stage+col.val⟩
        (.float .f32 (acc last col.val))) →
    ∃ (maximum : ℝ) (start : Nat) (u : TState), pos+6 ≤ start ∧
      NormalizedOutput l X g start stage old (normalizingReciprocal (sums last)) ∧
      (∀ (chunk : Fin 16) (k : Fin 8),
        old chunk k.val * normalizingReciprocal (sums last) =
          attention p batch coords.2 qrow (8*chunk.val+k.val)) ∧
      At u (outputFencePc stage+3) (finalStageLoadFacts l stage (sums last) maximum F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+163)) none := by
  dsimp only
  intro hSpec hWords hNumerator
  let coords := assignedCoordinates p batch (g/l.block)
  let qrow := stageRow coords.1 stage+rowOf l g
  let blocks := trips p batch coords.1
  let last := blocks-1
  let old := fun (chunk : Fin 16) (k : Nat) => acc last (8*chunk.val+k)
  have hBarrier := holds_mem ht.2.2.2.2 (hFrame 0 0).barrier
  obtain ⟨he,_,hTail⟩ := observeStatsBarrier hp stage false ht hBarrier hRun
  have hTerm := terminalWaitObservation stage he
  have hPass : pos+1 < (X.tr g).length := by
    by_contra! h
    rw [List.drop_eq_nil_iff.mpr h] at hTail
    cases hTail
  obtain ⟨pub,maximum,hPublished,hGeneration⟩ := hWords hTerm hPass
  have hInputs : FinalStageInputs l X g pos stage (sums last) maximum old := by
    constructor
    · intro _ he
      exact hPublished.read hp hX hTerm rfl rfl hGeneration 0 ⟨_,he⟩
    · intro _ he
      exact hPublished.read hp hX hTerm rfl rfl hGeneration 1 ⟨_,he⟩
    · intro n k _ _ chunk vals he
      exact finalizationLoadValuesOfTerminalPv hp hX hDone hFootprint stage chunk
        (load := (g,pos+4+n+1+k+1+10*chunk.val)) he hb hLo hHi (acc last)
        (fun j source hCta _ hComplete hPv =>
          hNumerator ⟨8*chunk.val+j.val,by have := chunk.isLt; have := j.isLt; omega⟩
            source hCta hComplete hPv)
  obtain ⟨start,u,hStart,hWrite,hu,hU⟩ := observeFinalStage hp stage (sums last) maximum old
    ht (hFrame (sums last) maximum) hInputs hRun
  have hBound : qrow < 256*(coords.1+1) := by
    have hr : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    have hs := stage.isLt
    unfold qrow stageRow
    omega
  have hCover : p.keyCount batch qrow ≤ 128*blocks := p.keyCount_le_kvBlocks hBound
  have hPositive : 0 < blocks := by
    have hKey : 0 < p.keyCount batch qrow := hp.keyCount_pos hb hRow
    omega
  refine ⟨maximum,start,u,hStart,hWrite,?_,hu,hU⟩
  intro chunk k
  have hd : 8*chunk.val+k.val < 128 := by have := chunk.isLt; have := k.isLt; omega
  exact (hSpec.result hPositive (hp.keyCount_pos hb hRow) hCover hd).1

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
