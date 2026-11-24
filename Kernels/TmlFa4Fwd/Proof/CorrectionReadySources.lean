-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeSurface
public import Kernels.TmlFa4Fwd.Proof.OutputReady

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue AsyncCopy

noncomputable section

/-- The writes and ready arrival of one lane's actual normalized output row. -/
structure NormalizedOutput (l : Launch) (X : Execution) (g start : Nat) (stage : Fin 2)
    (old : Fin 16 → Nat → ℝ) (reciprocal : ℝ) : Prop where
  chunks : ∀ chunk : Fin 16, NormalizedChunkEffects l X g (start + 10 * chunk.val)
    stage chunk (old chunk) reciprocal
  fence : X.get (g, start + 160) = some
    ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩
  ready : X.get (g, start + 162) = some
    ⟨outputFencePc stage + 2, .arrive (readyLoc l g stage) 0 1 true .cta⟩

/-- For any column of a subbox, find its actual correction write before the ready fence. -/
theorem NormalizedOutput.element {l : Launch} {X : Execution} {g start : Nat} {stage : Fin 2}
    {old : Fin 16 → Nat → ℝ} {reciprocal : ℝ}
    (h : NormalizedOutput l X g start stage old reciprocal)
    (subbox : Fin 4) {column : Nat} (hx : column < 32) :
    let chunk : Fin 16 := ⟨4 * subbox.val + column / 8, by have := subbox.isLt; omega⟩
    let pos := start + 10 * chunk.val + 2 + 4 * ((column / 4) % 2) + column % 4
    pos < start + 160 ∧
    X.get (g, pos) = some ⟨outputStorePc stage subbox ⟨column / 4, by omega⟩,
      .wr (outputElementAccess l g stage subbox column (rowOf l g))
        (fl (old chunk (column % 8) * reciprocal)).toBytes⟩ := by
  dsimp only
  let chunk : Fin 16 := ⟨4 * subbox.val + column / 8, by have := subbox.isLt; omega⟩
  let half : Fin 2 := ⟨(column / 4) % 2, by omega⟩
  let j : Fin 4 := ⟨column % 4, by omega⟩
  have hSub : finalizeSubset chunk = subbox := Fin.ext (by dsimp [finalizeSubset, chunk]; omega)
  have hVector : finalizeVector chunk half = ⟨column / 4, by omega⟩ := Fin.ext (by
    dsimp [finalizeVector, chunk, half]
    omega)
  have hColumn : 4 * half.val + j.val = column % 8 := by dsimp [half, j]; omega
  have hWrite := (h.chunks chunk).writes half j
  rw [hSub, hVector, hColumn] at hWrite
  refine ⟨?_, hWrite⟩
  have hc := chunk.isLt
  change start + 10 * chunk.val + 2 + 4 * ((column / 4) % 2) + column % 4 < start + 160
  omega

/-- The observed lane write is published through the matching ready phase of warp 13. -/
theorem normalizedOutputPublishes {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait issue : Nat} {stage : Fin 2} {start : Nat → Nat} {lane : Nat} (hl : lane < 128)
    {old : Fin 16 → Nat → ℝ} {reciprocal : ℝ}
    (hLane : NormalizedOutput l X ((g / l.block) * l.block + 256 + lane)
      (start lane) stage old reciprocal)
    (hSrc : OutputReadySources l X g stage (fun lane => start lane + 162))
    (hWait : X.get (g, wait) =
      some ⟨pollPc stage, .wait (readyLoc l g stage) 0 true true .cta⟩)
    {address : Nat} {spec : TensorStore.Spec}
    (hIssue : X.TensorStoreIssue (g, issue) address spec) (hOrder : wait < issue)
    (subbox : Fin 4) {column : Nat} (hx : column < 32) :
    let writer := (g / l.block) * l.block + 256 + lane
    let chunk : Fin 16 := ⟨4 * subbox.val + column / 8, by have := subbox.isLt; omega⟩
    let written := start lane + 10 * chunk.val + 2 + 4 * ((column / 4) % 2) + column % 4
    X.get (writer, written) = some ⟨outputStorePc stage subbox ⟨column / 4, by omega⟩,
      .wr (outputElementAccess l writer stage subbox column (rowOf l writer))
        (fl (old chunk (column % 8) * reciprocal)).toBytes⟩ ∧
    Staging.Publish l X (writer, written) (writer, start lane + 160) (writer, start lane + 162)
      (g, wait) (g, issue) (readyLoc l writer stage) := by
  dsimp only
  obtain ⟨hBefore, hWritten⟩ := hLane.element subbox hx
  exact ⟨hWritten, readyPublishesOutput hp hX hSrc hl hWait hIssue hOrder
    hBefore (by omega) hLane.fence hLane.ready⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
