-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal
public import Kernels.TmlFa4Fwd.Proof.EpilogueOutputWrites
public import Lemmas.Protocol.StagingHandoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof Epilogue

/-- A vector element writes one output element before the TMA transfer. -/
def outputElementAccess (l : Launch) (g : Nat) (stage : Fin 2) (subbox : Fin 4)
    (x y : Nat) : Acc :=
  { loc := (outputChunkLoc l g stage subbox y (x / 4)).at (4 * (x % 4))
    size := 4, elem := x % 4 }

/-- A shared source byte of the writeback issue is byte `k` of the correction store element
for the same row and column in the same CTA. -/
theorem writebackSourceAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {issuer writer batch head tile x y k : Nat} (hCta : writer / l.block = issuer / l.block)
    (stage : Fin 2) (subbox : Fin 4) (hx : x < 32) (hy : y < 128) (hk : k < 4) :
    TensorStore.readLoc (writebackStoreSpec p l issuer batch head tile stage subbox) x y k =
      some ((outputElementAccess l writer stage subbox x y).loc.at k) := by
  have hw : TensorTile.count p.oMap.box 0 = 32 := by simp [TensorTile.count, TensorTile.step,
    Params.oMap]
  have hr : TensorTile.rows p.oMap.box = 128 := by
    simp [TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step, Params.oMap]
  have hX : x < TensorTile.count p.oMap.box 0 := hw.symm ▸ hx
  have hY : y < TensorTile.rows p.oMap.box := hr.symm ▸ hy
  have hK : k < p.oMap.format.bytes := hk
  let slot : TensorTransfer.Slot p.oMap := ⟨⟨x, hX⟩, ⟨y, hY⟩, ⟨k, hK⟩⟩
  have hSlot : TensorTransfer.slotAt p.oMap x y k = some slot := by
    unfold TensorTransfer.slotAt
    rw [dite_eq_left hX, dite_eq_left hY, dite_eq_left hK]
  unfold TensorStore.readLoc
  change (TensorTransfer.slotAt p.oMap x y k).map
    (writebackStoreSpec p l issuer batch head tile stage subbox).sharedLoc = _
  rw [hSlot]
  change some ((writebackStoreSpec p l issuer batch head tile stage subbox).toTensorBox.sharedLoc
    slot) = _
  rw [writebackSlot_correctionChunk hp hCta]
  have hScale : (4 * x + k) % 16 = 4 * (x % 4) + k := by omega
  simp only [slot, hScale, outputElementAccess, Loc.at, Nat.add_assoc]

/-- The actual ready arrival publishes earlier correction writes when warp 13's acquire wait
observes that arrival. The two threads and the staged byte stay in the same CTA. -/
theorem correctionPublication {l : Launch} {X : Execution} {i : EvId}
    {writer pos fence ready wait : Nat} (stage : Fin 2)
    (hg : writer < l.threads) (hi : i.1 < l.threads)
    (hCta : writer / l.block = i.1 / l.block)
    (hIssue : i.2 < (X.tr i.1).length) (hWait : wait < i.2)
    (hBefore : pos < fence) (hAfter : fence ≤ ready)
    (hFence : X.get (writer, fence) =
      some ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩)
    (hReady : X.get (writer, ready) = some
      ⟨outputFencePc stage + 2, .arrive (readyLoc l writer stage) 0 1 true .cta⟩)
    (hObs : AsyncCopy.WaitObserves X (.thread (writer, ready)) (i.1, wait)
      (readyLoc l i.1 stage) true .cta) :
    Staging.Publish l X (writer, pos) (writer, fence) (writer, ready) (i.1, wait) i
      (readyLoc l writer stage) := by
  have hLength : fence < (X.tr writer).length := (List.getElem?_eq_some_iff.mp hFence).1
  have hReadyLoc : readyLoc l writer stage = readyLoc l i.1 stage := by simp [readyLoc, hCta]
  have hScope : ScopesMeet l .cta writer .cta i.1 :=
    ⟨⟨hg, hi, hCta⟩, ⟨hi, hg, hCta.symm⟩⟩
  have hOrder : po X (writer, pos) (writer, fence) :=
    ⟨rfl, hBefore, hLength, by simp [SameAccess, hFence, Event.acc]⟩
  refine ⟨⟨_, hFence⟩, hg, .single (.inl hOrder), ?_, ⟨rfl, hAfter⟩,
    ⟨rfl, hWait, hIssue⟩, ⟨hg, hi, congrArg l.clusterOfCta hCta⟩⟩
  exact ⟨.cta, ⟨0, 1, _, hReady⟩, .cta, hReadyLoc.symm ▸ hObs, hScope⟩

/-- The ready publication orders the correction write before the concrete TMA source read. -/
theorem writebackOrderFromReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {i : EvId} {writer pos fence ready wait batch head tile x k : Nat}
    (stage : Fin 2) (subbox : Fin 4)
    (hCta : writer / l.block = i.1 / l.block) (hx : x < 32) (hk : k < 4)
    (hi : X.TensorStoreIssue i p.oMapAddress
      (writebackStoreSpec p l i.1 batch head tile stage subbox))
    (hPublish : Staging.Publish l X (writer, pos) (writer, fence) (writer, ready) (i.1, wait)
      i (readyLoc l writer stage)) :
    let src := (outputElementAccess l writer stage subbox x (rowOf l writer)).loc.at k
    modelCausality l X src (.thread (writer, pos))
      (.async i (.read (.store x (rowOf l writer) k))) := by
  intro src
  have hy : rowOf l writer < 128 := Nat.mod_lt _ (by decide)
  have hRead := writebackSourceAddress hp (batch := batch) (head := head) (tile := tile)
    hCta stage subbox hx hy hk
  let a : Acc := { loc := src, size := 1 }
  have hCover : a.Covers src := ⟨rfl, rfl, Nat.le_refl _, Nat.lt_add_one _⟩
  have hIntent : X.Intent (.async i (.read (.store x (rowOf l writer) k))) a false :=
    ⟨rfl, _, _, hi, hRead, rfl⟩
  exact hPublish.modelCausality rfl rfl ⟨a, false, hIntent, hCover⟩

end PTX.Kernels.TmlFa4Fwd.Correction
