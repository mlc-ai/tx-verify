-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvAccumulatorSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RescaleRelease
import Lemmas.Tcgen05.TcDataCell

@[expose] public section

/-! # The rescale producer of a PV accumulator cell -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvRescalePublication

open PTX PTX.Flow PvAccumulatorSource
open Wg1Mma (tmemO)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The softmax lane responsible for a PV output cell. -/
def writerLane (head : Fin 64) (col : Fin 256) : Fin 128 :=
  ⟨head.val + 64 * (col.val / 128), by have := head.isLt; have := col.isLt; omega⟩

/-- The tile and register containing that cell in its producer's storage order. -/
def writerTile (half : Fin 2) (col : Fin 256) : Fin 4 :=
  ⟨2 * half.val + col.val % 128 / 64, by
    have := half.isLt
    have := Nat.mod_lt col.val (by decide : 0 < 128)
    omega⟩

/-- The softmax producer belongs to the same CTA and logical head as its PV result. -/
theorem writer_geometry (hpre : Pre P L mem0) (cta : Nat) (head : Fin 64) (col : Fin 256) :
    let h := GemmRing.softmax L cta (writerLane head col)
    ctaOf L h = cta ∧ Wg0.head L h = head.val := by
  have hHead := head.isLt
  have hLane := (writerLane head col).isLt
  simp only [ctaOf, Wg0.head, tidOf_eq hpre, GemmRing.softmax, hpre.block, writerLane] at *
  omega

/-- The first PV issue observes the rescale producer's same-block publication.
If the producer selected rescaling, the exact accumulator cell has a same-block store. -/
theorem writer_publication {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (head : Fin 64) (half : Fin 2) (col : Fin 256) :
    let cta := ctaOf L g
    let h := GemmRing.softmax L cta (writerLane head col)
    let cell : TcMma.Cell :=
      ⟨cta, (writerLane head col).val, tmemO + 128 * half.val + col.val % 128⟩
    ∃ a out ev, X.get (h, a) = some ev ∧
      Frame.stateAt (Machine.code P L) X h a = some (some (.wg0 out)) ∧
      out.site = .soReady ∧ out.block = d.i ∧ baseCausality L X (h, a) (g, i) ∧
      (Wg0.wantsRescale out = true →
        ∃ j < a, ∃ q, q.block = d.i ∧
          RescaleStore P L X h j cell q (writerTile half col)) := by
  dsimp only
  let cta := ctaOf L g
  let lane := writerLane head col
  let h := GemmRing.softmax L cta lane
  let tile := writerTile half col
  let reg := col.val % 64
  let cell := TcMma.Cell.mk cta lane.val (tmemO + 128 * half.val + col.val % 128)
  obtain ⟨a, out, tag, ha, hout, hReady, hBlock, hOrder⟩ :=
    PvProbabilitySource.publication_before_pv hpre hX (fun t ht' => (hs t ht').machine)
      ht he hd hsite lane
  refine ⟨a, out, _, ha, hout, hReady, hBlock, hOrder, ?_⟩
  intro hRescale
  obtain ⟨j, hja, q, hq, hQBlock, hQSite, hStore⟩ :=
    Wg0RescaleRelease.tensor_store_before_publication tile hpre hX hs ha hout hReady hRescale
  have htLane : h % 384 = lane.val := by
    have hl := lane.isLt
    simp only [h, GemmRing.softmax, hpre.block]
    omega
  have hCta : h / 384 = cta := by
    have hl := lane.isLt
    simp only [h, GemmRing.softmax, hpre.block]
    omega
  have hAddr : 64 * tile.val < 2 ^ 16 := by have := tile.isLt; omega
  have hWarp : h % 384 / 32 < 4 := by rw [htLane]; have := lane.isLt; omega
  have hCell : cell = tcDataCell L h .s32x32b (64 * tile.val) reg := by
    rw [tcDataCell_s32x32b]
    simp only [tcDataCell32, laneBase, PTX.laneOf, hpre.block, hCta, htLane,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt (htLane ▸ hWarp)]
    simp only [cell, tile, writerTile, reg, tmemO, Nat.zero_add, TcMma.Cell.mk.injEq,
      true_and]
    omega
  refine ⟨j, hja, q, hQBlock.trans hBlock, hq, hQSite, hStore, ?_⟩
  exact ⟨_, _, _, reg, hStore, by simp [Wg0.rescaleStoreValues, reg, Nat.mod_lt], hCell⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvRescalePublication
