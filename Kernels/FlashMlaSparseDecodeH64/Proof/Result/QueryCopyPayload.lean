-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQueryValues
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.QueryTmaPayload
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopyReuse
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryWriters
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaCopyOrder
import Lemmas.Tcgen05.MmaObservedReads
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingQuerySharedWrites

@[expose] public section

/-! # Each Tensor Memory query copy observes the actual Q payload -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy MmaDataTrace Wg1Mma Protocol.GemmRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem query_write_window {g i address : Nat} {a : Acc} {data : List Byte}
    {tile : Fin 8} {x y b : Nat}
    (hi : X.TensorIssue (g, i) address (queryTmaSpec P L g tile))
    (hw : X.MemWrites (.async (g, i) (.write (.load x y b))) a data) :
    a.loc.space = .shared ∧ a.loc.cta = ctaOf L g ∧ TensorSharedBounds.QueryWindow L a.loc := by
  obtain ⟨_, _, _, _, hActual, hLoc, _, _, _⟩ := hw
  have hSpec := (Kind.tensorIssue.inj
    (congrArg Event.kind (Option.some.inj (hActual.choose_spec.symm.trans hi.choose_spec)))).2
  rw [hSpec] at hLoc
  exact TensorSharedBounds.query_write_loc tile hLoc

/-- The observed bytes of all 32 query-copy elements per pair of rows come from launch Q.
Every dequantization overwrite of a read byte follows that exact copy, and the completed
TMA tile is the unique tensor writer of the byte. -/
theorem query_copy_payload {g i : Nat} {d : Wg1Mma.D}
    {chunk : Fin 16} {e : Event} {u : TState} {ops : MmaOperands}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : d.site = .qCopy chunk)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e (some u))
    (hOps : X.async.mmaOperands (g, i) = some ops) (row : Fin 128) :
    Bf16Operand ops.a row.val
      (fun k => P.q (batchOf L g) (queryOf L g) (row.val % 64)
        (128 * (chunk.val / 4) + 64 * (row.val / 64) + 16 * (chunk.val % 4) + k)) := by
  intro k hk b hb
  let feature : Fin 16 := ⟨k, hk⟩
  let byte : Fin 2 := ⟨b, hb⟩
  let index := 2 * (row.val * 16 + feature.val) + byte.val
  let reader : Ref := .async (g, i) (.mmaRead false index)
  let l : Loc := ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
    (kvLinearByte L 0 (row.val % 64) (qkFeature chunk row feature) byte.val)⟩
  have hg := Frame.lt_of_get hX he
  have hcp : X.CpIssue (g, i) (queryCopySpec L g chunk) := by
    obtain ⟨tag, kind⟩ := e
    have h := GemmReuseEndpoints.query_copy hpre hg hSite hf
    exact ⟨tag, by rw [he]; cases h; rfl⟩
  obtain ⟨observed, hr, hGet⟩ := queryCopy_read hX.tma.2.1 hcp hOps row feature byte
  have hRead : X.MemReads reader {loc := l, size := 1} [observed] := hr
  have hFoot : X.MmaFootprint (g, i) false index l := hRead.choose_spec.1.1
  obtain ⟨tile, x, y, t, _, loc, value, _, _, hIssue, hWriter, hFoot', _, hOrder, hFeat, hHead⟩ :=
    Protocol.QueryTmaCopyOrder.actual_query_tma_write_before_copy hpre hX hs he hd hSite hf
      row feature byte
  have hSame : loc = l := hcp.footprint_loc_eq hFoot' hFoot
  subst loc
  let writer : Ref := .async (g, t) (.write (.load x.val y.val byte.val))
  have hWrite : X.MemWrites writer {loc := l, size := 1} [value] := hWriter
  have hCover : ({loc := l, size := 1} : Acc).Covers l :=
    Acc.covers_at (k := 0) (show 0 < 1 by decide)
  have hZero : 0 < ({loc := l, size := 1} : Acc).size := Nat.zero_lt_succ 0
  have hQ : TensorSharedBounds.QueryWindow L l := (query_write_window hIssue hWriter).2.2
  have hRf : X.rf reader 0 = some writer := by
    have hVisible : ByteCausality L X l writer reader := hOrder
    have hHidden := hX.hidden reader {loc := l, size := 1} [observed] 0 writer
      {loc := l, size := 1} [value] hRead hZero
      hWrite (by simpa only [Loc.at, Nat.add_zero] using hCover)
      (by simpa only [Loc.at, Nat.add_zero] using hVisible)
    cases hSrc : X.rf reader 0 with
    | none => rw [hSrc] at hHidden; exact hHidden.elim
    | some source =>
      have hRf := (hX.rf reader _ _ hRead).2 0 (Nat.zero_lt_succ 0)
      rw [hSrc] at hRf
      obtain ⟨fp, data, hSource, hCover', _⟩ := hRf
      have hCovers : fp.Covers l := by simpa only [Loc.at, Nat.add_zero] using hCover'
      rcases Wg2.raw_read_competing_kinds hX hSource hCovers (show l.space = .shared from rfl) with
        ⟨⟨h, j⟩, rfl, hStore⟩ | ⟨⟨h, j⟩, x', y', b', rfl⟩
      · obtain ⟨hCta, q, r, s, hState, hStoreSite⟩ :=
          MachineTracking.actual_query_tile_writer hpre hX hs hStore hCovers rfl hQ
        have hBefore := actual_query_copy_before_store hpre hX hs hCta hd hSite hcp
          hFoot hState hStoreSite hStore hCovers
        exact (hX.noFuture reader _ _ 0 _ hRead hZero hSrc
          (by change ByteCausality L X l reader (.thread (h, j)); exact hBefore)).elim
      · exact congrArg some (query_writer_unique hpre hX hs hSource hCovers hWriter hCover hQ)
  have hByte := query_tile_write_byte hpre hX hs tile x y byte hIssue hWriter
  have hContent := mmaByte_of_rf hX hRead hWrite hRf
  have hV := List.cons.inj hByte |>.1
  rw [hFeat, hHead] at hV
  change ops.a[index]? = _
  rw [hGet, hContent, hV]
  rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
