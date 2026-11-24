-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmReuseBlockZero
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaCopyOrder
import Lemmas.Tcgen05.MmaObservedReads
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # The earlier query TMA write precedes the shared overwrite -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy PTX.Flow

/-- An actual Q TMA write precedes a dequantizer overwrite of its byte through the
intervening shared-source copy. -/
private theorem observed_source_before_overwrite {P : Params} {L : Launch} {mem0 : Mem0}
    {X : Execution} {read wait write : EvId} {index : Nat} {chunk : Fin 16} {byte : Loc}
    {q : Wg1Mma.D} {f : Event} {u : TState}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hindex : index < 4096) (hpo : po X wait write)
    (hcopyEv : X.get read = some f)
    (hcopyState : Frame.stateAt (Machine.code P L) X read.1 read.2 = some (some (.mma q)))
    (hcopySite : q.site = .qCopy chunk)
    (hcopyFire : (Machine.machine P L read.1).Fired (some (.mma q)) f (some u))
    (hObserve : QueryTileReuseObserved L X read wait write index byte) :
    ∃ (issuer t x y b : Nat) (value : Byte),
      X.MemWrites (.async (issuer, t) (.write (.load x y b))) {loc := byte, size := 1} [value] ∧
      ByteCausality L X byte (.async (issuer, t) (.write (.load x y b))) (.thread write) := by
  obtain ⟨⟨spec, hcp⟩, hRead, ⟨out, bytes, hStore, hStoreCover, _⟩, hFinish, _⟩ := hObserve
  let row : Fin 128 := ⟨index / 32, by omega⟩
  let feature : Fin 16 := ⟨index / 2 % 16, Nat.mod_lt _ (by decide)⟩
  let b : Fin 2 := ⟨index % 2, Nat.mod_lt _ (by decide)⟩
  have hSplit : 2 * (row.val * 16 + feature.val) + b.val = index := by
    dsimp only [row, feature, b]
    omega
  obtain ⟨_, x, y, t, _, l, value, _, _, _, hWrite, hFoot, _, hPrior, _, _⟩ :=
    QueryTmaCopyOrder.actual_query_tma_write_before_copy hpre hX
      (fun _ hg => Machine.code_sound hpre hg)
      hcopyEv hcopyState hcopySite hcopyFire row feature b
  rw [hSplit] at hPrior hFoot
  have hLoc : l = byte := hcp.footprint_loc_eq hFoot hRead
  subst l
  have hCover : ({loc := byte, size := 1} : Acc).Covers byte :=
    Acc.covers_at (k := 0) (show 0 < 1 by decide)
  exact ⟨read.1, t, x.val, y.val, b.val, value, hWrite,
    hPrior.before_copy_overwrite hX (copy_footprint_shared ⟨spec, hcp⟩ hRead)
      hWrite hCover hcp hRead hFinish hpo hStore hStoreCover⟩

/-- Every dequantization write that overlaps the Q tile follows its actual TMA byte source. -/
theorem query_tma_before_store_byte {P : Params} {L : Launch} {mem0 : Mem0}
    {X : Execution} {g j : Nat} {d : Wg2.D} {r : Fin 4} {s : Fin 8}
    {a : Acc} {bs : List Byte} {byte : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)))
    (hsite : d.site = .store r s) (hw : X.Writes (g, j) a bs) (hcover : a.Covers byte)
    (hlo : L.sharedBase ≤ byte.addr) (hhi : byte.addr < L.sharedBase + 65536) :
    ∃ (issuer t x y b : Nat) (value : Byte),
      X.MemWrites (.async (issuer, t) (.write (.load x y b))) {loc := byte, size := 1} [value] ∧
      ByteCausality L X byte (.async (issuer, t) (.write (.load x y b))) (.thread (g, j)) := by
  obtain ⟨_, _, _, _, hindex, hpo, ⟨q, f, v, hEv, hState, hSite, hFire⟩, hObserve⟩ :=
    query_copy_before_store_byte hpre hX hs hd hsite hw hcover hlo hhi
  exact observed_source_before_overwrite hpre hX hindex hpo hEv hState hSite hFire hObserve

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
