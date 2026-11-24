-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopyProgressSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQuery
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryWriters
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GlobalFrame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReuseHistory
import Lemmas.TensorStore.StoreWrite

public section

/-! # The query-copy input tiles and absence of competing shared writes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.AsyncCopy MmaDataTrace Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An actual query copy follows a successful query TMA wait that observed all eight tiles. -/
theorem query_copy_tiles_observed
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g i : Nat} {copy : TcCopy.Spec} (hc : X.CpIssue (g, i) copy) (tile : Fin 8) :
    ∃ t o, X.tensor (g, t) = some o ∧ o.spec = queryTmaSpec P L g tile ∧
      X.TensorIssue (g, t) (P.param1Base + Wg1Mma.qMapOff) o.spec ∧ o.effects.notified = true := by
  let sound := fun w hw => (hs w hw).machine
  have hg := Frame.lt_of_get hX hc.choose_spec
  obtain ⟨d, k, hd, hSite, _⟩ := QueryCopy.issue_state hpre hX hs ht hc
  obtain ⟨w, _, q, tag, hw, hq, hWait⟩ :=
    QueryTmaHistory.wait_before_copy hpre hX (sound g hg) hc.choose_spec hd hSite
  obtain ⟨t, _, hi⟩ := QueryTmaHistory.load_before_wait tile hpre hX (sound g hg)
    hWait hw hq
  obtain ⟨r, m, hn, _⟩ := QueryTmaWait.tile_observed hpre hX sound ht hi hWait
  obtain ⟨_, o, addr, hObs, hIssue, _, hNotified⟩ :
      r = .async (g, t) (.notify .load) ∧ NotifyOn X (g, t) .load m := hn
  have hEq := Kind.tensorIssue.inj (congrArg Event.kind
    (Option.some.inj (hIssue.choose_spec.symm.trans hi.choose_spec)))
  exact ⟨t, o, hObs, hEq.2, hEq.1 ▸ hIssue, hNotified⟩

/-- A byte of a captured query tile has its one TMA writer until the CTA's query copies finish.
Every ordinary overlapping dequantization store requires the query-copy acquire. -/
theorem query_copy_tile_unique
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g i t addr x y b : Nat} {copy : TcCopy.Spec} {l : Loc} {a : Acc} {bs : List Byte}
    (hc : X.CpIssue (g, i) copy) (hd : X.async.mmaDone (g, i) = false) (tile : Fin 8)
    (hTile : X.TensorIssue (g, t) addr (queryTmaSpec P L g tile))
    (hSource : X.MemWrites (.async (g, t) (.write (.load x y b))) a bs) (hCover : a.Covers l)
    {writer : Ref} {f : Acc} {data : List Byte} (hw : X.MemWrites writer f data)
    (hf : f.Covers l) : writer = .async (g, t) (.write (.load x y b)) := by
  have hOriginal := hSource
  obtain ⟨o, _, _, _, hSrc, hLoc, _, hOne, _⟩ := hSource
  have hEq := (Kind.tensorIssue.inj (congrArg Event.kind
    (Option.some.inj (hSrc.choose_spec.symm.trans hTile.choose_spec)))).2
  rw [hEq, Acc.loc_of_one hCover hOne] at hLoc
  obtain ⟨hSpace, hCta, hQ⟩ := TensorSharedBounds.query_write_loc tile hLoc
  cases writer with
  | thread w =>
    rcases hw with hWrite | ⟨_, hRmw⟩
    · have hBelow : l.addr < L.sharedBase + 131072 := by have := hQ.2; omega
      obtain ⟨hOwner, ⟨d, r, s, hState, hSite⟩ | ⟨hAbove, _⟩⟩ :=
        RawSharedWrites.tile_writer_role hpre hX hs ht hWrite hf hSpace hBelow
      · have hg := Frame.lt_of_get hX hWrite.choose_spec
        obtain ⟨j, _, tag, hWait⟩ := Wg2ReuseHistory.query_before_store hpre hX
          (hs w.1 hg).machine hg hState hSite
        have hDone := QueryCopy.copy_done_of_wait hpre hX hs ht hc
          (hCta.symm.trans hOwner) (tag := tag) hWait
        rw [hDone] at hd
        cases hd
      · have := hQ.2
        omega
    · exact (GlobalWrites.no_rmw hX hRmw).elim
  | async w p =>
    cases p <;> try contradiction
    case writeLoad u v k =>
      rcases w with ⟨issuer, index⟩
      exact (GemmRing.query_writer_unique hpre hX hs hOriginal hCover hw hf hQ).symm
    case writeStore u v k =>
      obtain ⟨_, _, _, _, hIssue, hWrite, _, hSize, _⟩ := hw
      rw [Acc.loc_of_one hf hSize] at hWrite
      obtain ⟨_, _, _, _, _, _, _, _, hDst⟩ :=
        Result.output_destination hpre hs hX ht hIssue hWrite
      have hGlobal : l.space = .global := by rw [hDst]; rfl
      rw [hSpace] at hGlobal
      cases hGlobal
    case writeCta c =>
      obtain ⟨_, _, hIssue, _, _⟩ := hw
      exact (GlobalWrites.no_clc hX hIssue).elim
    case writeCopy =>
      obtain ⟨_, hIssue, _, _, _⟩ := hw
      exact (GlobalWrites.no_copy hX hIssue).elim
    case writeElem k =>
      obtain ⟨_, hIssue, _, _⟩ := hw
      exact (GlobalWrites.no_copy hX hIssue).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
