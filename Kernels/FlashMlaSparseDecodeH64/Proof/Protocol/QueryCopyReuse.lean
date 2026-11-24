-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmReuseSingle
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites

@[expose] public section

/-! # The exact copy read precedes the dequantized overwrite -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX PTX.Flow AsyncCopy

/-- Every actual query-copy read follows the completion protocol before an overlapping
dequantization store in its CTA. The proof follows the supplied copy reference. -/
theorem actual_query_copy_before_store {P : Params} {L : Launch} {mem0 : Mem0}
    {X : Execution} {g i h j index : Nat} {d : Wg1Mma.D} {q : Wg2.D} {chunk : Fin 16}
    {r : Fin 4} {s : Fin 8} {sp : TcCopy.Spec} {a : Acc} {bs : List Byte} {byte : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hcta : ctaOf L g = ctaOf L h)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qCopy chunk) (hcp : X.CpIssue (g, i) sp)
    (hRead : X.MmaFootprint (g, i) false index byte)
    (hd' : Frame.stateAt (Machine.code P L) X h j = some (some (.wg2 q)))
    (hStore : q.site = .store r s) (hw : X.Writes (h, j) a bs) (ha : a.Covers byte) :
    QueryTileReuseOrdered L X (g, i) (h, j) index byte := by
  have hg := Frame.lt_of_get hX hw.choose_spec
  obtain ⟨wait, hwait, _, hquery⟩ :=
    Wg2ReuseHistory.query_before_store hpre hX (hs h hg).machine hg hd' hStore
  obtain ⟨issuer, c, _, _, _, dd, hCommit, hIssuer, hCommitSite, hCommitState, hObs⟩ :=
    QueryCopy.actual_observe_query_copy_commit hpre hX hs hquery
  obtain ⟨_, hLeader⟩ :=
    Wg1MmaLeader.cta_issuer (cta := ctaOf L h) hpre hX (fun t ht => (hs t ht).machine)
  have hEq : issuer = g :=
    (hLeader issuer c dd hIssuer hCommitState (by simp [hCommitSite])).trans
      (hLeader g i d hcta hd (by simp [hsite])).symm
  subst issuer
  obtain ⟨t, _, dt, _, hLt, hEvent, hState, hSite, _, _⟩ :=
    QueryCopyHistory.query_copy_site_before_commit chunk hpre hX
      (hs g (Frame.lt_of_get hX hCommit)).machine hCommit hCommitState hCommitSite
  have hIt : i = t := QueryTmaSites.copy_site_unique hcp.choose_spec hEvent hd hState hsite hSite
  have hFinish := QueryCopy.copy_read_finished (index := index) hX
    hCommit hcp (hIt ▸ hLt) hObs hcta
  have hBefore : baseCausality L X (h, wait) (h, j) :=
    .single (.inl (po_of_source_not_access rfl hwait (PTX.len_of_get hw.choose_spec)
      (by rw [hquery]; rfl)))
  exact copy_read_before_write ⟨sp, hcp⟩ hRead hw ha hFinish hBefore

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
