-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopyCompletion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryOperandHistory
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCopyHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCellWriters
import Lemmas.Order.OrderWaits

@[expose] public section

/-! # Actual query-copy completion and the QK Tensor Memory A operand -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandSource

open PTX PTX.Flow AsyncCopy MmaDataTrace Wg1Mma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The matching chunk's query copy was issued by the QK lane. Its acquire observes the
copy commit, and the actual fence reaches the QK issue. -/
theorem observed_copy_before_qk {g j : Nat} {d : Wg1Mma.D} {e : Event} {issue : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hsite : d.site = .qkMma issue) :
    ∃ i f q u, X.get (g, i) = some f ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qCopy issue ∧ (Machine.machine P L g).Fired (some (.mma q)) f (some u) ∧
      X.CpIssue (g, i) (queryCopySpec L g issue) ∧
      X.async.mmaDone (g, i) = true ∧ TcMma.DoneBefore L X (g, i) (g, j) := by
  have hg := Frame.lt_of_get hX he
  have hm := fun t ht' => (hs t ht').machine
  obtain ⟨w, f, tag, ft, hwf, hfj, hw, hf⟩ :=
    QueryOperandHistory.wait_and_fence_before_qk hpre hX (hm g hg) he hd hsite
  obtain ⟨issuer, commit, ct, sp, rank, cd, hc, hcta, hcSite, hcState, hObserve⟩ :=
    QueryCopy.actual_observe_query_copy_commit hpre hX hs hw
  obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := ctaOf L g) hpre hX hm
  have hG := hLeader g j d rfl hd (by rw [hsite]; simp)
  have hIssuer := hLeader issuer commit cd hcta hcState (by rw [hcSite]; simp)
  have hsame := hIssuer.trans hG.symm
  rw [hsame] at hc hcState hObserve
  obtain ⟨i, v, q, u, hic, hget, hst, hq, hiFire, hcp⟩ :=
    QueryCopyHistory.query_copy_site_before_commit issue hpre hX (hm g hg) hc hcState hcSite
  have hFinish := QueryCopy.copy_read_finished (index := 0) hX hc hcp hic hObserve rfl
  rcases hFinish with ⟨k, hno, _⟩ | ⟨scope, hobs, hscope⟩
  · cases k with
    | bulk mode => cases mode <;> cases hno
    | cpAsync => cases hno
  have hobserved : AsyncObserved X (g, i) .mmaDone (g, w) true scope := hobs
  have hdone : X.async.mmaDone (g, i) = true := by
    obtain ⟨_, _, hnotify, _⟩ := hobserved
    obtain ⟨commit', _, rank', _, hTracks, _, _, hNotified⟩ := hnotify
    exact (hX.tcCommit commit' rank' hNotified).2 _ hTracks
  have hWaitFence : baseCausality L X (g, w) (g, f) :=
    .single (.inl (po_of_source_not_access rfl hwf (PTX.len_of_get hf) (by rw [hw]; rfl)))
  have hFenceQk : po X (g, f) (g, j) :=
    po_of_source_not_access rfl hfj (PTX.len_of_get he) (by rw [hf]; rfl)
  exact ⟨i, v, q, u, hget, hst, hq, hiFire, hcp, hdone,
    .inr ⟨(g, w), ⟨true, scope, hobserved, hscope⟩, (g, f), hWaitFence, ⟨ft, hf⟩, hFenceQk⟩⟩

/-- The actual copy covers every A cell of its matching QK chunk. -/
theorem copy_writes_qk_a {g i : Nat} {issue : Fin 16}
    (hcopy : X.CpIssue (g, i) (queryCopySpec L g issue)) (row : Fin 128) (k : Fin 16) :
    TcMma.CpCell X (g, i) ⟨ctaOf L g, row.val, qkACol issue + k.val / 2⟩ := by
  let n := 32 * row.val + 2 * k.val
  have hrow := row.isLt
  have hk := k.isLt
  refine ⟨_, ctaOf L g, n, row.val, hcopy, by simp [queryCopySpec], ?_, ?_, ?_⟩
  · change n < 4096
    dsimp [n]
    omega
  · change row.val ∈ [n / 32]
    have hn : n / 32 = row.val := by dsimp [n]; omega
    rw [hn]
    exact List.mem_singleton.mpr rfl
  · simp only [queryCopySpec, TcCopy.cell, TcCpShape.rowBytes, qCopyCol, qkACol, tmemQ]
    dsimp [n]
    congr 1 <;> omega

/-- All A cells of the actual QK chunk read its actual earlier copy, once its allocation
lifetime has been established. No other event can write those cells. -/
theorem read_source_of_query_copy {g j : Nat} {d : Wg1Mma.D} {issue : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, j) tmemP (qkOperands L g d.i issue) (qkAccum issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hsite : d.site = .qkMma issue) :
    ∃ i e q u, X.get (g, i) = some e ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qCopy issue ∧ (Machine.machine P L g).Fired (some (.mma q)) e (some u) ∧
      X.CpIssue (g, i) (queryCopySpec L g issue) ∧ X.async.mmaDone (g, i) = true ∧
      ∀ (row : Fin 128) (k : Fin 16),
        let cell : TcMma.Cell := ⟨ctaOf L g, row.val, qkACol issue + k.val / 2⟩
        TcMma.SourceLive L X (g, i) (g, j) cell → TcMma.ReadSource L X .a (g, i) (g, j) cell := by
  obtain ⟨i, e, q, u, he, hq, hqsite, hfire, hcopy, hDone, hBefore⟩ :=
    observed_copy_before_qk hpre hX hs hi.choose_spec hd hsite
  have hne : (g, i) ≠ (g, j) := by
    intro h
    obtain ⟨_, he'⟩ := hcopy
    rw [h] at he'
    cases congrArg Event.kind (Option.some.inj (he'.symm.trans hi.choose_spec))
  refine ⟨i, e, q, u, he, hq, hqsite, hfire, hcopy, hDone, ?_⟩
  intro row k
  dsimp only
  intro hLive
  refine ⟨hne, .inr (.inr (.inl (copy_writes_qk_a hcopy row k))), .inl (.inl hBefore), ?_, hLive⟩
  intro other hw
  exact .inl (QueryCellWriters.unique_writer hpre hX hs he hq hqsite row k hw)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandSource
