-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmDequantRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmReuseOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopyCompletion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCopyHistory
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmReuseGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReuseHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
public import Lemmas.Order.OrderWaits

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # Query-copy completion and the first dequantization write -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy PTX.Flow PTX.MbarRing

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- A real dequantization store overlapping the Q window follows the actual copy read
of the covered byte. -/
theorem query_copy_before_store_byte {X : Execution} {g j : Nat} {d : Wg2.D} {r : Fin 4} {s : Fin 8}
    {a : Acc} {bs : List Byte} {byte : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)))
    (hsite : d.site = .store r s) (hw : X.Writes (g, j) a bs) (hcover : a.Covers byte)
    (hlo : L.sharedBase ≤ byte.addr) (hhi : byte.addr < L.sharedBase + 65536) :
    ∃ (read wait : EvId) (index : Nat) (chunk : Fin 16),
      index < 4096 ∧ po X wait (g, j) ∧
      (∃ q f u, X.get read = some f ∧
        Frame.stateAt (Machine.code P L) X read.1 read.2 = some (some (.mma q)) ∧
        q.site = .qCopy chunk ∧ (Machine.machine P L read.1).Fired (some (.mma q)) f (some u)) ∧
      QueryTileReuseObserved L X read wait (g, j) index byte := by
  obtain ⟨tag, he⟩ := hw
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (hs g hg).produces (hX.thr g hg) |>.fired_at he hd
  cases o with
  | none =>
    obtain ⟨_, _, hf⟩ := hf
    rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    obtain ⟨a', hk, hloc, hsize⟩ := Wg2.fired_store_event hpre hsite hf
    obtain ⟨rfl, -⟩ := Kind.wr.inj hk
    have hByteGeom : byte = ⟨.shared, ctaOf L g, byte.addr⟩ := by
      have hspace := hcover.1
      have hcta := hcover.2.1
      rw [hloc] at hspace hcta
      cases byte
      simp_all
    obtain ⟨wait, hwait, _, hquery⟩ :=
      Wg2ReuseHistory.query_before_store hpre hX (hs g hg) hg hd hsite
    obtain ⟨issuer, commit, _, _, _, _, hcommit, hIssuer, hqsite, hqstate, hobserve⟩ :=
      QueryCopy.actual_observe_query_copy_commit hpre hX
        (fun _ hg => Machine.code_sound hpre hg) hquery
    obtain ⟨chunk, index, hindex, hbyte⟩ :=
      GemmReuseEndpoints.query_covers_window_byte (g := issuer) hpre hlo hhi
    rw [hIssuer, ← hByteGeom] at hbyte
    obtain ⟨copy, f, q, u', hcopyLt, hCopyEv, hCopyState, hCopySite, hCopyFire, hcopy⟩ :=
      QueryCopyHistory.query_copy_site_before_commit chunk hpre hX
        (hs issuer (Frame.lt_of_get hX hcommit)) hcommit hqstate hqsite
    let spec := MmaDataTrace.queryCopySpec L issuer chunk
    have hfoot : X.MmaFootprint (issuer, copy) false index byte := by
      refine .inr ⟨spec, 0, ctaOf L g, hcopy, rfl, ?_, Nat.div_eq_of_lt hindex, ?_⟩
      · simp [spec, MmaDataTrace.queryCopySpec, hIssuer]
      · rw [Nat.mod_eq_of_lt (show index < spec.shape.sourceBytes from hindex)]
        exact hbyte
    have hpo : po X (g, wait) (g, j) :=
      po_of_source_not_access rfl hwait (PTX.len_of_get he) (by rw [hquery]; rfl)
    exact ⟨(issuer, copy), (g, wait), index, chunk, hindex, hpo,
      ⟨q, f, u', hCopyEv, hCopyState, hCopySite, hCopyFire⟩,
      ⟨spec, hcopy⟩, hfoot, ⟨a, bs, ⟨tag, he⟩, hcover, hsize⟩,
      QueryCopy.copy_read_finished (index := index) hX hcommit hcopy hcopyLt hobserve hIssuer,
      .single (.inl hpo)⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
