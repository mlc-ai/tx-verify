-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmReuseAudit

@[expose] public section

/-! # Query-copy completion orders shared source reuse -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy

/-- An actual copy source footprint is always in shared memory. -/
theorem copy_footprint_shared {X : Execution} {read : EvId} {index : Nat} {byte : Loc}
    (hcopy : ∃ sp, X.CpIssue read sp) (hread : X.MmaFootprint read false index byte) :
    byte.space = .shared := by
  rcases hread with ⟨d, s, accum, mask, hmma, _⟩ | ⟨sp, k, cta, hi, _, _, _, hloc⟩
  · obtain ⟨sp, tag, hcp⟩ := hcopy
    obtain ⟨pc, hmma⟩ := hmma
    rw [hcp] at hmma
    cases hmma
  · unfold TcCopy.byteLoc at hloc
    split at hloc
    · obtain ⟨addr, _, hbyte⟩ := Option.map_eq_some_iff.mp hloc
      cases hbyte
      rfl
    · cases hloc

variable {L : Launch} {X : Execution} {read wait write : EvId} {index : Nat} {byte : Loc}

/-- An observed tensor-memory copy read precedes a later thread write on each shared byte
covered by both operations. -/
theorem copy_read_before_write {a : Acc} {bs : List Byte} (hcopy : ∃ sp, X.CpIssue read sp)
    (hread : X.MmaFootprint read false index byte) (hwrite : X.Writes write a bs)
    (hcovered : a.Covers byte) (hfinish : AsyncFinished L X read (.mmaRead false index) wait)
    (hbefore : baseCausality L X wait write) :
    QueryTileReuseOrdered L X read write index byte := by
  let aRead : Acc := { loc := byte, size := 1 }
  have hcover : AsyncCovers X read (.mmaRead false index) byte :=
    ⟨aRead, false, ⟨rfl, rfl, hread⟩, by simp [aRead, Acc.Covers, Loc.InRange]⟩
  exact (query_reuse_order_iff_completion L X read write index byte).mpr
    ⟨hcover, wait, hfinish,
      .inr ⟨copy_footprint_shared hcopy hread, .inl ⟨rfl, hcopy⟩,
        hbefore, a, bs, hwrite, hcovered⟩⟩

/-- The query acquire's completion observation orders the read before its overlapping tile write. -/
theorem QueryTileReuseObserved.ordered (h : QueryTileReuseObserved L X read wait write index byte) :
    QueryTileReuseOrdered L X read write index byte := by
  obtain ⟨hcopy, hread, ⟨a, bs, hw, hc, _⟩, hfinish, hbefore⟩ := h
  exact copy_read_before_write hcopy hread hw hc hfinish hbefore

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
