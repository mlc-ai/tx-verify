-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePageHistory
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchSave

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- A warm V save consumes the real page and row words of the selected scratch entry. -/
theorem warmValuePointerSave {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos index batch head trips warp tid row : Nat} (hb : batch < p.batch)
    (hh : head < p.kvHeads) (slot : Fin 2) (more : Bool)
    (hMeta : WarmPageWords p l X g pos batch row slot)
    (hBefore : pos + primingScratchReads p batch row + 2 ≤ index)
    {s : TState} {ending : Option TState}
    (hs : At s 1212 ([(9538, b64 slot.val), (10, .pred more)] ++
      warmCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index 1223 ending)
    (hLast : ∀ (target : Bool), ∀ k < 4, ∀ j < index, ∀ dst, X.Access (g, j) dst true →
      dst.Covers ((pageRefreshAccess l g 0 target slot).loc.at k) →
      j ≤ pos + primingScratchReads p batch row + (if target then 1 else 0)) :
    let ptr := primingVRowPointer p batch head row
    X.get (g, index) = some ⟨1214,
      .rd (pageRefreshAccess l g 0 false slot)
        ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (g, index + 1) = some ⟨1216,
      .rd (pageRefreshAccess l g 0 true slot) ((b32 (row % 16)).toBytes.map some)⟩ ∧
    X.get (g, index + 2) =
      some ⟨1223, .wr (pointerSaveAccess l g 1 slot) (b64 ptr).toBytes⟩ ∧
    ∃ u, At u 1224 ((10, .pred more) :: warmCacheFrame p l batch head trips warp tid) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 3)) ending := by
  let page := primingScratchPage p batch row
  let ps := p.vLayout.pageStride
  let rs := p.vLayout.rowStride
  let base := p.vLayout.base + 2 * (head * p.vLayout.headStride)
  let pw := pos + primingScratchReads p batch row
  let rw := pw + 1
  let F := (10, .pred more) :: warmCacheFrame p l batch head trips warp tid
  have hPageBound : page < p.pages := primingScratchPageBound hp hb
  have hPageSigned : page < 2 ^ 31 := by
    dsimp [page, primingScratchPage]
    split
    · exact ((hp.pageTable batch hb).2 (row / 16) (by omega)).2
    · decide
  have hRow := Nat.mod_lt row (show 0 < 16 by decide)
  have hPS : ps < 2 ^ 64 := (hp.objectBytes 2 40 8 ps (by simp [ps, Params.objectWords])).1
  have hRS : rs < 2 ^ 64 := (hp.objectBytes 2 24 8 rs (by simp [rs, Params.objectWords])).1
  obtain ⟨hPointer, hFit, _⟩ := sourceScratchPayload_live hp 1 hPageBound hRow hh
  change sourceScratchPayload page (row % 16) ps rs base = primingVRowPointer p batch head row
    at hPointer
  have hAt : At s 1212 (recurringScratchSaveInput l 1 slot ps rs base ++ F) := by
    apply hs.mono
    apply (holds_append ..).mpr
    refine ⟨?_, hs.2.2.2.2.2⟩
    simp only [recurringScratchSaveInput, recurringScratchCarry, recurringSaveInputs,
      pointerReloadBase, pointerReloadAddress, List.cons_append, List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first | trivial | exact holds_lookup hs.2.2.2.2 rfl
  have hExtra : RecurringSaveFrame 1 F := by
    have hFresh : (F.map Prod.fst).all (fun r => decide (r ≠ 7710 ∧ r ≠ 7712)) = true := rfl
    have hf (pair : Nat × Value) (hm : pair ∈ F) : pair.1 ≠ 7710 ∧ pair.1 ≠ 7712 :=
      of_decide_eq_true (List.all_eq_true.mp hFresh _ (List.mem_map_of_mem hm))
    exact ⟨by kernel_rfl, fun pair hm => (hf pair hm).1,
      by kernel_rfl, fun pair hm => (hf pair hm).2, by kernel_rfl⟩
  have hLastOr (target : Bool) (k : Nat) (hk : k < 4) (j : Nat) (dst : Acc)
      (ha : X.Access (g, j) dst true)
      (hc : dst.Covers ((pageRefreshAccess l g 0 target slot).loc.at k)) :
      j ≤ pw + (if target then 1 else 0) ∨ index ≤ j := by
    by_cases hj : j < index
    · exact .inl (hLast target k hk j hj dst ha hc)
    · exact .inr (Nat.le_of_not_gt hj)
  obtain ⟨hReadPage, hReadRow, hWrite, hTail⟩ :=
    recurringScratchSaveObservedInPrefixWithFrame hp hX 1 slot (pw := pw) (rw := rw)
      (g := g) (page := page) (row := row % 16) (ps := ps) (rs := rs) (base := base)
      (by dsimp only [pw]; omega) (by dsimp only [rw, pw]; omega) hPageSigned
      (by omega : row % 16 < 2 ^ 31) hPS hRS hFit hExtra hAt hr hDemand hMeta.page hMeta.rowWord
      (by simpa [pw, pageRefreshAccess, recurringPageStoreSite,
          scratchReloadAccess, recurringScratchWord] using hLastOr false)
      (by simpa [rw, pw, pageRefreshAccess, recurringPageStoreSite,
          scratchReloadAccess, recurringScratchWord] using hLastOr true)
  change X.get (g, index + 2) =
    some ⟨1223, .wr (pointerSaveAccess l g 1 slot)
      (b64 (sourceScratchPayload page (row % 16) ps rs base)).toBytes⟩ at hWrite
  rw [hPointer] at hWrite
  exact ⟨hReadPage, hReadRow, hWrite, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
