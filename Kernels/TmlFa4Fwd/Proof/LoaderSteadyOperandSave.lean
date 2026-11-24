-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadySpillStart
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPageHistory
import Kernels.TmlFa4Fwd.Proof.LoaderSourceLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- The actual K or V row pointer, including the decoded zero-page choice on masked rows. -/
def steadyOperandPointer (p : Params) (value : Bool) (batch head row : Nat) : Nat :=
  ((recurringCache p (steadySpillSite value)).loc
    (primingScratchPage p batch row) head (row % 16) 0).addr

set_option maxRecDepth 100000 in
/-- The observed steady scratch reads and pointer write use that round's two refreshed words. -/
theorem steadyOperandPointerSave {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos index batch head trips warp tid row : Nat} (hb : batch < p.batch)
    (hh : head < p.kvHeads) (value : Bool) (slot : Fin 2) (more : Bool)
    (hMeta : SteadyPageWords p l X g pos batch row slot)
    (hBefore : pos + primingScratchReads p batch row + 2 ≤ index)
    {s : TState} {ending : Option TState}
    (hs : At s (steadySpillFirst value)
      (steadySpillFacts value slot more ++ steadyCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index (pointerSavePc (steadySpillSite value)) ending)
    (hLast : ∀ (target : Bool), ∀ k < 4, ∀ j < index, ∀ dst, X.Access (g, j) dst true →
      dst.Covers ((pageRefreshAccess l g 1 target slot).loc.at k) →
      j ≤ pos + primingScratchReads p batch row + (if target then 1 else 0)) :
    let site := steadySpillSite value
    let ptr := steadyOperandPointer p value batch head row
    X.get (g, index) = some ⟨(recurringScratchWord site false).pc,
      .rd (pageRefreshAccess l g 1 false slot)
        ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (g, index + 1) = some ⟨(recurringScratchWord site true).pc,
      .rd (pageRefreshAccess l g 1 true slot) ((b32 (row % 16)).toBytes.map some)⟩ ∧
    X.get (g, index + 2) =
      some ⟨pointerSavePc site, .wr (pointerSaveAccess l g site slot) (b64 ptr).toBytes⟩ ∧
    ∃ u, At u (pointerSavePc site + 1)
        ((steadySpillPred value, .pred more) :: steadyCacheFrame p l batch head trips warp tid) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 3)) ending := by
  let site := steadySpillSite value
  let page := primingScratchPage p batch row
  let cache := recurringCache p site
  let ps := cache.pageStride
  let rs := cache.rowStride
  let base := cache.base + 2 * (head * cache.headStride)
  let pw := pos + primingScratchReads p batch row
  let rw := pw + 1
  let F := (steadySpillPred value, .pred more) :: steadyCacheFrame p l batch head trips warp tid
  have hPageBound : page < p.pages := primingScratchPageBound hp hb
  have hPageSigned : page < 2 ^ 31 := by
    dsimp [page, primingScratchPage]
    split
    · exact ((hp.pageTable batch hb).2 (row / 16) (by omega)).2
    · decide
  have hRow := Nat.mod_lt row (show 0 < 16 by decide)
  have hPS : ps < 2 ^ 64 := by
    cases value <;> dsimp [ps, cache, site, steadySpillSite, recurringCache]
    · exact (hp.objectBytes 1 40 8 p.kLayout.pageStride (by simp [Params.objectWords])).1
    · exact (hp.objectBytes 2 40 8 p.vLayout.pageStride (by simp [Params.objectWords])).1
  have hRS : rs < 2 ^ 64 := by
    cases value <;> dsimp [rs, cache, site, steadySpillSite, recurringCache]
    · exact (hp.objectBytes 1 24 8 p.kLayout.rowStride (by simp [Params.objectWords])).1
    · exact (hp.objectBytes 2 24 8 p.vLayout.rowStride (by simp [Params.objectWords])).1
  have hPayload : sourceScratchPayload page (row % 16) ps rs base =
      steadyOperandPointer p value batch head row ∧
      sourceScratchPayload page (row % 16) ps rs base < 2 ^ 64 := by
    cases value <;> dsimp [ps, rs, base, cache, site, steadySpillSite, recurringCache,
      steadyOperandPointer]
    · exact (sourceScratchPayload_live hp 0 hPageBound hRow hh).imp_right And.left
    · exact (sourceScratchPayload_live hp 1 hPageBound hRow hh).imp_right And.left
  obtain ⟨hPointer, hFit⟩ := hPayload
  have hAt : At s (steadySpillFirst value)
      (recurringScratchSaveInput l site slot ps rs base ++ F) := by
    apply hs.mono
    apply (holds_append ..).mpr
    refine ⟨?_, hs.2.2.2.2.2⟩
    cases value <;>
      simp only [site, steadySpillSite, recurringCache, cache, ps, rs, base,
        recurringScratchSaveInput,
        recurringScratchCarry, recurringSaveInputs, pointerReloadBase, pointerReloadAddress,
        List.cons_append, List.nil_append, Holds, Bool.false_eq_true, ↓reduceIte]
    all_goals repeat' apply And.intro
    all_goals first | trivial | exact holds_lookup hs.2.2.2.2 rfl
  have hExtra : RecurringSaveFrame site F := by
    have hFresh : (F.map Prod.fst).all (fun r => decide
        (r ≠ (recurringScratchWord site false).destination ∧
         r ≠ (recurringScratchWord site true).destination)) = true := by cases value <;> rfl
    have hf (pair : Nat × Value) (hm : pair ∈ F) := of_decide_eq_true
      (List.all_eq_true.mp hFresh _ (List.mem_map_of_mem hm))
    exact ⟨by cases value <;> kernel_rfl, fun pair hm => (hf pair hm).1,
      by cases value <;> kernel_rfl, fun pair hm => (hf pair hm).2, by cases value <;> kernel_rfl⟩
  have hLastOr (target : Bool) (k : Nat) (hk : k < 4) (j : Nat) (dst : Acc)
      (ha : X.Access (g, j) dst true)
      (hc : dst.Covers ((pageRefreshAccess l g 1 target slot).loc.at k)) :
      j ≤ pw + (if target then 1 else 0) ∨ index ≤ j := by
    by_cases hj : j < index
    · exact .inl (hLast target k hk j hj dst ha hc)
    · exact .inr (Nat.le_of_not_gt hj)
  have hPageEvent : X.get (g, pw) = some ⟨(recurringScratchWord site false).store,
      .wr (scratchReloadAccess l g (recurringScratchWord site false) slot) (b32 page).toBytes⟩ := by
    cases value <;> exact hMeta.page
  have hRowEvent : X.get (g, rw) = some ⟨(recurringScratchWord site true).store,
      .wr (scratchReloadAccess l g (recurringScratchWord site true) slot)
        (b32 (row % 16)).toBytes⟩ := by
    cases value <;> exact hMeta.rowWord
  obtain ⟨hReadPage, hReadRow, hWrite, hTail⟩ :=
    recurringScratchSaveObservedInPrefixWithFrame hp hX site slot (pw := pw) (rw := rw)
      (g := g) (page := page) (row := row % 16) (ps := ps) (rs := rs) (base := base)
      (by dsimp only [pw]; omega) (by dsimp only [rw, pw]; omega) hPageSigned
      (by omega : row % 16 < 2 ^ 31) hPS hRS hFit hExtra hAt hr hDemand hPageEvent hRowEvent
      (by cases value <;> exact hLastOr false)
      (by cases value <;> exact hLastOr true)
  rw [hPointer] at hWrite
  exact ⟨by cases value <;> exact hReadPage, by cases value <;> exact hReadRow, hWrite, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
