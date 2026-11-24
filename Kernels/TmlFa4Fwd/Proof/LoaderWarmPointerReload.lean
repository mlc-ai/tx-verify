-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import Kernels.TmlFa4Fwd.Flow.Code.Part015

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof Prologue Epilogue

noncomputable section

private def warmKFirstReload : SavedPointerReload := ⟨1003, 7293, 0, 1998, 1999⟩

/-- The first warm K reload recovers both words from an earlier live save of its cell. -/
theorem warmKFirstReloadObserved {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g write index batch head row trips warp tid bound : Nat} (hb : batch < p.batch)
    (hh : head < p.kvHeads) (hOrder : write < index) (hBound : 1003 ≤ bound)
    {s : TState} {ending : Option TState}
    (hs : At s 1003 (warmCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index bound ending)
    (hSaved : X.Writes (g, write) (pointerSaveAccess l g 0 0)
      (b64 (primingKRowPointer p batch head row)).toBytes)
    (hLast : ∀ byte < 8, ∀ j < index, ∀ a, X.Access (g, j) a true →
      a.Covers ((pointerSaveAccess l g 0 0).loc.at byte) → j ≤ write) :
    let ptr := primingKRowPointer p batch head row
    ∃ u, At u 1004 ([(1998, b32 (ptr % 2 ^ 32)), (1999, b32 (ptr / 2 ^ 32))] ++
        warmCacheFrame p l batch head trips warp tid) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 2)) ending ∧
      X.get (g, index) = some ⟨1003,
        .rd (pointerSlotAccess l g 0 0 0) (pointerReadBytes ptr 0)⟩ ∧
      X.get (g, index + 1) = some ⟨1003,
        .rd (pointerSlotAccess l g 0 0 1) (pointerReadBytes ptr 1)⟩ := by
  let F := warmCacheFrame p l batch head trips warp tid
  let site := warmKFirstReload
  have hCode : kernel.code[site.pc]? = some ⟨none, .mem site.mem⟩ := Flow.code_1003
  have hAddr : l.localBase + 32 + site.offset < 2 ^ 64 := by
    have := hp.localMemory.2.1
    change l.localBase + 32 + 0 < 2 ^ 64
    omega
  have hAlign : (l.localBase + 32 + site.offset) % 8 = 0 := by
    have := hp.localMemory.1
    change (l.localBase + 32 + 0) % 8 = 0
    omega
  have hInput : At s site.pc ((site.baseReg, b64 (l.localBase + 32)) :: F) :=
    hs.mono ⟨holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2⟩
  have hFresh : ∀ pair ∈ F, pair.1 ≠ site.lowReg ∧ pair.1 ≠ site.highReg := by
    intro pair hm
    have hAudit : (F.map Prod.fst).all (fun r => decide (r ≠ 1998 ∧ r ≠ 1999)) = true := by
      rfl
    exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (List.mem_map_of_mem hm))
  have hPtr : primingKRowPointer p batch head row < 2 ^ 64 := by
    obtain ⟨hEq, hFit, _⟩ := sourceScratchPayload_live hp 0
      (primingScratchPageBound hp (row := row) hb) (Nat.mod_lt row (by decide : 0 < 16)) hh
    have hEqual : _ = primingKRowPointer p batch head row := hEq
    rwa [hEqual] at hFit
  obtain ⟨u, hU, hf, hRun, hReadLow, hReadHigh⟩ := site.observedInPrefix hX (by decide)
    hCode hAddr hAlign (by decide) hPtr hOrder hInput hFresh hBound hr hDemand hSaved hLast
  exact ⟨u, hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, hf⟩, hRun, hReadLow, hReadHigh⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
