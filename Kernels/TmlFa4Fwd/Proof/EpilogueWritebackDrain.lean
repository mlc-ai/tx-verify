-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Proof.EpilogueWriteback

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

noncomputable section

/-- A completed output warp starting at its first ready wait issues both groups and then
enters the drain scan. The first drain shuffle uses the same cumulative query lengths. -/
theorem writebackDrainFirst {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (g j : Nat) {batch head tile : Nat} {t : TState}
    (hb : batch < p.batch) (hh : head < p.heads) (htile : 256 * tile < p.qLength batch)
    (ht : At t 2958 (writebackEntry p l batch head tile))
    (hGate : t.regs 307 = some (.pred (p.batch < laneOf l g)))
    (hIndex : t.regs 1201 = some (b32 (laneOf l g)))
    (hBase : t.regs 7506 = some (b64 p.cuQBase))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * laneOf l g)).at k)) :
    ∃ written suffix, (X.tr g).drop j = written ++ suffix ∧
      WritebackTrace p l g batch head tile (some (.ready 0)) written none ∧
      written.filter (fun e => writebackSucceeded e.kind) =
        writebackRemaining p l g batch head tile (some (.ready 0)) ∧
      let start := j + written.length
      let idx := if laneOf l g ≤ p.batch then start + 1 else start
      let word := b32 (drainCuQ p (laneOf l g))
      (laneOf l g ≤ p.batch → X.get (g, start) = some ⟨2989,
        .rd {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} (word.toBytes.map some)⟩) ∧
      ∃ recv ok u, X.get (g, idx) = some ⟨2990, .shfl .down word 1 31 recv ok⟩ ∧
        At u 2991 [(7229, word), (2401, recv)] ∧
        (∀ r, r ∉ writebackWrites ++ [7872, 7873, 7229, 2401] → u.regs r = t.regs r) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop (idx + 1)) none := by
  have hWB {s : TState} (hs : WritebackPc s.pc) :
      out kernel Assumptions.all l g s = out kernel [] l g s :=
    epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
  obtain ⟨written, suffix, last, v, hsplit, hTrace, hv, hFrame, hSuffix⟩ :=
    writebackFromFirstPollOfOutEq hp g hWB hb hh htile ht hRun
  cases last with
  | some _ => exact (Bool.noConfusion hSuffix.2)
  | none =>
    refine ⟨written, suffix, hsplit, hTrace, hTrace.successful rfl, ?_⟩
    have hpv : v.pc = 2986 := hv.1
    have hfv := hv.2.2.2.1
    have hGate' := (hFrame 307 (by decide)).trans hGate
    have hIndex' := (hFrame 1201 (by decide)).trans hIndex
    have hBase' := (hFrame 7506 (by decide)).trans hBase
    have hZero : v.regs 7229 = some (b32 0) := by
      apply holds_mem hv.2.2.2.2
      simp [writebackFacts, writebackEntry]
    have hModel {s : TState} (hlo : 2986 ≤ s.pc) (hhi : s.pc ≤ 2990) :
        out kernel Assumptions.all l g s = out kernel [] l g s :=
      epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
    have hDrop : (X.tr g).drop (j + written.length) = suffix := by
      rw [← List.drop_drop, hsplit, List.drop_append_length]
    cases suffix with
    | nil => cases hSuffix
    | cons e es =>
      cases es with
      | nil =>
        rcases drainFirstEvent hp g v hModel hpv hfv hGate' hIndex' hBase' hZero with
          ⟨_, _, _, hNext⟩ | ⟨_, _, _, _, _, _, _, hNext⟩
        all_goals
          obtain ⟨_, _, hRest⟩ := hNext.continuing_event (by
            rintro ⟨_, _, _, he⟩
            cases he) hSuffix
          cases hRest
      | cons e' rest =>
        obtain ⟨hRead, recv, ok, u, he, hu, hDrainFrame, hRest⟩ :=
          drainFirstTrace hp hX g (j + written.length) v hModel hpv hfv hv.2.1 hv.2.2.1
            hGate' hIndex' hBase' hZero hDrop hSuffix hProtected
        refine ⟨hRead, recv, ok, u, he, hu, ?_, hRest⟩
        intro r hr
        exact (hDrainFrame r (fun h => hr (List.mem_append_right _ h))).trans
          (hFrame r (fun h => hr (List.mem_append_left _ h)))

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
