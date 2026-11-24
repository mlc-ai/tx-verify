-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainRoot
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import all Kernels.TmlFa4Fwd.Proof.Thread.RowDrainRoot
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue Epilogue Correction Softmax

/-- Preserve an audited register frame between two actual checkpoints in the same trace,
including any traversal of internal backedges. -/
theorem RowDrainSpan.recordedKeep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g start stop : Nat} {F G : List (Nat × Value)}
    (span : RowDrainSpan) (hs : span.lo ≤ start) (hStrict : start < stop)
    (hStop : stop < span.stop) (hEq : span.stop = span.bypass)
    (hStopSites : ∀ pc ∈ Assumptions.swExp2Sites, pc < stop)
    (hBypassSites : ∀ pc ∈ Assumptions.swExp2Sites, pc < span.bypass)
    (hAudit : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected (F.map Prod.fst) i.op) = true)
    (hSegments : span.segmentKeeps (F.map Prod.fst))
    (hBefore : (kernel.code.drop stop).all (fun i => staysPastEvent stop i.op) = true)
    (hAfter : (kernel.code.drop span.bypass).all
      (fun i => staysPastEvent span.bypass i.op) = true)
    (c : OpeningTripCursor l X g start F) (u : OpeningTripCursor l X g stop G) :
    Holds u.ready.regs F := by
  have hNoBack (events : List Event) :
      ¬TraceReach kernel Assumptions.all l g u.ready events c.ready := by
    intro h
    have hPc := (show RowDrainSpan from ⟨span.lo,stop,stop⟩).traceAboveExit h hBefore
      hStopSites u.checkpoint.1.ge
    exact (Nat.not_le_of_lt hStrict) (c.checkpoint.1 ▸ hPc)
  obtain ⟨_,hPath⟩ := recordedCheckpointsPath c.bounded u.bounded c.recorded
    c.localSteps u.recorded u.localSteps hNoBack
  have hTail {a b : TState} {events : List Event}
      (ab : TraceReach kernel Assumptions.all l g a events b) (ha : span.bypass ≤ a.pc) :
      span.bypass ≤ b.pc :=
    span.traceAboveExit ab hAfter hBypassSites ha
  have valid {s t : TState} {events : List Event}
      (path : TraceReach kernel Assumptions.all l g s events t)
      (ha : span.lo ≤ s.pc) (hb : t.pc < span.bypass) (hSub : s.sub ≤ 3)
      (hScratch : ScoreScratchState s) (hRegs : Holds s.regs F) : Holds t.regs F := by
    have next {a b t : TState} {ev : Option Event} {events : List Event}
        (he : WStep kernel Assumptions.all l g a ev b)
        (hRest : TraceReach kernel Assumptions.all l g b events t)
        (hA : span.lo ≤ a.pc) (hB : t.pc < span.bypass) (hSub : a.sub ≤ 3)
        (hScratch : ScoreScratchState a) (hRegs : Holds a.regs F) :
        span.lo ≤ b.pc ∧ b.sub ≤ 3 ∧ ScoreScratchState b ∧ Holds b.regs F := by
      have hHi : a.pc < span.stop := by
        by_contra! hBig
        have hEnd := hTail (show TraceReach kernel Assumptions.all l g a ev.toList b from
          by
            rcases he with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
            · exact .tau hTau (.refl _)
            · exact .event hEvent (.refl _)) (by omega)
        exact (Nat.not_le_of_lt hB) (hTail hRest hEnd)
      obtain ⟨hLo,_,hS,hScratch',hValues⟩ :=
        span.step hp hAudit hSegments hA hHi hSub hScratch hRegs he
      exact ⟨hLo,hS,hScratch',hValues⟩
    induction path with
    | refl => exact hRegs
    | tau ht hRest ih =>
      obtain ⟨hA,hSub,hScratch,hR⟩ := next (.inl ⟨rfl,ht⟩) hRest ha hb hSub hScratch hRegs
      exact ih hA hb hSub hScratch hR
    | event he hRest ih =>
      obtain ⟨hA,hSub,hScratch,hR⟩ := next (.inr ⟨_,rfl,he⟩) hRest ha hb hSub hScratch hRegs
      exact ih hA hb hSub hScratch hR
  exact valid hPath (c.checkpoint.1.symm ▸ hs) (u.checkpoint.1.symm ▸ (hEq ▸ hStop))
    (by rw [c.checkpoint.2.1]; decide)
    (scratchStateOfClear ⟨c.checkpoint.2.1,c.checkpoint.2.2.1⟩) c.checkpoint.2.2.2.2

end PTX.Kernels.TmlFa4Fwd.Thread
