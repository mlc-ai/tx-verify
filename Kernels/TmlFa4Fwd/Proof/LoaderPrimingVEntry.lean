-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
public import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchRows
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private def primingVWaitSite : DrainWaitSite := ⟨782, 9611, 1925, 1926⟩

/-- Initial V-ring reuse acquires the priming V slot at parity one. -/
def primingVWaitEvent (l : Launch) (g : Nat) (ok : Bool) : Event :=
  ⟨782, .wait ⟨.shared, g / l.block, l.sharedBase + 64⟩ 1 ok true .cta⟩

/-- The first iteration has selected the first page and row slots on the local stack. -/
def primingVFirstScratchFacts (l : Launch) : List (Nat × Value) :=
  [(7600, b64 (l.localBase + kvLocalOffset 3 0)), (7599, b64 0), (9536, b64 0),
   (774, .pred true), (6, .pred true)]

/-- Compute both operands of the opening V empty wait from the shared base. -/
theorem primingVWaitPrep {l : Launch} {g : Nat} (hAddr : l.sharedBase + 64 < 2 ^ 32) :
    Seg kernel [] l g 2 780 [(2535, b32 l.sharedBase)] 782
      [(1925, b32 (l.sharedBase + 64)), (1926, b32 1)] := by
  intro t ht
  seg_fp ht using norm_bits

/-- Compute the initial V page selector from the stable stack base. -/
theorem primingVFirstScratchPrep {l : Launch} {g : Nat}
    (hStack : l.localBase + 128 ≤ 2 ^ 32) :
    Seg kernel [] l g 5 785 [(7295, b64 (l.localBase + 96))] 790
      (primingVFirstScratchFacts l) := by
  have hFit : l.localBase + 96 < 2 ^ 64 := by omega
  intro t ht
  simp only [primingVFirstScratchFacts, show kvLocalOffset 3 0 = 96 by decide]
  have hMod : (l.localBase + 96) % 18446744073709551616 = l.localBase + 96 :=
    Nat.mod_eq_of_lt hFit
  seg_fp ht using first | rfl | norm_bits [hMod]

/-- The caller's V facts survive the decoded wait prep, result predicate, and first stack setup. -/
structure PrimingVEntryFrame (F : List (Nat × Value)) : Prop where
  waitPrep : ((kernel.code.drop 780).take 2).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  scratchPrep : ((kernel.code.drop 785).take 5).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  resultFresh : ∀ pair ∈ F, pair.1 ≠ 9611

/-- The actual V wait retries until success and reaches the first metadata load with the
caller's frame and the first-slot registers. -/
theorem primingVWaitAndScratchLaneInPrefix {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {events : List Event} {F : List (Nat × Value)}
    (hF : PrimingVEntryFrame F) (hBase : (2535, b32 l.sharedBase) ∈ F)
    (hStack : (7295, b64 (l.localBase + 96)) ∈ F)
    {ending : Option TState}
    (ht : At t 780 F) (hr : Run kernel Assumptions.all l g t events ending)
    (hProgress : ending = none ∨ ∃ e ∈ events, 782 < e.pc) :
    ∃ n u rest, events = List.replicate n (primingVWaitEvent l g false) ++
        (primingVWaitEvent l g true :: rest) ∧
      At u 790 (primingVFirstScratchFacts l ++ F) ∧
      Run kernel Assumptions.all l g u rest ending := by
  let operands := [(1925, b32 (l.sharedBase + 64)), (1926, b32 1)]
  have hAddr : l.sharedBase + 64 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase + 64) % 8 = 0 := by have := hp.shared.1; omega
  obtain ⟨v, hv, hV⟩ := primingVWaitPrep (g := g) hAddr t (ht.mono ⟨holds_mem ht.2.2.2.2 hBase,
    trivial⟩)
  obtain ⟨hvA, hVFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) ht.1
    hF.waitPrep (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hAt : At v 782 (operands ++ F) := hV.mono ((holds_append ..).mpr
    ⟨hV.2.2.2.2, holdsSchedulerFrame ht.2.2.2.2 hVFrame (fun _ hm => List.mem_map_of_mem hm)⟩)
  have hFresh : ∀ pair ∈ operands ++ F, pair.1 ≠ primingVWaitSite.result := by
    intro pair hPair
    rcases List.mem_append.mp hPair with h | h
    · simp [operands] at h
      rcases h with rfl | rfl <;> simp [primingVWaitSite]
    · exact hF.resultFresh pair h
  have hMore : events ≠ [] := by
    intro h
    rw [h] at hr hProgress
    rcases hProgress with hDone | ⟨e, he, _⟩
    · rw [hDone] at hr
      cases hr
    · cases he
  obtain ⟨n, w, rest, hTrace, hW, hRest⟩ :=
    loaderWaitTraceInPrefix (phase := 1) primingVWaitSite
      ⟨Flow.code_782, Flow.code_783, Flow.code_784⟩
      (by decide) hAddr hAlign (by decide) hFresh (by simp [operands, primingVWaitSite])
      (by simp [operands, primingVWaitSite]) hAt
      (hr.after_local_nonempty (run_rtg hvA) hMore) hProgress
  have hHeld := ((holds_append ..).mp hW.2.2.2.2).2
  have hStackAt : At w 785 [(7295, b64 (l.localBase + 96))] :=
    hW.mono ⟨holds_mem hHeld hStack, trivial⟩
  obtain ⟨u, hu, hU⟩ := primingVFirstScratchPrep (g := g) hp.localMemory.2.1 w hStackAt
  obtain ⟨huA, hUFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide)
    hStackAt.1 hF.scratchPrep (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hTail : rest ≠ [] := by
    intro h
    rw [h] at hRest hTrace
    rcases hProgress with hDone | ⟨e, he, hPc⟩
    · rw [hDone] at hRest
      cases hRest
    · rw [hTrace] at he
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at he
      rcases he with ⟨_, rfl⟩ | rfl <;> exact Nat.lt_irrefl 782 hPc
  exact ⟨n, u, rest, hTrace, hU.mono ((holds_append ..).mpr
    ⟨hU.2.2.2.2, holdsSchedulerFrame hHeld hUFrame (fun _ hm => List.mem_map_of_mem hm)⟩),
    hRest.after_local_nonempty (run_rtg huA) hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
