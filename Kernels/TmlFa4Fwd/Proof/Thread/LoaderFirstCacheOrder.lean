-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyFacts
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption EventFrame Prologue

set_option maxRecDepth 100000 in
private theorem afterFirstEmptyCode :
    (kernel.code.drop 520).all (fun ins => Thread.staysPastEvent 520 ins.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterFirstEmptySegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some segment => decide (520 ≤ segment.stop)
      | none => false) = true := by kernel_rfl

private theorem afterFirstEmpty {l : Launch} {g : Nat} {t u : TState}
    {events : List Event} (hTrace : TraceReach kernel Assumptions.all l g t events u)
    (ht : 520 ≤ t.pc) : 520 ≤ u.pc := by
  induction hTrace with
  | refl => exact ht
  | tau ht' _ ih => exact ih (Thread.eventTailStepOfAudit afterFirstEmptyCode
      afterFirstEmptySegments ht (.inl ⟨rfl,ht'⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit afterFirstEmptyCode
      afterFirstEmptySegments ht (.inr ⟨_,rfl,he⟩))

private theorem beforeFirstEmpty {l : Launch} {g : Nat} {t u : TState}
    {events : List Event} (hTrace : TraceReach kernel Assumptions.all l g t events u)
    (hu : u.pc < 520) : ∀ e ∈ events, e.pc < 520 := by
  induction hTrace with
  | refl => simp
  | tau _ _ ih => exact ih hu
  | @event t v u es e he hTail ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hMem
    · by_contra! hLate
      have hAt := (estep_source_pc he).symm ▸ hLate
      have hNext := Thread.eventTailStepOfAudit afterFirstEmptyCode
        afterFirstEmptySegments hAt (.inr ⟨_,rfl,he⟩)
      have hFloor := afterFirstEmpty hTail hNext
      omega
    · exact ih hu x hMem

/-- At the first empty wait, a returned whole-trace loader lane has published no tile. -/
theorem noCachePublicationAtFirstEmpty {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} {t u : TState}
    (hRun : Run kernel Assumptions.all l g {} (X.tr g) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    (hAt : u.pc = 517) : ∀ (i : Nat) (loc : Loc), ¬ X.AsyncArrive (g,i) loc true := by
  rintro i loc ⟨pc,he⟩
  obtain ⟨⟨site,rfl⟩,_,_,_⟩ := TmlFa4Fwd.Loader.actualAsyncArrival hX he
  have hBound : 520 ≤ TmlFa4Fwd.Loader.copyCommitPc site + 1 := by
    fin_cases site <;> decide
  have hReach := hRun.returning_reach.append (TraceReach.of_local hLocal)
  rw [List.append_nil] at hReach
  have hLo := beforeFirstEmpty hReach (show u.pc < 520 by rw [hAt]; decide) _
    (List.mem_of_getElem? he)
  exact (Nat.not_lt_of_ge hBound) hLo

/-- Every actual loader thread is one of the CTA cache producer lanes. -/
theorem producerOfLoaderWarp {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : 14 ≤ warpIndex l g) :
    ∃ lane : Fin 64, g = producer l (g/l.block) lane := by
  have hLo : 448 ≤ g % l.block := by unfold warpIndex at hg; omega
  have hHi : g % l.block < 512 := by rw [hp.block]; omega
  let lane : Fin 64 := ⟨g % l.block - 448,by omega⟩
  have hSplit := Nat.mod_add_div g l.block
  rw [Nat.mul_comm l.block (g/l.block)] at hSplit
  exact ⟨lane,by dsimp [producer,TmlFa4Fwd.Loader.readyProducer,lane]; omega⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
