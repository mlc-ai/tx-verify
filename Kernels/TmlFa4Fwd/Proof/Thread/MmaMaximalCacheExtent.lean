-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSelectedCacheExtent
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstGroupShuffles
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
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Termination
import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Epilogue

private theorem metadataTailCode :
    (kernel.code.drop 2110).all (fun ins => staysPastEvent 2110 ins.op) = true := by
  decide +kernel

private theorem metadataTailSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2110 ≤ seg.stop)
      | none => false) = true := by
  decide +kernel

private theorem metadataFloorOfLocal {l : Launch} {g : Nat} {s u : TState}
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u)
    (hFloor : 2110 ≤ s.pc) : 2110 ≤ u.pc := by
  induction hLocal with
  | refl => exact hFloor
  | tail _ hStep ih =>
    exact eventTailStepOfAudit metadataTailCode metadataTailSegments ih (.inl ⟨rfl, hStep⟩)

private theorem metadataFloorOfLateMember {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {ending : Option TState}
    (hRun : Run kernel Assumptions.all l g s events ending)
    (hFloor : 2110 ≤ s.pc ∨ ∃ e ∈ events, 2110 ≤ e.pc) :
    ∀ t, ending = some t → 2110 ≤ t.pc := by
  induction hRun with
  | nil t =>
    rintro _ ⟨rfl⟩
    simpa using hFloor
  | step hLocal hStep _ ih =>
    apply ih
    rcases hFloor with hFloor | ⟨e, he, hEvent⟩
    · exact .inl (eventTailStepOfAudit metadataTailCode metadataTailSegments
        (metadataFloorOfLocal hLocal hFloor) (.inr ⟨_,rfl,hStep⟩))
    · rw [List.mem_cons] at he
      rcases he with rfl | hRest
      · rw [estep_source_pc hStep] at hEvent
        exact .inl (eventTailStepOfAudit metadataTailCode metadataTailSegments
          hEvent (.inr ⟨_,rfl,hStep⟩))
      · exact .inr ⟨e, hRest, hEvent⟩
  | last => simp

/-- The MMA metadata checkpoint precedes every observed event of its work body. -/
theorem selectedMetadataBeforeBodyEvent {l : Launch} {g i pos : Nat} {X : Execution}
    {t u : TState} (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    (hAt : u.pc = 2109) {e : Event} (he : X.get (g,i) = some e) (hFloor : 2110 ≤ e.pc) :
    pos ≤ i := by
  by_contra! hBefore
  have hRecorded : ((X.tr g).take pos)[i]? = some e := by
    rw [List.getElem?_take_of_lt hBefore]
    exact he
  have hPast := metadataFloorOfLateMember hPrefix
    (.inr ⟨_, List.mem_of_getElem? hRecorded, hFloor⟩) t rfl
  have hStill := metadataFloorOfLocal hLocal hPast
  rw [hAt] at hStill
  omega

/-- A terminal commit in a maximal scheduled CTA follows its lane's actual
metadata checkpoint, so all selected cache acquisitions are available. -/
theorem selectedCacheExtentOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {final : EvId} {spec : TcCommit.Spec}
    (hFinal : SecondOutputCommit X final spec)
    (hWork : final.1 / l.block < tilePrefix p p.batch * p.heads) :
    Nonempty (SelectedCacheExtent l p X final) := by
  obtain ⟨batch, ⟨hb,hLo,hHi⟩, _⟩ := tileBatch_existsUnique p hWork
  have hg := event_thread_lt hMax.1 hFinal.decoded
  obtain ⟨pos,t,u,o,_,_,_,_,_,hAt,hPrefix,hLocal,hRun⟩ :=
    Allocation.mmaMetadataOfMaximal hp hMax hg (hFinal.issuerWarp hp hMax.1)
      (hFrame.metadataProtected hp).1 hb hLo hHi
  have hReached := selectedMetadataBeforeBodyEvent hPrefix hLocal hAt.1 hFinal.decoded
    (show 2110 ≤ (2646 : Nat) by decide)
  have hSuffix := hRun.after_local_nonempty hLocal (by
    have hGet : (X.tr final.1).drop pos ≠ [] := by
      intro hEmpty
      have hGet := hFinal.decoded
      change (X.tr final.1)[final.2]? = _ at hGet
      have hIndex : ((X.tr final.1).drop pos)[final.2-pos]? = some ⟨2646,.tc (.commit spec)⟩ := by
        rwa [List.getElem?_drop, Nat.add_sub_of_le hReached]
      simp [hEmpty] at hIndex
    exact hGet)
  exact ⟨SelectedCacheExtent.ofSelectedPrefix hp hMax.1 hFrame hFinal
    hb hLo hHi hAt hSuffix (.inr hReached)⟩

private theorem SelectedCacheExtent.restrict {p : Params} {l : Launch} {X Y : Execution}
    {final : EvId} {e : Event} (hExtent : SelectedCacheExtent l p Y final)
    (hPrefix : X.le Y) (hFinal : X.get final = some e) :
    Nonempty (SelectedCacheExtent l p X final) := by
  refine ⟨⟨hExtent.batch,hExtent.batch_lt,hExtent.cta_lower,hExtent.cta_upper,?_⟩⟩
  intro use hUse
  obtain ⟨pos,hBefore,⟨e',hRead,hWait⟩,hCount⟩ := hExtent.acquires use hUse
  have hLast := (List.getElem?_eq_some_iff.mp hFinal).1
  have hHere : pos < (X.tr final.1).length := hBefore.2.1.trans hLast
  have hGet : X.get (final.1,pos) = some e' := by
    obtain ⟨suf, hSuf⟩ := hPrefix.1 final.1
    change (X.tr final.1)[pos]? = some e'
    change (Y.tr final.1)[pos]? = some e' at hRead
    rwa [← hSuf,List.getElem?_append_left hHere] at hRead
  have hTake : (Y.tr final.1).take pos = (X.tr final.1).take pos := by
    obtain ⟨suf, hSuf⟩ := hPrefix.1 final.1
    rw [← hSuf, List.take_append_of_le_length hHere.le]
  exact ⟨pos,⟨rfl,hBefore.2.1,hLast⟩,⟨e',hGet,hWait⟩,by
    simpa only [atPrefix, hTake] using hCount⟩

/-- The extent of an observed terminal commit depends only on the lane's prefix
through that commit. A bounded maximal extension supplies its selected metadata. -/
theorem selectedCacheExtentOfConsistentPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {final : EvId} {spec : TcCommit.Spec} (hFinal : SecondOutputCommit X final spec)
    (hWork : final.1 / l.block < tilePrefix p p.batch * p.heads) :
    Nonempty (SelectedCacheExtent l p X final) := by
  obtain ⟨Y,hY,hPrefix,hLargest⟩ := bounded_largest_extension (terminates hp) hX
  have hMax : Maximal l kernel Assumptions.all m Y :=
    ⟨hY, fun Z hZ hExt => hLargest Z hZ (Execution.le_trans hPrefix hExt)⟩
  have hCommit := hFinal.mono hPrefix
  obtain ⟨extent⟩ := selectedCacheExtentOfMaximal hp hMax (hFrame Y hY) hCommit hWork
  exact extent.restrict hPrefix hFinal.decoded

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
