-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetimeBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorLoadSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingObjects
import Lemmas.Protocol.ObjectSource
import Lemmas.Protocol.Region

@[expose] public section

/-! # Exhaustion of shared lifetime uses -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime

open PTX PTX.Flow PTX.AsyncCopy MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Load notifications finish before an exit of the issuing CTA. -/
def LoadNotified (L : Launch) (X : Execution) : Prop :=
  ∀ i address sp, X.TensorIssue i address sp → CtaExited L X (ctaOf L i.1) →
    SharedFinished L kernel Assumptions.all X (.async i (.notify .load)) (ctaOf L i.1)

/-- Tensor Core operations with shared operands finish before an exit of the issuing CTA. -/
def MmaFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i, X.TcAsync i → CtaExited L X (ctaOf L i.1) →
    SharedFinished L kernel Assumptions.all X (.async i .mmaDone) (ctaOf L i.1)

/-- Commit notifications finish before an exit of the issuing CTA. -/
def CommitFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i sp rank m, X.Commit i sp → TcCommit.target sp rank = some m →
    CtaExited L X (ctaOf L i.1) →
    SharedFinished L kernel Assumptions.all X (.async i (.tcNotify rank)) (ctaOf L i.1)

private theorem load_byte_finished (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {address x y k : Nat} {sp : TensorCopy.Spec}
    (hi : X.TensorIssue i address sp) (hSlot : (TensorTransfer.slotAt sp.descriptor x y k).isSome)
    (hn : SharedFinished L kernel Assumptions.all X (.async i (.notify .load)) (ctaOf L i.1)) :
    SharedFinished L kernel Assumptions.all X (.async i (.write (.load x y k))) (ctaOf L i.1) := by
  obtain ⟨o, ho, hnote⟩ := hn.1
  obtain ⟨⟨mapAddr, hi'⟩, hCopy, _⟩ := hX.tensor i o ho
  have hSpec := (Kind.tensorIssue.inj (congrArg Event.kind
    (Option.some.inj (hi.choose_spec.symm.trans hi'.choose_spec)))).2
  rw [hSpec] at hSlot
  obtain ⟨slot, hs⟩ := Option.isSome_iff_exists.mp hSlot
  obtain ⟨value, hv⟩ := hCopy.complete hnote slot
  have hp : X.RefPresent (.async i (.write (.load x y k))) := ⟨o, slot, value, ho, hs, hv⟩
  exact SharedFinished.of_stage (j := i) (q := .notify .load) hp
    (.inr ⟨rfl, rfl, rfl, rfl, hp, hn.1⟩) hn

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hLoad : LoadNotified L X)
include hpre hX hs ht hLoad

private theorem action_use (hCommit : CommitFinished L X) {e : Ref} {c addr : Nat}
    {act : MBarrier.Action} (hAct : objectAction X X.async ⟨.shared, c, addr⟩ e = some act) :
    c = ctaOf L e.issuer.1 ∧ (CtaExited L X c → SharedFinished L kernel Assumptions.all X e c) := by
  let recd : MBarrier.Record Ref := ⟨e, act, { state := none }, none⟩
  have hSource := objectAction_source (r := recd) hAct
  have own {i : EvId} (hu : X.UsesMbar i ⟨.shared, c, addr⟩) : c = ctaOf L i.1 := by
    obtain ⟨g, j⟩ := i
    exact (mbar_own hpre hX hs ht hu).2
  have sync {i : EvId} {ev : Event} (he : X.get i = some ev) (hne : ∀ p, ev ≠ ⟨p, .exit⟩)
      (hc : c = ctaOf L i.1) :
      c = ctaOf L i.1 ∧ (CtaExited L X c →
        SharedFinished L kernel Assumptions.all X (.thread i) c) :=
    ⟨hc, SharedFinished.of_thread hX.outside he hne hc.symm⟩
  cases hSource with
  | init hid he _ =>
    have h := own (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, _, he⟩))))))))
    change e = _ at hid
    subst e
    exact sync he (by simp) h
  | arrive hid he _ =>
    have h := own (.inl ⟨_, _, _, _, _, he⟩)
    change e = _ at hid
    subst e
    exact sync he (by simp) h
  | wait hid he _ =>
    have h := own (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, he⟩)))))
    change e = _ at hid
    subst e
    exact sync he (by simp) h
  | inval _ he _ => exact (Protocol.no_inval hX ⟨_, he⟩).elim
  | increment _ he _ | arriveOn _ he _ _ _ => exact (Protocol.no_async_arrive hX he rfl).elim
  | bulk _ he _ _ _ => exact (GlobalWrites.no_copy hX ⟨_, he⟩).elim
  | clc _ he _ _ _ => exact (GlobalWrites.no_clc hX ⟨_, he⟩).elim
  | tensor hid he hm _ =>
    have h := own (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, ⟨_, he⟩, hm⟩)))))))
    change e = _ at hid
    subst e
    refine ⟨h, fun hx => ?_⟩
    rw [h] at hx ⊢
    exact hLoad _ _ _ ⟨_, he⟩ hx
  | commit hid he htgt _ =>
    have h := own (.inr (.inr (.inr (.inl ⟨_, _, ⟨_, he⟩, htgt⟩))))
    change e = _ at hid
    subst e
    refine ⟨h, fun hx => ?_⟩
    rw [h] at hx ⊢
    exact hCommit _ _ _ _ ⟨_, he⟩ htgt hx

/-- A shared use names the issuing CTA. In an exited CTA the use has finished before an exit. -/
theorem use_ok (hMma : MmaFinished L X) (hCommit : CommitFinished L X) {e : Ref} {c : Nat}
    (hu : SharedUse L X e c) :
    c = ctaOf L e.issuer.1 ∧ (CtaExited L X c → SharedFinished L kernel Assumptions.all X e c) := by
  rcases hu with ⟨hp, ⟨a, w, hint, hSpace, rfl⟩ | ⟨addr, act, hAct⟩⟩ |
    ⟨i, sp, rfl, hi, hGroup⟩ | ⟨i, address, sp, x, y, k, rfl, hi, hSlot, rfl⟩ |
    ⟨i, address, sp, rfl, hi, rfl⟩ | ⟨i, p, rfl, hFinal, hu⟩
  · cases e with
    | thread i => exact thread_access hpre hX hs ht hint hSpace
    | async i p =>
      have hfp := hint.2
      cases p <;> try exact hfp.elim
      case mmaRead isB index =>
        obtain ⟨g, j⟩ := i
        have hOwner := (MmaAccessWindow.footprint hpre hX hs ht hfp.2).2.2.1
        refine ⟨hOwner, fun hx => ?_⟩
        rw [hOwner] at hx ⊢
        have hIssue : X.TcAsync (g, j) := by
          rcases hfp.2 with ⟨d, sp, acc, mask, hi, _⟩ | ⟨cp, _, _, hi, _⟩
          · exact .inl ⟨d, sp, acc, mask, hi⟩
          · exact .inr (.inl ⟨cp, hi⟩)
        have hf := hMma _ hIssue hx
        exact SharedFinished.of_stage (j := (g, j)) (q := .mmaDone) hp
          (.inr ⟨rfl, rfl, rfl, hp, hf.1⟩) hf
      case readStore x y k =>
        obtain ⟨sp, address, hi, hl, _⟩ := hfp
        have hOwner : a.loc.cta = ctaOf L i.1 := by
          obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp hl
          rw [← hLoc]
          exact store_owner hpre hX hs ht hi
        refine ⟨hOwner, fun hx => ?_⟩
        rw [hOwner] at hx ⊢
        exact store_byte_finished hX hs ht hi hp hx
      case writeLoad x y k =>
        obtain ⟨sp, address, hi, hl, _⟩ := hfp
        obtain ⟨g, j⟩ := i
        have hOwner := (TensorSharedBounds.write_loc_windows hpre hX hs ht hi hl).2.1
        refine ⟨hOwner, fun hx => ?_⟩
        rw [hOwner] at hx ⊢
        obtain ⟨_, hSlot, _⟩ := Option.map_eq_some_iff.mp hl
        exact load_byte_finished hX hi (Option.isSome_iff_exists.mpr ⟨_, hSlot⟩) (hLoad _ _ _ hi hx)
      case readLoad =>
        obtain ⟨_, _, _, hl, _⟩ := hfp
        exact (Space.noConfusion ((Execution.tensor_readLoc_global hl).symm.trans hSpace))
      case writeStore =>
        obtain ⟨_, _, _, hl, _⟩ := hfp
        exact (Space.noConfusion ((Execution.store_writeLoc_global hl).symm.trans hSpace))
      case oldStore =>
        obtain ⟨_, _, _, _, hl, _⟩ := hfp
        exact (Space.noConfusion ((Execution.store_writeLoc_global hl).symm.trans hSpace))
      case readPrefetch =>
        obtain ⟨_, _, hi, _, _⟩ := hfp
        exact (TensorLoadSources.no_tensor_prefetch hX hi).elim
      case readCopy =>
        rcases hfp with ⟨_, hi, _⟩ | hi
        · exact (GlobalWrites.no_copy hX hi).elim
        · exact (GlobalWrites.no_bulk_prefetch hX hi).elim
      case writeCta =>
        obtain ⟨_, _, hi, _, _⟩ := hfp
        exact (GlobalWrites.no_clc hX hi).elim
      case writeCopy =>
        obtain ⟨_, hi, _, _⟩ := hfp
        exact (GlobalWrites.no_copy hX hi).elim
      case writeElem =>
        obtain ⟨_, hi, _⟩ := hfp
        exact (GlobalWrites.no_copy hX hi).elim
      case oldElem =>
        obtain ⟨_, _, hi, _, _⟩ := hfp
        exact (GlobalWrites.no_copy hX hi).elim
  · exact action_use hpre hX hs ht hLoad hCommit hAct
  · have hOwner := same_cluster_owner hpre hGroup.1
    exact ⟨hOwner, SharedFinished.of_thread hX.outside hi.choose_spec (by simp) hOwner.symm⟩
  · obtain ⟨slot, hSlot'⟩ := Option.isSome_iff_exists.mp hSlot
    have hl : TensorCopy.writeLoc sp x y k = some (sp.sharedLoc slot) := by
      simp [TensorCopy.writeLoc, hSlot']
    obtain ⟨g, j⟩ := i
    have hOwner : sp.sharedBase.cta = ctaOf L g :=
      (TensorSharedBounds.write_loc_windows hpre hX hs ht hi hl).2.1
    refine ⟨hOwner, fun hx => ?_⟩
    rw [hOwner] at hx ⊢
    exact load_byte_finished hX hi hSlot (hLoad _ _ _ hi hx)
  · have hOwner := store_owner hpre hX hs ht hi
    exact ⟨hOwner, fun hx => hOwner ▸ store_reads_finished hX hs ht hi (hOwner ▸ hx)⟩
  · rcases hFinal with ⟨sp, _, hi, _, rfl⟩ | ⟨sp, hi, _, rfl⟩ |
      ⟨m, noinc, ⟨tag, he⟩, rfl⟩ | ⟨htc, rfl⟩ | ⟨sp, _, _, hi, _, rfl⟩ |
      ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
    · exact (GlobalWrites.no_copy hX hi).elim
    · exact (GlobalWrites.no_copy hX hi).elim
    · exact (Protocol.no_async_arrive hX he rfl).elim
    · obtain ⟨g, j⟩ := i
      have hOwner : c = ctaOf L g := by
        rcases hu with ⟨d, sp, acc, mask, hi, hc⟩ | ⟨cp, hi, hc⟩
        · rcases (MmaAccessWindow.mma_spec hpre hX hs ht hi).2 with
            ⟨block, k, _, rfl, _⟩ | ⟨block, k, _, rfl, _⟩
          · exact hc.elim id id
          · exact hc.elim id id
        · obtain ⟨k, rfl⟩ := MmaAccessWindow.copy_spec hpre hX hs ht hi
          simpa [queryCopySpec] using hc
      refine ⟨hOwner, fun hx => ?_⟩
      rw [hOwner] at hx ⊢
      exact hMma _ htc hx
    · exact (GlobalWrites.no_clc hX hi).elim
    · obtain ⟨address, sp, hi, _, rfl⟩ := hu
      obtain ⟨g, j⟩ := i
      have hOwner := (mbar_own hpre hX hs ht
        (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨address, sp, hi, rfl⟩)))))))).2
      refine ⟨hOwner, fun hx => ?_⟩
      rw [hOwner] at hx ⊢
      exact hLoad _ _ _ hi hx
    · exact hu.elim
    · obtain ⟨sp, m, hi, htgt, rfl⟩ := hu
      obtain ⟨g, j⟩ := i
      have hOwner := (mbar_own hpre hX hs ht (.inr (.inr (.inr (.inl ⟨sp, _, hi, htgt⟩))))).2
      refine ⟨hOwner, fun hx => ?_⟩
      rw [hOwner] at hx ⊢
      exact hCommit _ _ _ _ hi htgt hx

/-- The lifetime check is discharged by the three issued-asynchronous completion obligations. -/
theorem no_unsafe_of_completions (hMma : MmaFinished L X) (hCommit : CommitFinished L X) :
    ¬ SharedLifetimeUnsafe L kernel Assumptions.all X := by
  rintro ⟨e, c, hu, ⟨hWrong, _⟩ | ⟨hExit, hUnfinished⟩⟩
  · exact hWrong (use_ok hpre hX hs ht hLoad hMma hCommit hu).1
  · exact hUnfinished ((use_ok hpre hX hs ht hLoad hMma hCommit hu).2 hExit)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime
