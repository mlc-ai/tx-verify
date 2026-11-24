-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
public import Lemmas.Kernel.ExitChain
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RoleSharedWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputTrace
import Lemmas.Protocol.ObjectSource

public section

/-! # CTA ownership and shared source reads at exit -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime

open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem same_cluster_owner (hpre : Pre P L mem0) {c owner : Nat}
    (hGroup : CtaInCluster L c owner) : owner = c := by
  have hSize (k : Nat) : L.clusterSizeAt k = L.clusterSize.val := by
    simp [Launch.clusterSizeAt, hpre.clusterPlaces, gridPlace, Dim3.prod, hpre.clusterSize]
  have hCluster := hGroup.2.2
  simp only [Launch.clusterOfCta, Launch.locate_regular hSize, hpre.clusterSize, Nat.div_one,
    Nat.zero_add] at hCluster
  exact hCluster.symm

/-- The last event of an exited CTA's lane can witness the lane's earlier instruction. -/
theorem exit_after (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {e : Event} (he : X.get i = some e) (hne : e.kind ≠ .exit)
    (hx : CtaExited L X (ctaOf L i.1)) :
    ∃ finish, OwnerExit L X (ctaOf L i.1) finish ∧ TraceBefore X i finish := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨tag, hl⟩ := hx i.1 hg rfl
  rw [List.getLast?_eq_getElem?] at hl
  have hGet : X.get (i.1, (X.tr i.1).length - 1) = some ⟨tag, .exit⟩ := hl
  have hi := PTX.len_of_get he
  have hLast := PTX.len_of_get hGet
  have hlt : i.2 < (X.tr i.1).length - 1 := by
    by_contra hn
    have hIndex : i = (i.1, (X.tr i.1).length - 1) := Prod.ext rfl (by omega)
    have hEq := Option.some.inj ((hIndex ▸ he).symm.trans hGet)
    exact hne (congrArg Event.kind hEq)
  exact ⟨(i.1, (X.tr i.1).length - 1), ⟨hg, rfl, tag, hGet⟩, rfl, hlt, hLast⟩

/-- An ordinary shared access belongs to the issuing CTA and finishes before its exit. -/
theorem thread_access (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {a : Acc} {w : Bool} (hi : X.Access i a w) (hSpace : a.loc.space = .shared) :
    a.loc.cta = ctaOf L i.1 ∧ (CtaExited L X a.loc.cta →
      SharedFinished L kernel Assumptions.all X (.thread i) a.loc.cta) := by
  have hOwner : a.loc.cta = ctaOf L i.1 := by
    rcases (Execution.access_iff_of_not_rmw (fun tag _ _ _ he =>
      GlobalWrites.no_rmw hX ⟨tag, he⟩)).mp hi with ⟨bytes, hr, _⟩ | ⟨bytes, hw, _⟩
    · obtain ⟨g, j⟩ := i
      exact (OrdinaryReadWindow.read_window hpre hX hs ht hr).2.1
    · exact RoleSharedWrites.shared_cta hpre hs hX ht hw hSpace
  exact ⟨hOwner, SharedFinished.of_access hX.outside hi hOwner.symm⟩

/-- Each tensor store reads only its issuing CTA's output staging area. -/
theorem store_owner (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {address : Nat} {sp : TensorStore.Spec} (hi : X.TensorStoreIssue i address sp) :
    sp.sharedBase.cta = ctaOf L i.1 := by
  obtain ⟨_, j, hd, hSite⟩ := GlobalWrites.outputTile_site hs hX ht hi
  obtain ⟨g, k⟩ := i
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hSpec := (Wg0OutputTrace.tileSpec hpre hX (hs g hg).machine hi hd hSite).2
  rw [hSpec]
  rfl

/-- The read completion of an output store precedes its issuer's exit by A8. -/
theorem store_reads_finished (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {address : Nat} {sp : TensorStore.Spec} (hi : X.TensorStoreIssue i address sp)
    (hx : CtaExited L X (ctaOf L i.1)) :
    SharedFinished L kernel Assumptions.all X (.async i .readsDone) (ctaOf L i.1) := by
  obtain ⟨tag, he⟩ := hi
  obtain ⟨finish, hExit, hBefore⟩ := exit_after hX he (by simp) hx
  exact Wg0OutputTrace.readsFinished hX (fun g hg => (hs g hg).machine) ht ⟨tag, he⟩ hBefore hExit

/-- Each performed shared read of an output store precedes its read completion. -/
theorem store_byte_finished (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {address x y k : Nat} {sp : TensorStore.Spec}
    (hi : X.TensorStoreIssue i address sp) (hp : X.RefPresent (.async i (.read (.store x y k))))
    (hx : CtaExited L X (ctaOf L i.1)) :
    SharedFinished L kernel Assumptions.all X (.async i (.read (.store x y k))) (ctaOf L i.1) := by
  have hf := store_reads_finished hX hs ht hi hx
  exact SharedFinished.of_stage (j := i) (q := .readsDone) hp
    (.inr ⟨rfl, rfl, rfl, hp, hf.1⟩) hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime
