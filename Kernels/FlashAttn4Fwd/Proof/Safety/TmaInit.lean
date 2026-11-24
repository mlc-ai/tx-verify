-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Kernels.FlashAttn4Fwd.Proof.Interface.Cluster
public import Lemmas.Protocol.FirstPublished
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Every table barrier's records lie in its initialization's lifetime

The mbarrier objects of the kernel are the 37 table barriers of each CTA (`FBar`). The
initialization protocol shows that each is initialized first, once, without fault, with its count
(`TableInit`, the protocol's `InitFirst.init_first`), and initialized once a user after the start
exists (`InitsExist`, `InitFirst.init_exists`). Every other record of a barrier is issued by an
event of its cluster after the start (`record_issuer`): a poll, an arrival or a commit's arrive-on
names a barrier of its issuer's pair (`AsyncFacts.mbar_pair`), a copy completes on a ring barrier
of its pair (`AsyncFacts.copy_ring`, `RingFacts.issue`). The cluster start publishes every
initialization to such events (`InitsPublished`, `ClusterStart.init_published`). So every record
lies in its barrier's initialization lifetime (`record_published`), and every initialization record
is fault-free (`init_fault_free`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every table barrier is initialized first, once, without fault, with its count (the
initialization protocol's `InitFirst.init_first`). -/
def TableInit (L : Launch) (X : Execution) : Prop :=
  ∀ (b : FBar) (cta : Nat), PairTmaRing.InitFirst X (b.loc L cta) b.count

/-- A table barrier of the pair of an event after the start is initialized (the initialization
protocol's `InitFirst.init_exists`). -/
def InitsExist (L : Launch) (X : Execution) : Prop :=
  ∀ (b : FBar) {cta g j : Nat} {ev : Event}, X.get (g, j) = some ev → ¬ PreKind ev.kind →
    (∀ f, ev.kind ≠ .ub f) → ctaOf L g / 2 = cta / 2 →
      ∃ e pc n, X.get e = some ⟨pc, .mbInit (b.loc L cta) n⟩

/-- Every barrier initialization is published to every event of its cluster after the start (the
cluster start's `ClusterStart.init_published`). -/
def InitsPublished (L : Launch) (X : Execution) : Prop :=
  ∀ {g0 a pc c : Nat} {m : Loc}, X.get (g0, a) = some ⟨pc, .mbInit m c⟩ →
    ∀ {g j : Nat} {ev : Event}, X.get (g, j) = some ev → ¬ PreKind ev.kind →
      (∀ f, ev.kind ≠ .ub f) → clusterOf L g0 = clusterOf L g → InitPublished L X (g0, a) (g, j) m

/-- **A table barrier's records other than initializations are of its cluster, after the
start.** -/
theorem record_issuer (hX : Consistent L kernel asms mem0 X) (hr : RingFacts L X)
    (htm : TmemFacts L X) (ha : AsyncFacts P L X) {b : FBar} {cta : Nat} {s : Record Ref}
    (hs : s ∈ X.objects (b.loc L cta)) (hnon : ∀ n, s.action ≠ .init n) :
    ∃ ev, X.get s.id.issuer = some ev ∧ ¬ PreKind ev.kind ∧ (∀ f, ev.kind ≠ .ub f) ∧
      ctaOf L s.id.issuer.1 / 2 = cta / 2 := by
  have hpair : ∀ {e : EvId}, X.UsesMbar e (b.loc L cta) → ctaOf L e.1 / 2 = cta / 2 := by
    intro e hu
    obtain ⟨b', c', hm, hc'⟩ := ha.mbar_pair hu
    rw [(FBar.loc_inj hm).2]
    exact hc'.symm
  cases record_source hX.tma.2.2.1 hs with
  | init _ _ ha' => exact absurd ha' (hnon _)
  | inval _ he _ => exact absurd he htm.no_inval
  | @wait g j pc p ok acq sc hid he ha' =>
    refine ⟨_, by rw [hid]; exact he, by simp [PreKind], by simp, ?_⟩
    rw [hid]
    exact hpair (.inr (.inr (.inr (.inr (.inl ⟨pc, p, ok, acq, sc, he⟩)))))
  | @arrive g j pc tx c rel sc hid he ha' =>
    refine ⟨_, by rw [hid]; exact he, by simp [PreKind], by simp, ?_⟩
    rw [hid]
    exact hpair (.inl ⟨tx, c, rel, sc, pc, he⟩)
  | @tensor i pc a sp hid he hm ha' =>
    obtain ⟨b', c', hring, hm'⟩ := ha.copy_ring he
    obtain ⟨-, hc', -⟩ := hr.issue (Frame.lt_of_get hX he) he hm' hring
    refine ⟨_, by rw [hid]; exact he, by simp [PreKind], by simp, ?_⟩
    have hcc := (FBar.loc_inj (hm'.symm.trans hm)).2
    rw [hid]
    simp only [Ref.issuer]
    rw [← hcc, hc', pairBase]
    omega
  | increment _ he _ => exact absurd he htm.no_arriveOn
  | arriveOn _ he _ _ _ => exact absurd he htm.no_arriveOn
  | bulk _ he _ _ _ => exact absurd he htm.no_bulk
  | @commit i pc sp rank hid he htg ha' =>
    refine ⟨_, by rw [hid]; exact he, by simp [PreKind], by simp, ?_⟩
    rw [hid]
    exact hpair (.inr (.inr (.inr (.inl ⟨sp, rank, ⟨pc, he⟩, htg⟩))))
  | clc _ he _ _ _ => exact absurd he htm.no_clc

/-- **Every record of every table barrier lies in its initialization's lifetime.** -/
theorem record_published (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hr : RingFacts L X) (htm : TmemFacts L X) (ha : AsyncFacts P L X)
    (hinit : TableInit L X) (hpub : InitsPublished L X) (b : FBar) (cta : Nat)
    {r : Record Ref} (hrm : r ∈ X.objects (b.loc L cta)) :
    ObjectPublished L X (b.loc L cta) r := by
  obtain ⟨r0, h0, ha0, hf0, -⟩ := hinit b cta r hrm
  cases record_source hX.tma.2.2.1 (List.mem_of_getElem? h0) with
  | @init g0 a pc n hid he ha' =>
    rw [ha0] at ha'
    cases ha'
    have hcta : ctaOf L g0 = cta := by
      obtain ⟨b', hm, -⟩ := hc.init_site (Frame.lt_of_get hX he) he
      exact (FBar.loc_inj hm).2.symm
    refine objectPublished_of_first hX h0 hid ha0 hf0 ⟨pc, he⟩
      (fun _ _ ⟨_, hv⟩ => htm.no_inval hv) (fun s hs hnon => ?_) hrm
    obtain ⟨ev, hev, hk, hub, hcl⟩ := record_issuer hX hr htm ha hs hnon
    generalize s.id.issuer = i at hev hcl ⊢
    obtain ⟨g, j⟩ := i
    refine hpub he hev hk hub ?_
    rw [clusterOf_eq hpre, clusterOf_eq hpre, hcta]
    exact hcl.symm
  | inval _ _ ha' | arrive _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | commit _ _ _ ha'
  | clc _ _ _ _ ha' => rw [ha0] at ha'; cases ha'
  | increment _ he _ => exact absurd he htm.no_arriveOn
  | arriveOn _ he _ _ _ => exact absurd he htm.no_arriveOn
  | bulk _ he _ _ _ => exact absurd he htm.no_bulk

/-- **Every initialization record of a table barrier is fault-free.** -/
theorem init_fault_free (hinit : TableInit L X) (b : FBar) (cta : Nat) {r : Record Ref}
    (hrm : r ∈ X.objects (b.loc L cta)) (hn : ∃ n, r.action = .init n) : r.fault = none := by
  obtain ⟨r0, -, -, hf0, hone⟩ := hinit b cta r hrm
  exact fault_of_first hf0 hone hrm hn

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
