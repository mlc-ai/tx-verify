-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.Tensor
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Lemmas.Kernel.ExitChain
public import Lemmas.Protocol.Region
public import Lemmas.TensorStore.TensorStore
public import Lemmas.Step.BulkWaitReady

@[expose] public section

/-! # `SharedLifetimeUnsafe`: every use of a CTA's shared memory

ERR-SHARED-LIFETIME asks of every use of a CTA's shared memory (`SharedUse`) that the CTA started
before a use from another CTA, and that the use completes before an exit of the CTA once the CTA has
exited. The kernel's uses, by the table's rows (`use_ok`):

* **Places.** A thread's accesses are of its own CTA (`AsyncFacts.access_own`); its mbarrier
  operations and a commit's targets name a barrier of its pair (`mbar_pair`); a tensor load writes
  its loader's CTA and completes on the pair's even CTA (`load_source`); a tensor store reads its
  own CTA (`store_base`); an MMA's operands are in its pair (`mma_pair`). The kernel has no linear
  copy or prefetch, `cp.async.mbarrier.arrive`, CLC request, Tensor Core copy or tensor prefetch.
  Every use of another CTA is of the issuer's cluster, by an event after the start, so the cluster
  start shows the CTA started (`PeersStarted`, the cluster start's `ClusterStart.peer_started`).
* **Own-CTA thread instructions** precede their thread's exit (`SharedFinished.of_thread`).
* **Tensor stores' source reads** are observed by the lane's `cp.async.bulk.wait_group.read`
  (`StoreSrc`), which guards the lane's exit (`store_reads_finished`).
* **The rest** are the protocols' chains (named premises): a thread's use of the other CTA of its
  pair (remote arrivals, the leader's commit issue: the TMEM-release handshake chain,
  `PeerThreadFinished`); a tensor load's writes and completion (`CopyFinished`); an MMA's
  completion (`MmaFinished`, whose operand reads finish with it); a commit's arrive-ons
  (`CommitFinished`: observed by the consumers' waits, the last Q0-empty arrive-on through the
  commit-order assumption, `SharedFinished.of_commitNext`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Premises -/

/-- Every CTA of the cluster of an event after the start started before its issue (the cluster
start's `ClusterStart.peer_started`). -/
def PeersStarted (L : Launch) (X : Execution) : Prop :=
  ∀ {g j : Nat} {ev : Event}, X.get (g, j) = some ev → ¬ PreKind ev.kind →
    (∀ f, ev.kind ≠ .ub f) → ∀ {owner : Nat}, owner < L.grid →
      L.clusterOfCta owner = clusterOf L g → ∀ (e : Ref), e.issuer = (g, j) →
        PeerSharedStarted L kernel asms X e owner

/-- A thread instruction's use of the other CTA of its pair completes before an exit of that CTA
(the TMEM-release handshake chain: the remote arrivals of the softmax, correction and MMA warps and
the leader's commit issue precede `bar.sync 2` and the handshake into the other CTA's MMA warp's
exit). -/
def PeerThreadFinished (L : Launch) (X : Execution) : Prop :=
  ∀ (i : EvId) (c : Nat), SharedUse L X (.thread i) c → c ≠ ctaOf L i.1 → CtaExited L X c →
    SharedFinished L kernel asms X (.thread i) c

/-- A tensor load's writes complete before an exit of the destination CTA, and its completion
before an exit of the mbarrier's CTA (observed by the leader MMA warp's full-barrier waits). -/
def CopyFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i a (s : TensorCopy.Spec), X.TensorIssue i a s →
    (∀ x y k, (TensorTransfer.slotAt s.descriptor x y k).isSome → CtaExited L X s.sharedBase.cta →
      SharedFinished L kernel asms X (.async i (.write (.load x y k))) s.sharedBase.cta) ∧
    (CtaExited L X s.mbar.cta →
      SharedFinished L kernel asms X (.async i (.notify .load)) s.mbar.cta)

/-- An MMA's completion precedes an exit of each CTA holding its operands (its commit observed by
the softmax's and correction's waits in both CTAs). -/
def MmaFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i d (s : TcMma.OperandSpec) acc mask (c : Nat), X.MmaIssue i d s acc mask →
    (c = s.lowCta ∨ c = s.highCta) → CtaExited L X c →
      SharedFinished L kernel asms X (.async i .mmaDone) c

/-- A commit's arrive-on completes before an exit of the target barrier's CTA (observed by the
consumers' waits; the last Q0-empty arrive-on by the commit-order assumption,
`SharedFinished.of_commitNext`). -/
def CommitFinished (L : Launch) (X : Execution) : Prop :=
  ∀ i (s : TcCommit.Spec) rank (m : Loc), X.Commit i s → TcCommit.target s rank = some m →
    CtaExited L X m.cta → SharedFinished L kernel asms X (.async i (.tcNotify rank)) m.cta

/-! ### Discharged rows -/

/-- A use of a CTA of the issuer's pair, by an event after the start, follows the CTA's start. -/
theorem started_of (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : PeersStarted L X) {e : Ref} {ev : Event} (he : X.get e.issuer = some ev)
    (hk : ¬ PreKind ev.kind) (hub : ∀ f, ev.kind ≠ .ub f) {c : Nat}
    (hc : c / 2 = ctaOf L e.issuer.1 / 2) : PeerSharedStarted L kernel asms X e c := by
  have hgr := hpre.grid
  generalize hi : e.issuer = i at he hc
  obtain ⟨g, j⟩ := i
  change c / 2 = ctaOf L g / 2 at hc
  have := cta_lt (Frame.lt_of_get hX he)
  refine hst he hk hub (by omega) ?_ e hi
  rw [clusterOf_eq hpre]
  simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]
  exact hc

/-- **A tensor store's source reads finish before its lane's exit**: the lane's later
`wait_group.read` observes their completion and guards its exit. -/
theorem store_reads_finished (hX : Consistent L kernel asms mem0 X) (ho : OutputFacts L X)
    {g k a : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue (g, k) a s)
    (hx : CtaExited L X (ctaOf L g)) :
    SharedFinished L kernel asms X (.async (g, k) .readsDone) (ctaOf L g) := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, st, -, -, -, -, -, hwaits⟩ := ho.store_tma hg he
  obtain ⟨pcx, hl⟩ := hx g hg rfl
  have hlast : (X.tr g)[(X.tr g).length - 1]? = some ⟨pcx, .exit⟩ := by
    rw [List.getLast?_eq_getElem?] at hl; exact hl
  have hkl : k < (X.tr g).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1
  have hkx : k < (X.tr g).length - 1 := by
    rcases Nat.lt_or_ge k ((X.tr g).length - 1) with h | h
    · exact h
    · have heq : k = (X.tr g).length - 1 := by omega
      have he' : (X.tr g)[k]? = _ := he
      rw [heq, hlast] at he'
      cases he'
  obtain ⟨w, -, hwx, hwait, -⟩ := hwaits _ pcx hkx (.inl hlast)
  have hq : Part.readsDone ∈ GroupWaitStages X (g, k) (.bulk .read) := by
    simp [GroupWaitStages, he]
  have hpres : X.AsyncPresent (g, k) .readsDone :=
    Step.BulkWait.stages_of_returned hX hwait (by simp only; omega) _ hq
  obtain ⟨pcw, n, hgw, -⟩ := id hwait
  exact SharedFinished.of_observer_exit (finish := (g, (X.tr g).length - 1)) hpres
    (Step.BulkWait.witness_of_waitsFor hwait hq hpres)
    (Resumes.of_blocking hgw (b := false) rfl ⟨rfl, hwx, show _ < (X.tr g).length by omega⟩)
    ⟨hg, rfl, pcx, hlast⟩

/-- A thread instruction other than an exit, of a CTA, is finished once that CTA exited; one of
another CTA of the pair by the premise. -/
theorem thread_finished (hX : Consistent L kernel asms mem0 X) (hpeer : PeerThreadFinished L X)
    {i : EvId} {c : Nat} (hu : SharedUse L X (.thread i) c) {ev : Event} (he : X.get i = some ev)
    (hne : ∀ pc, ev ≠ ⟨pc, .exit⟩) (hx : CtaExited L X c) :
    SharedFinished L kernel asms X (.thread i) c := by
  by_cases hown : c = ctaOf L i.1
  · exact SharedFinished.of_thread hX.outside he hne hown.symm hx
  · exact hpeer i c hu hown hx

/-- The record an object action describes. -/
def actionRecord (e : Ref) (act : Action) : Record Ref :=
  { id := e, action := act, reply := { state := none }, fault := none }

/-! ### The table -/

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (hr : RingFacts L X)
    (hcp : RingCopies P L X) (htm : TmemFacts L X) (hs : ScoreFacts L X) (ho : OutputFacts L X)
    (hcf : ClusterFacts L X) (ha : AsyncFacts P L X) (hst : PeersStarted L X)
    (hpeer : PeerThreadFinished L X) (hcopy : CopyFinished L X) (hmma : MmaFinished L X)
include hpre hX hr hcp htm hs ho hcf ha hst hpeer hcopy hmma

/-- **Every use of a CTA's shared memory is safe**: a use of another CTA follows that CTA's start,
and a use of an exited CTA finished before one of its exits. -/
theorem use_ok (hcommit : CommitFinished L X) {e : Ref} {c : Nat} (huse : SharedUse L X e c) :
    (c ≠ ctaOf L e.issuer.1 → PeerSharedStarted L kernel asms X e c) ∧
      (CtaExited L X c → SharedFinished L kernel asms X e c) := by
  have pairOf : ∀ {i : EvId} {m : Loc}, X.UsesMbar i m → m.cta / 2 = ctaOf L i.1 / 2 := by
    intro i m hu
    obtain ⟨b, c', rfl, hc'⟩ := ha.mbar_pair hu
    exact hc'
  have hu0 := huse
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i, s, rfl, hc, hgrp⟩ | ⟨i, address, s, x, y, k, rfl, hi, hsl, hcta⟩ |
      ⟨i, address, s, rfl, hi, hcta⟩ | ⟨i, p, rfl, hfin, hsu⟩
  · -- an access of the owner's shared memory
    rcases e with ⟨g, k⟩ | ⟨i, p⟩
    · have hown : c = ctaOf L g := hcta ▸ ha.access_own hint hsp
      exact ⟨fun h => absurd hown h, fun hx => SharedFinished.of_access hX.outside hint
        hown.symm hx⟩
    · cases p with
      | mmaRead isB idx =>
        obtain ⟨-, -, hfp⟩ := hint
        rcases hfp with ⟨d, sp, acc, mask, hmi, hbl⟩ | ⟨c', k', cta, hcpi, -⟩
        · have hlh := TcMma.OperandSpec.byteLoc_cta hbl
          rw [hcta] at hlh
          obtain ⟨pc, hget⟩ := hmi
          obtain ⟨h1, h2⟩ := ha.mma_pair ⟨pc, hget⟩
          refine ⟨fun _ => started_of (e := .async i (.mmaRead isB idx)) hpre hX hst hget
            (by simp [PreKind]) (by simp) (by rcases hlh with rfl | rfl <;> assumption),
            fun hx => ?_⟩
          have hf := hmma i d sp acc mask c ⟨pc, hget⟩ hlh hx
          exact SharedFinished.of_stage (j := i) (q := .mmaDone) hpres
            (.inr ⟨rfl, rfl, rfl, hpres, hf.1⟩) hf
        · exact (hs.no_cp _ _ hcpi).elim
      | readStore x y k =>
        obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
        have hb := ha.store_base hti
        simp only [TensorStore.readLoc, Option.map_eq_some_iff] at hl
        obtain ⟨slot, -, hl⟩ := hl
        have hown : c = ctaOf L i.1 := by rw [← hcta, ← hl, ← hb]; rfl
        refine ⟨fun h => absurd hown h, fun hx => ?_⟩
        obtain ⟨g, j⟩ := i
        rw [hown] at hx ⊢
        have hf := store_reads_finished hX ho hti hx
        exact SharedFinished.of_stage (j := (g, j)) (q := .readsDone) hpres
          (.inr ⟨rfl, rfl, rfl, hpres, hf.1⟩) hf
      | readLoad x y k =>
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [Execution.tensor_readLoc_global hl] at hsp
        cases hsp
      | readPrefetch x y k =>
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [TensorTransfer.sourceLoc_global hl] at hsp
        cases hsp
      | readCopy =>
        obtain ⟨-, ⟨s, ⟨pc, hget⟩, -⟩ | ⟨pc, hget⟩⟩ := hint
        · exact (htm.no_bulk hget).elim
        · exact (htm.no_prefetch hget).elim
      | writeStore x y k =>
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [Execution.store_writeLoc_global hl] at hsp
        cases hsp
      | oldStore x y k =>
        obtain ⟨-, sp, addr, -, -, hl, -⟩ := hint
        rw [Execution.store_writeLoc_global hl] at hsp
        cases hsp
      | writeLoad x y k =>
        obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
        obtain ⟨pc, hget⟩ := hti
        obtain ⟨g, j⟩ := i
        obtain ⟨b, -, -, hsp'⟩ := load_source hX hr hcp ha hget
        simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hl
        obtain ⟨slot, hslot, hl⟩ := hl
        have hloc : (sp.sharedLoc slot).cta = sp.sharedBase.cta := rfl
        have hown : c = ctaOf L g := by
          rw [← hcta, ← hl, hloc, hsp']
          rfl
        refine ⟨fun h => absurd hown h, fun hx => ?_⟩
        have hb : sp.sharedBase.cta = c := by rw [hsp', hown]; rfl
        rw [← hb] at hx ⊢
        exact (hcopy _ _ _ ⟨pc, hget⟩).1 x y k (by simp [hslot]) hx
      | writeCta c' =>
        obtain ⟨-, s, tg, ⟨pc, hget⟩, -⟩ := hint
        exact (htm.no_clc hget).elim
      | writeCopy =>
        obtain ⟨-, s, ⟨pc, hget⟩, -⟩ := hint
        exact (htm.no_bulk hget).elim
      | writeElem j =>
        obtain ⟨-, s, ⟨pc, hget⟩, -⟩ := hint
        exact (htm.no_bulk hget).elim
      | oldElem j =>
        obtain ⟨-, s, r, ⟨pc, hget⟩, -⟩ := hint
        exact (htm.no_bulk hget).elim
      | _ => exact hint.2.elim
  · -- an action on a barrier of the owner
    have hsrc := objectAction_source (r := actionRecord e act) hact
    simp only [actionRecord] at hsrc
    cases hsrc with
    | @init g j pc n hid he ha' =>
      subst hid
      obtain ⟨b, hm, -⟩ := hcf.init_site (Frame.lt_of_get hX he) he
      have hown : c = ctaOf L g := congrArg Loc.cta hm
      exact ⟨fun h => absurd hown h,
        fun hx => SharedFinished.of_thread hX.outside he (fun _ h => by cases h) hown.symm hx⟩
    | inval hid he _ => exact (htm.no_inval he).elim
    | @arrive g j pc tx n rel sc hid he ha' =>
      subst hid
      have hc' : c / 2 = ctaOf L g / 2 := pairOf (.inl ⟨tx, n, rel, sc, pc, he⟩)
      exact ⟨fun _ => started_of (e := .thread (g, j)) hpre hX hst he (by simp [PreKind])
        (by simp) hc',
        fun hx => thread_finished hX hpeer hu0 he (fun _ h => by cases h) hx⟩
    | @wait g j pc q ok acq sc hid he ha' =>
      subst hid
      have hc' : c / 2 = ctaOf L g / 2 :=
        pairOf (.inr (.inr (.inr (.inr (.inl ⟨pc, q, ok, acq, sc, he⟩)))))
      exact ⟨fun _ => started_of (e := .thread (g, j)) hpre hX hst he (by simp [PreKind])
        (by simp) hc',
        fun hx => thread_finished hX hpeer hu0 he (fun _ h => by cases h) hx⟩
    | @tensor i pc a sp hid he hm ha' =>
      subst hid
      obtain ⟨g, j⟩ := i
      obtain ⟨b, -, hmb, -⟩ := load_source hX hr hcp ha he
      have hc' : c / 2 = ctaOf L g / 2 := by
        have := congrArg Loc.cta (hm.symm.trans hmb)
        simp only [FBar.loc] at this
        rw [this, pairBase]
        omega
      have hcm : sp.mbar.cta = c := by rw [hm]
      refine ⟨fun _ => started_of (e := .async (g, j) (.notify .load)) hpre hX hst he
        (by simp [PreKind]) (by simp) hc', fun hx => ?_⟩
      rw [← hcm] at hx ⊢
      exact (hcopy _ _ _ ⟨pc, he⟩).2 hx
    | increment hid he _ => exact (htm.no_arriveOn he).elim
    | arriveOn hid he _ _ _ => exact (htm.no_arriveOn he).elim
    | bulk hid he _ _ _ => exact (htm.no_bulk he).elim
    | @commit i pc sp rank hid he htg ha' =>
      subst hid
      have hc' : c / 2 = ctaOf L i.1 / 2 :=
        pairOf (.inr (.inr (.inr (.inl ⟨sp, rank, ⟨pc, he⟩, htg⟩))))
      refine ⟨fun _ => started_of (e := .async i (.tcNotify rank)) hpre hX hst he
        (by simp [PreKind]) (by simp) hc', fun hx => ?_⟩
      exact hcommit i sp rank _ ⟨pc, he⟩ htg hx
    | clc hid he _ _ _ => exact (htm.no_clc he).elim
  · -- a commit's issue, in each CTA of its group
    obtain ⟨pc, he⟩ := hc
    obtain ⟨⟨-, -, h3⟩, -⟩ := hgrp
    have hc' : c / 2 = ctaOf L i.1 / 2 := by
      simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster] at h3
      exact h3.symm
    exact ⟨fun _ => started_of (e := .thread i) hpre hX hst he (by simp [PreKind]) (by simp) hc',
      fun hx => thread_finished hX hpeer hu0 he (fun _ h => by cases h) hx⟩
  · -- a tensor load's write, in its loader's CTA
    obtain ⟨g, j⟩ := i
    obtain ⟨pc, he⟩ := hi
    obtain ⟨b, -, -, hsp'⟩ := load_source hX hr hcp ha he
    have hown : c = ctaOf L g := by rw [← hcta, hsp']; rfl
    refine ⟨fun h => absurd hown h, fun hx => ?_⟩
    rw [← hcta] at hx ⊢
    exact (hcopy _ _ _ ⟨pc, he⟩).1 x y k hsl hx
  · -- a tensor store's source reads, in its lane's CTA
    obtain ⟨g, j⟩ := i
    have hown : c = ctaOf L g := by rw [← hcta]; exact ha.store_base hi
    refine ⟨fun h => absurd hown h, fun hx => ?_⟩
    rw [hown] at hx ⊢
    exact store_reads_finished hX ho hi hx
  · -- the final stage of an operation
    rcases hfin with ⟨s, m, ⟨pc, hget⟩, -, rfl⟩ | ⟨s, ⟨pc, hget⟩, -, rfl⟩ |
        ⟨m, noinc, ⟨pc, hget⟩, rfl⟩ | ⟨-, rfl⟩ | ⟨s, tg, c', ⟨pc, hget⟩, -, rfl⟩ |
        ⟨a, s, -, rfl⟩ | ⟨a, s, -, rfl⟩ | ⟨s, rank, m, -, -, rfl⟩
    · exact (htm.no_bulk hget).elim
    · exact (htm.no_bulk hget).elim
    · exact (htm.no_arriveOn hget).elim
    · -- an MMA's completion, in each CTA of its operands
      rcases hsu with ⟨d, s, acc, mask, ⟨pc, he⟩, hlh⟩ | ⟨cp, hcpi, -⟩
      · obtain ⟨h1, h2⟩ := ha.mma_pair ⟨pc, he⟩
        exact ⟨fun _ => started_of (e := .async i .mmaDone) hpre hX hst he (by simp [PreKind])
          (by simp) (by rcases hlh with rfl | rfl <;> assumption),
          fun hx => hmma i d s acc mask c ⟨pc, he⟩ hlh hx⟩
      · exact (hs.no_cp _ _ hcpi).elim
    · exact (htm.no_clc hget).elim
    · -- a tensor load's completion, on the pair's even CTA
      obtain ⟨address, s, ⟨pc, he⟩, -, hcta⟩ := hsu
      obtain ⟨g, j⟩ := i
      obtain ⟨b, -, hmb, -⟩ := load_source hX hr hcp ha he
      have hc' : c / 2 = ctaOf L g / 2 := by
        rw [← hcta, hmb]
        simp only [FBar.loc, pairBase]
        omega
      refine ⟨fun _ => started_of (e := .async (g, j) (.notify .load)) hpre hX hst he
        (by simp [PreKind]) (by simp) hc', fun hx => ?_⟩
      rw [← hcta] at hx ⊢
      exact (hcopy _ _ _ ⟨pc, he⟩).2 hx
    · exact hsu.elim
    · -- a commit's arrive-on, at its target's CTA
      obtain ⟨s, m, ⟨pc, he⟩, htg, hcta⟩ := hsu
      have hc' : c / 2 = ctaOf L i.1 / 2 := by
        rw [← hcta]
        exact pairOf (.inr (.inr (.inr (.inl ⟨s, rank, ⟨pc, he⟩, htg⟩))))
      refine ⟨fun _ => started_of (e := .async i (.tcNotify rank)) hpre hX hst he
        (by simp [PreKind]) (by simp) hc', fun hx => ?_⟩
      rw [← hcta] at hx ⊢
      exact hcommit i s rank m ⟨pc, he⟩ htg hx

/-- **No use of a CTA's shared memory is unsafe.** -/
theorem no_sharedLifetimeUnsafe (hcommit : CommitFinished L X) :
    ¬ SharedLifetimeUnsafe L kernel asms X := by
  rintro ⟨e, owner, huse, ⟨h1, h2⟩ | ⟨h3, h4⟩⟩
  · exact h2 ((use_ok hpre hX hr hcp htm hs ho hcf ha hst hpeer hcopy hmma hcommit huse).1 h1)
  · exact h4 ((use_ok hpre hX hr hcp htm hs ho hcf ha hst hpeer hcopy hmma hcommit huse).2 h3)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
