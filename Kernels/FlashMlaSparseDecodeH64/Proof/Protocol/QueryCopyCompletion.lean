-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingObjects
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.Protocol.PairTmaRing.Hyp
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualMbarInit
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCommitOrigins
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxActualArrivals
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Lemmas.Flow.NotObject
import Lemmas.Protocol.MbarOneShot
import Lemmas.Protocol.BarTable
import Lemmas.Protocol.PairTmaRing.ItemFacts

public section

/-! # Query Tensor Memory copy completion -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopy
open PTX AsyncCopy MBarrier PTX.Flow MachineTracking

/-- The per-CTA barrier for completed query Tensor Memory copies. -/
abbrev object (L : Launch) (cta : Nat) : Loc :=
  ⟨.shared, cta, L.sharedBase + 222784⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {cta : Nat}

private abbrev Sound (P : Params) (L : Launch) : Prop :=
  ∀ g < L.threads, (Machine.code P L g).Sound

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

private theorem no_arrival (hs : Sound P L) {g i tx count : Nat} {rel : Bool} {sc : MbarScope}
    {e : Event} (he : X.get (g, i) = some e) (hk : e.kind = .arrive (object L cta) tx count rel sc)
    :
    False := by
  have hg := Frame.lt_of_get hX he
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
  · have hRange := dismissed_arrival_range hpre hX hs he hk hDismiss
    change L.sharedBase + 222872 ≤ L.sharedBase + 222784 ∧ _ at hRange
    omega
  obtain ⟨d, _, hState, hf⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine hDismiss he (by
      intro f hf
      rw [hk] at hf
      cases hf)
  clear hState
  have hsite := RingSourceSites.arrive_site hf hk
  have apart {loc : Loc} {bytes n : Nat} {release : Bool} {scope : MbarScope}
      (h : e.kind = .arrive loc bytes n release scope) : loc.addr = L.sharedBase + 222784 :=
    (congrArg Loc.addr (Kind.arrive.inj (h.symm.trans hk)).1)
  cases d
  case wg0 d =>
    rcases hsite with hd | hd | hd
    · have h := apart (RingEvents.lastStore_arrive hpre hd hf)
      change L.sharedBase + 222768 = L.sharedBase + 222784 at h
      omega
    · have h := apart (RingEvents.maskFree_arrive hpre hd hf)
      change L.sharedBase + (222872 + 8 * (d.block % 4)) = L.sharedBase + 222784 at h
      omega
    · have h := apart (RingEvents.scores_arrive hpre hd hf)
      change L.sharedBase + (222920 + 8 * (d.block % 2)) = L.sharedBase + 222784 at h
      omega
  case mma d =>
    have h := apart (RingEvents.query_expectTx hpre hsite hf)
    change L.sharedBase + 222776 = L.sharedBase + 222784 at h
    omega
  case tma d =>
    rcases hsite with hd | hd
    · have h := apart (RingEvents.rawReady_expectTx hpre hd hf)
      change L.sharedBase + (222808 + 8 * (d.block % 2)) = L.sharedBase + 222784 at h
      omega
    · have h := apart (RingEvents.validFree_arrive hpre hd hf)
      change L.sharedBase + (222872 + 8 * (d.block % 4)) = L.sharedBase + 222784 at h
      omega
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    have h := apart (RingEvents.validReady_arrive hpre hd hf)
    change L.sharedBase + (222840 + 8 * (d.block % 4)) = L.sharedBase + 222784 at h
    omega
  case wg2 d =>
    rcases hsite with hd | hd
    · have h := apart (RingEvents.dequantReady_arrive hpre hd hf)
      change L.sharedBase + (222792 + 8 * (d.block % 2)) = L.sharedBase + 222784 at h
      omega
    · have h := apart (RingEvents.rawFree_arrive hpre hd hf)
      change L.sharedBase + (222824 + 8 * (d.block % 2)) = L.sharedBase + 222784 at h
      omega
  all_goals exact hsite.elim

/-- The query-copy object receives Tensor Core arrivals and no transaction completions. -/
theorem actual_no_completion (hs : ∀ g < L.threads, (Machine.code P L g).Sound) {r : Record Ref}
    {n : Nat} (hr : r ∈ X.objects (object L cta)) (ha : r.action = .completeTx n) : False := by
  obtain ⟨⟨g, i⟩, e, addr, sp, _, he, hk, hm, _⟩ := object_completion_source hX hr ha
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, hf⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine
      (actual_tensor_issue_followed hpre hX hs he hk) he (by
        intro f hf
        rw [hk] at hf
        cases hf)
  rcases RingTensorEvents.issue_source hpre hf hk with hq | ⟨d, _, _, _, _, _, hraw, _⟩
  · have ho := congrArg Loc.addr (hm.symm.trans hq)
    change L.sharedBase + 222784 = L.sharedBase + 222776 at ho
    omega
  · have ho := congrArg Loc.addr (hm.symm.trans hraw)
    change L.sharedBase + 222784 = L.sharedBase + (222808 + 8 * (d.block % 2)) at ho
    omega

/-- The query-copy notification comes from the CTA's represented query-copy commit. -/
theorem actual_notify_source (hs : ∀ g < L.threads, (Machine.code P L g).Sound) {id : EvId}
    {tag : Nat} {sp : TcCommit.Spec} {rank : Fin 16} (he : X.get id = some ⟨tag, .tc (.commit sp)⟩)
    (hrank : TcCommit.target sp rank = some (object L cta)) :
    ctaOf L id.1 = cta ∧ ∃ d : Wg1Mma.D, d.site = .qCopyCommit ∧
      Frame.stateAt (Machine.code P L) X id.1 id.2 = some (some (.mma d)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hst, hf⟩ := actual_commit_fired hpre hX hs he rfl
  obtain ⟨_, q, rfl, ⟨hd, hm⟩ | ⟨_, hm⟩ | ⟨_, hm⟩⟩ :=
    RingCommitEvents.commit_source hpre hg hf rfl hrank
  · exact ⟨(congrArg Loc.cta hm).symm, q, hd, hst⟩
  · have ho := congrArg Loc.addr hm
    change L.sharedBase + 222784 = L.sharedBase + (222904 + 8 * (q.i % 2)) at ho
    omega
  · have ho := congrArg Loc.addr hm
    change L.sharedBase + 222784 = L.sharedBase + (222936 + 8 * (q.i % 2)) at ho
    omega

/-- The real initialization precedes every use of the query-copy notification object. -/
theorem actual_init_first (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    PairTmaRing.InitFirst X (object L cta) 1 := by
  let j : Fin 23 := 2
  obtain ⟨init, hInit⟩ := actual_init_sites hpre hX hs
  change PairTmaRing.InitFirst X (IndexRing.initTable.loc L cta j) (initCount j)
  apply IndexRing.published_init_first hX hInit cta j
  intro r hr hNotInit
  have use_before :
      ∃ a, X.MbInit a (IndexRing.initTable.loc L cta j) (initCount j) ∧
        baseCausality L X a r.id.issuer := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact (hNotInit _ ha).elim
    | @wait g i _ _ _ _ _ hid he _ =>
      obtain ⟨hc, a, hMb, hOrder⟩ := table_init_before_actual_poll hpre hX hs he rfl j
      change cta = ctaOf L g at hc
      rw [← hc] at hMb
      rw [hid]
      exact ⟨a, hMb, hOrder⟩
    | arrive _ he _ => exact (no_arrival hpre hX hs he rfl).elim
    | @commit id _ _ _ hid he htarget _ =>
      obtain ⟨g, i⟩ := id
      obtain ⟨hc, d, _, hState⟩ := actual_notify_source hpre hX hs he htarget
      obtain ⟨a, hMb, hOrder⟩ := completed_init_before_followed_role hpre hX hs he hState
        (by intro s h; cases h) j
      rw [hc] at hMb
      rw [hid]
      exact ⟨a, hMb, hOrder⟩
    | inval _ _ hAct => exact ((objects_single_lifetime hX _) r hr hAct).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
    | tensor _ _ _ hAct | bulk _ _ _ _ hAct | clc _ _ _ _ hAct =>
      exact (actual_no_completion hpre hX hs hr hAct).elim
  obtain ⟨a, hMb, hBefore⟩ := use_before
  have ha := (hInit j cta a _ _ trivial hMb.choose_spec).1
  rw [← ha]
  exact ⟨hMb, .inl hBefore⟩

omit hpre hX in
/-- Only Tensor Core notifications arrive on the query-copy object. -/
theorem actual_arrival_form (hX : Consistent L kernel Assumptions.all mem0 X)
    (hpre : Pre P L mem0) (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    {r : Record Ref} {n tx : Nat} (hr : r ∈ X.objects (object L cta))
    (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 0 ∧ ∃ issuer tag sp rank, r.id = .async issuer (.tcNotify rank) ∧
      X.get issuer = some ⟨tag, .tc (.commit sp)⟩ ∧
      TcCommit.target sp rank = some (object L cta) := by
  cases record_source hX.tma.2.2.1 hr with
  | commit hid he htarget ha' =>
    obtain ⟨rfl, rfl⟩ := Action.arrive.inj (ha.symm.trans ha')
    exact ⟨rfl, rfl, _, _, _, _, hid, he, htarget⟩
  | arrive _ he _ => exact (no_arrival hpre hX hs he rfl).elim
  | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | increment _ _ ha'
  | tensor _ _ _ ha' | bulk _ _ _ _ ha' | clc _ _ _ _ ha' =>
    rw [ha] at ha'
    cases ha'

omit hpre hX in
private theorem arrival_record (hX : Consistent L kernel Assumptions.all mem0 X)
    (hpre : Pre P L mem0) (hs : Sound P L)
    {r : Record Ref} {n tx : Nat} (hr : r ∈ X.objects (object L cta))
    (ha : r.action = .arrive n tx) :
    n = 1 ∧ ∃ issuer tag sp rank, r.id = .async issuer (.tcNotify rank) ∧
      X.get issuer = some ⟨tag, .tc (.commit sp)⟩ ∧
      TcCommit.target sp rank = some (object L cta) := by
  obtain ⟨hn, _, hw⟩ := actual_arrival_form hX hpre hs hr ha
  exact ⟨hn, hw⟩

/-- A successful query-copy barrier wait observes a real Tensor Core commit notification from
the same CTA. The observed logical phase is recovered from the checked object history. -/
theorem actual_observe_query_copy_commit (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    {g j tag : Nat} (he : X.get (g, j) = some ⟨tag, .wait (object L cta) 0 true true .cta⟩) :
    ∃ issuer c tag' sp rank d, X.get (issuer, c) = some ⟨tag', .tc (.commit sp)⟩ ∧
      ctaOf L issuer = cta ∧ d.site = Wg1Mma.Site.qCopyCommit ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      WaitObserves X (.async (issuer, c) (.tcNotify rank)) (g, j) (object L cta) true .cta := by
  classical
  let m := object L cta
  let log := X.objects m
  have hfirst : PairTmaRing.InitFirst X m 1 := actual_init_first hpre hX hs
  have hno : NoInval log := objects_single_lifetime hX m
  have hchecked : CheckedLog log := X.objects_checked hX m
  have hact : objectAction X X.async m (.thread (g, j)) = some (.pollParity 0 true) := by
    simp [objectAction, he, m]
  obtain ⟨k, w, hw, hwid, hwa⟩ := MbarOneShot.Hist.record_of_action hX hact
  have hwf := PairTmaRing.poll_clean hX hfirst hno w (List.mem_of_getElem? hw) ⟨_, _, hwa⟩
  have hwait := ((hX.tma.2.2.1 m).2.1 w (List.mem_of_getElem? hw)).2 0 true hwa hwf
  obtain ⟨st, parity, hst, hwp, hopp, hcompleted⟩ := hchecked.okPoll hw hwait
  obtain ⟨rfl, -⟩ := Action.pollParity.inj (hwp.symm.trans hwa)
  have hpos : 0 < st.phase := by omega
  have ho : observedAt log k = some (st.phase - 1) := by
    simp only [log, observedAt, hw, Option.bind_some, hcompleted, ite_eq_left hpos]
  have hu := hchecked.card_unit_arrivals_phase hno (n := 1) (q := st.phase - 1)
    (fun _ r cnt tx hr _ ha => (arrival_record hX hpre hs (List.mem_of_getElem? hr) ha).1)
    (fun _ _ _ h => PairTmaRing.expected_of_init hX hfirst hno h)
    (objects_no_pending_increment hX m)
    (List.getElem?_eq_some_iff.mp hw).1.le hst (by omega)
  have hcard : 0 < ((Finset.range log.length).filter (UnitArrivalIn log (st.phase - 1))).card := by
    rw [hu]
    decide
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hcard
  obtain ⟨r, tx, hr, hra, hrf, hrphase⟩ := (Finset.mem_filter.mp hl).2
  obtain ⟨_, ⟨issuer, c⟩, tag', sp, rank, hrid, he', htarget⟩ :=
    arrival_record hX hpre hs (List.mem_of_getElem? hr) hra
  obtain ⟨hc, d, hd, hdstate⟩ := actual_notify_source hpre hX hs he' htarget
  have hvis := MbarRing.Slot.updateBeforeWait_of_phase hchecked hno hr hrf hw hwf hwait hrphase ho
  rw [hrid, hwid] at hvis
  exact ⟨issuer, c, tag', sp, rank, d, he', hc, hd, hdstate, ⟨⟨tag, 0, he⟩, hvis⟩⟩

/-- The checked query-copy history also applies to tracked executions. -/
theorem no_completion (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) {r : Record Ref} {n : Nat}
    (hr : r ∈ X.objects (object L cta)) (ha : r.action = .completeTx n) : False :=
  actual_no_completion hpre hX (fun _ hg => Machine.code_sound hpre hg) hr ha

/-- The checked query-copy history also applies to tracked executions. -/
theorem notify_source (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) {id : EvId} {tag : Nat} {sp : TcCommit.Spec}
    {rank : Fin 16} (he : X.get id = some ⟨tag, .tc (.commit sp)⟩)
    (hrank : TcCommit.target sp rank = some (object L cta)) :
    ctaOf L id.1 = cta ∧ ∃ d : Wg1Mma.D, d.site = .qCopyCommit ∧
      Frame.stateAt (Machine.code P L) X id.1 id.2 = some (some (.mma d)) :=
  actual_notify_source hpre hX (fun _ hg => Machine.code_sound hpre hg) he hrank

/-- The checked query-copy history also applies to tracked executions. -/
theorem init_first (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) :
    PairTmaRing.InitFirst X (object L cta) 1 :=
  actual_init_first hpre hX (fun _ hg => Machine.code_sound hpre hg)

omit hpre hX in
/-- The checked query-copy history also applies to tracked executions. -/
theorem arrival_form (hX : Consistent L kernel Assumptions.all mem0 X)
    (hpre : Pre P L mem0) (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X)
    {r : Record Ref} {n tx : Nat} (hr : r ∈ X.objects (object L cta))
    (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 0 ∧ ∃ issuer tag sp rank, r.id = .async issuer (.tcNotify rank) ∧
      X.get issuer = some ⟨tag, .tc (.commit sp)⟩ ∧
      TcCommit.target sp rank = some (object L cta) :=
  actual_arrival_form hX hpre (fun _ hg => Machine.code_sound hpre hg) hr ha

/-- The checked query-copy history also applies to tracked executions. -/
theorem observe_query_copy_commit (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) {g j tag : Nat}
    (he : X.get (g, j) = some ⟨tag, .wait (object L cta) 0 true true .cta⟩) :
    ∃ issuer c tag' sp rank d, X.get (issuer, c) = some ⟨tag', .tc (.commit sp)⟩ ∧
      ctaOf L issuer = cta ∧ d.site = Wg1Mma.Site.qCopyCommit ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      WaitObserves X (.async (issuer, c) (.tcNotify rank)) (g, j) (object L cta) true .cta :=
  actual_observe_query_copy_commit hpre hX (fun _ hg => Machine.code_sound hpre hg) he
end

/-- An acquire on the query-copy barrier observes the read of each actual copy tracked by
its commit, at every operand byte covered by that copy. -/
theorem copy_read_finished (hX : Consistent L kernel Assumptions.all mem0 X)
    {g j issuer copy commit site index : Nat} {sp : TcCommit.Spec} {cp : TcCopy.Spec}
    {rank : Fin 16} (hcommit : X.get (issuer, commit) = some ⟨site, .tc (.commit sp)⟩)
    (hcopy : X.CpIssue (issuer, copy) cp) (hbefore : copy < commit)
    (hwait : WaitObserves X (.async (issuer, commit) (.tcNotify rank)) (g, j)
      (object L cta) true .cta)
    (hcta : ctaOf L issuer = ctaOf L g) :
    AsyncFinished L X (issuer, copy) (.mmaRead false index) (g, j) := by
  have hrecord := hwait.2
  obtain ⟨k, _, r, _, _, hr, hid, _, _⟩ := hrecord
  have ha := (hX.tma.2.2.1 (object L cta)).2.1 r (List.mem_of_getElem? hr)
  rw [hid] at ha
  have hdelivery : TcCommit.target sp rank = some (object L cta) ∧
      rank ∈ X.tcNotified (issuer, commit) := by
    by_contra hn
    simp [objectAction, hcommit, hn] at ha
  have htracks : TracksMma X (issuer, copy) (issuer, commit) :=
    ⟨rfl, hbefore, .inr (.inl ⟨cp, hcopy⟩), sp, site, hcommit⟩
  obtain ⟨_, _, hwget⟩ := hwait.1
  have hi := Frame.lt_of_get hX hcommit
  have hg := Frame.lt_of_get hX hwget
  exact .inr ⟨.cta, ⟨_, _, ⟨_, sp, rank, rfl, htracks, ⟨site, hcommit⟩,
    hdelivery.1, hdelivery.2⟩, hwait⟩,
    ⟨hi, hg, congrArg L.clusterOfCta hcta⟩, ⟨hg, hi, hcta.symm⟩⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopy
