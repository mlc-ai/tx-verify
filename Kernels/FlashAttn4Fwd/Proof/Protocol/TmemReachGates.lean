-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemReach
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OtherFaultFree

@[expose] public section

/-! # The gates of the P-ready, S-full and O-full objects

The reuse paths of `TmemReach` end at the counted arrivals and notifications of the P-ready,
second P-ready, S-full and O-full objects (those with a fault-free record), as the handoffs need.
Fault freedom needs them at every arrival and every recorded notification
(`Faults.PReadyGated`, `P2Gated`, `SFullGated`, `OFullGated`): an arrival that would fault is
not counted. The paths are the same: their construction (`stepP`, `stepP2`, `stepS`, `stepO`)
uses the arrival's event, its use and the notification's record, not that the record is
fault-free. Here they are restated at those events (`arriveP`, `arriveP2`, `notifyS`, `notifyO`),
with the induction hypothesis at every node (`ih_all`, from `reach_all`), and give the gates
through a poller of the object: lane 0 of the leader's MMA warp for the P-ready objects, the
first thread of the stage's softmax warps for an S-full object, the first correction thread for
an O-full object. So `Safety.OtherFaultFree` follows from the reuse context
(`Faults.otherFaultFree_of_route`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- The induction hypothesis holds at every node. -/
theorem ih_all (H : RouteCtx P L mem0 K A X) (n : Ref × Bool) : IH L K X n :=
  fun p hp _ => reach_all H p hp

set_option maxRecDepth 20000 in
/-- **The reuse paths of a P-ready arrival**: each MMA lane's polls for the uses before an
arrival's use precede it. -/
theorem arriveP (H : RouteCtx P L mem0 K A X) {c st p i pc : Nat} {sc : MbarScope}
    (hst : st < 2) (hga : X.get (p, i) = some ⟨pc, .arrive (pReadyBar L c st) 0 1 true sc⟩)
    {h0 : Nat} (hh0 : mmaIn L c h0) {j : Nat}
    (hj : j < arrivals (pReadyBar L c st) ((X.tr p).take i)) :
    Relation.TransGen (DepStep L K X)
      (.thread (h0, MbarRing.Poll.nth X (pReadyBar L c st) h0 j), true)
      (.thread (p, i), false) := by
  have hX := H.cons
  have ih := ih_all H (.thread (p, i), false)
  obtain ⟨s, harr⟩ : ∃ s, arrivals (pReadyBar L c st) ((X.tr p).take i) = s := ⟨_, rfl⟩
  rw [harr] at hj
  have hgp : p < L.threads := event_thread_lt hX hga
  have hlen : i < (X.tr p).length := len_of_get hga
  obtain ⟨hl, hrole, -⟩ := H.pf.p_arrive (g := p) (i := i) hgp hst hga
  rcases hrole with ⟨hw, hws⟩ | ⟨h8, h12⟩
  · -- a softmax arrival of tile `s`
    have hsp := H.rt.soft_p (g := p) (i := i) hgp hw (by rw [hl, hws]; exact hga)
    unfold pArr at hsp
    rw [hl, hws, harr] at hsp
    exact (soft_reach H ih hst hh0 hgp hw hws hl hlen (by omega) .refl).1
  · -- a correction arrival of credit `s`
    obtain ⟨-, hq⟩ := H.rt.corr_p (h := p) (i := i) hgp h8 h12 hst (arrive_lead hl hga)
    have hpa : pArr L X p st i = s := by unfold pArr; rw [hl]; exact harr
    rw [hpa] at hq
    rcases hq with hq | ⟨y, pcy, hyi, hyget, hG⟩ | ⟨jo, pco, po, acq, sco, hjo, hoget, hq⟩
    · omega
    · -- a rescale: the statistics partner's arrival follows `s + 1` S-full polls
      have hpass : y + 1 < (X.tr p).length := by omega
      obtain ⟨hgl, hgc, hgw, a, pc', cnt, md, ha, hord⟩ :=
        soft_partner H hgp h8 h12 hst hyget hpass
      have hren := stats_rendezvous H hgp h8 h12 hst hgl hgc hyget hpass ha hord
      have hw' : warpOf L (partnerLane L p st) < 8 := by omega
      obtain ⟨e, hea, hge⟩ := H.rt.soft_gen hgl hw' ha (by unfold statsId; omega)
      have hws : warpOf L (partnerLane L p st) / 4 = st := by omega
      rw [hord, hws] at hge
      have hmono := MbarRing.Poll.okPolls_mono
        (sFullBar L (ctaOf L (partnerLane L p st)) st) (X.tr (partnerLane L p st)) hea.le
      exact (soft_reach H ih hst hh0 hgl hw' hws (by rw [hgc, hl]) (len_of_get ha)
        (show j + 2 ≤ okPolls _ ((X.tr _).take a) by unfold sPolls at hge; omega)
        (rendezvous_path hyget hren hyi hlen).to_reflTransGen).1
    · -- a final pass: the O-full poll observes the commit of the item
      set I := okPolls (oFullBar L (ctaOf L p) st) ((X.tr p).take jo)
      have hI1 := MbarRing.Poll.okPoll_get hoget
      have hI : I + 1 ≤ okPolls (oFullBar L (ctaOf L p) st) ((X.tr p).take i) :=
        le_trans hI1.ge (MbarRing.Poll.okPolls_mono _ _ hjo)
      have hpath := Relation.TransGen.single (poll_guard H hlen hI)
      obtain ⟨y, pc, sp, rank, hy, hm, hcnt, hlead, hr, hobs⟩ :=
        contentO H ih hgp h8 h12 hst (poll_lt hlen.le hI) hpath
      obtain ⟨hY, hY12, hYl, k, pck, inst, l, hk, hel, -, hO⟩ :=
        H.rt.mma_commit ⟨pc, hy⟩ hst (.inr hm)
      have hO' := hO hm
      change kvTiles L * (OAcc.oCommits L X y.1 st y.2 + 1) ≤ _ at hO'
      rw [hcnt] at hO'
      obtain ⟨hh0', rfl, hh12⟩ := hh0
      obtain ⟨eh, hehl, hp1, -, hlane⟩ := lane_to_commit H hY hY12 hel hk (len_of_get hy) hh0'
        hh12 (by rw [← hYl, hlead, hl]) hst
      have htail := hlane.trans (((Relation.TransGen.single
        (commit_notify (K := K) hy hr)).tail (DepStep.of_witness L hobs)).trans hpath)
      exact .head (poll_guard H hehl
        (show j + 1 ≤ pPolls L X h0 st eh by omega)) htail

set_option maxRecDepth 20000 in
/-- **The reuse paths of a second P-ready arrival.** -/
theorem arriveP2 (H : RouteCtx P L mem0 K A X) {c st p i pc : Nat} {sc : MbarScope}
    (hst : st < 2) (hga : X.get (p, i) = some ⟨pc, .arrive (pReady2Bar L c st) 0 1 true sc⟩)
    {h0 : Nat} (hh0 : mmaIn L c h0) {j : Nat}
    (hj : j < arrivals (pReady2Bar L c st) ((X.tr p).take i)) :
    Relation.TransGen (DepStep L K X)
      (.thread (h0, MbarRing.Poll.nth X (pReady2Bar L c st) h0 j), true)
      (.thread (p, i), false) := by
  have hX := H.cons
  have hgp : p < L.threads := event_thread_lt hX hga
  have hlen : i < (X.tr p).length := len_of_get hga
  obtain ⟨hl, hw, hws, -, -, -, -, hcnt, -⟩ := H.p2.p2_arrive (g := p) (k := i) hgp hst hga
  exact (soft_reach H (ih_all H _) hst hh0 hgp hw hws hl hlen
    (show j + 2 ≤ sPolls L X p st i by omega) .refl).2

set_option maxRecDepth 20000 in
/-- **The reuse paths of an S-full notification**: each softmax thread's polls of its stage's
S-full object for the uses before a recorded notification's use precede it. -/
theorem notifyS (H : RouteCtx P L mem0 K A X) {h : Nat} (hh : h < L.threads)
    (hw : warpOf L h < 8) {y : EvId} {rank : Fin 16} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects (sFullBar L (ctaOf L h) (warpOf L h / 4)))
    (hid : r.id = .async y (.tcNotify rank)) {j : Nat}
    (hj : j < sCommits L X y.1 (warpOf L h / 4) y.2) :
    Relation.TransGen (DepStep L K X)
      (.thread (h, MbarRing.Poll.nth X (sFullBar L (ctaOf L h) (warpOf L h / 4)) h j), true)
      (.async y (.tcNotify rank), false) := by
  have hX := H.cons
  have ih := ih_all H (.async y (.tcNotify rank), false)
  have hst : warpOf L h / 4 < 2 := by omega
  obtain ⟨pc, sp, hy, ht, hrank⟩ := notify_rec hX hr hid
  have hm := (H.scom hst ⟨pc, hy⟩ ⟨pc, hy⟩ ht ht rfl).1
  have hlead := commit_lead H hy (.inl ht)
  obtain ⟨hY, hY12, hYl, k, -, -, -, hk, -, hS, -⟩ := H.rt.mma_commit ⟨pc, hy⟩ hst (.inl hm)
  have hP := (hS hm).1
  have hpy : j + 1 ≤ okPolls (pReadyBar L (ctaOf L y.1) (warpOf L h / 4))
      ((X.tr y.1).take y.2) :=
    le_trans (show j + 1 ≤ pPolls L X y.1 (warpOf L h / 4) k by omega)
      (MbarRing.Poll.okPolls_mono _ _ hk.le)
  have hpath := (Relation.TransGen.single (poll_guard H (len_of_get hy) hpy)).tail
    (commit_notify (K := K) hy hrank)
  have hcl : leadCta (ctaOf L h) = ctaOf L y.1 := hlead.symm.trans hYl
  obtain ⟨a, ha⟩ := pThread_of H.pre hYl ⟨hh, hcl, .inl ⟨hw, rfl⟩⟩
  obtain ⟨hS', hobs⟩ := contentP H ih hYl hst ⟨hY, rfl, hY12⟩ (poll_lt (len_of_get hy).le hpy)
    hpath a
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (pObj H.pre hX H.pf H.tm H.pinit hYl hst).S_rec hS'
  have e := unit_it_eq (X := X) (m := pReadyBar L (ctaOf L y.1) (warpOf L h / 4)) ha j
  change X.get (MbarRing.Unit.it _ _ _ a j) = _ at hga
  change arrivals _ ((X.tr (pThread _ _ _ a)).take (MbarRing.Unit.it _ _ _ a j).2) = j at harr
  rw [e] at hga harr hobs
  rw [← ha] at harr
  have hsp := H.rt.soft_p hh hw (arrive_lead hcl hga)
  unfold pArr at hsp
  rw [hcl, harr] at hsp
  have hg : j + 1 ≤ okPolls (sFullBar L (ctaOf L h) (warpOf L h / 4))
      ((X.tr h).take (nthEv X (arrivesOn (pReadyBar L (ctaOf L y.1) (warpOf L h / 4))) h j)) :=
    by unfold sPolls at hsp; omega
  exact .head (poll_guard H (len_of_get hga) hg)
    ((Relation.TransGen.single (DepStep.of_witness L hobs)).trans hpath)

set_option maxRecDepth 20000 in
/-- **The reuse paths of an O-full notification**: each correction thread's polls of stage `st`'s
O-full object for the uses before a recorded notification's use precede it. -/
theorem notifyO (H : RouteCtx P L mem0 K A X) {h st : Nat} (hh : h < L.threads)
    (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12) (hst : st < 2) {y : EvId} {rank : Fin 16}
    {r : MBarrier.Record Ref} (hr : r ∈ X.objects (oFullBar L (ctaOf L h) st))
    (hid : r.id = .async y (.tcNotify rank)) {j : Nat} (hj : j < OAcc.oCommits L X y.1 st y.2) :
    Relation.TransGen (DepStep L K X)
      (.thread (h, MbarRing.Poll.nth X (oFullBar L (ctaOf L h) st) h j), true)
      (.async y (.tcNotify rank), false) := by
  have hX := H.cons
  have ih := ih_all H (.async y (.tcNotify rank), false)
  obtain ⟨pc, sp, hy, ht, hrank⟩ := notify_rec hX hr hid
  have hm := (H.ocom hst ⟨pc, hy⟩ ⟨pc, hy⟩ ht ht rfl).1
  have hlead := commit_lead H hy (.inr ht)
  obtain ⟨hY, hY12, hYl, k, -, -, -, hk, -, -, hO⟩ := H.rt.mma_commit ⟨pc, hy⟩ hst (.inr hm)
  have hO' := hO hm
  have hn0 := kvTiles_pos H.pre
  have h1 : kvTiles L * (j + 1) ≤ kvTiles L * OAcc.oCommits L X y.1 st y.2 :=
    Nat.mul_le_mul_left _ hj
  change kvTiles L * (OAcc.oCommits L X y.1 st y.2 + 1) ≤ _ at hO'
  rw [Nat.mul_succ] at hO'
  have hpy : kvTiles L * (j + 1) + 1 ≤ okPolls (pReadyBar L (ctaOf L y.1) st)
      ((X.tr y.1).take y.2) :=
    le_trans (show kvTiles L * (j + 1) + 1 ≤ pPolls L X y.1 st k by omega)
      (MbarRing.Poll.okPolls_mono _ _ hk.le)
  have hpath := (Relation.TransGen.single (poll_guard H (len_of_get hy) hpy)).tail
    (commit_notify (K := K) hy hrank)
  have hcl : leadCta (ctaOf L h) = ctaOf L y.1 := hlead.symm.trans hYl
  obtain ⟨a, ha⟩ := pThread_of (st := st) H.pre hYl ⟨hh, hcl, .inr ⟨h8, h12⟩⟩
  obtain ⟨hS', hobs⟩ := contentP H ih hYl hst ⟨hY, rfl, hY12⟩ (poll_lt (len_of_get hy).le hpy)
    hpath a
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (pObj H.pre hX H.pf H.tm H.pinit hYl hst).S_rec hS'
  have e := unit_it_eq (X := X) (m := pReadyBar L (ctaOf L y.1) st) ha (kvTiles L * (j + 1))
  change X.get (MbarRing.Unit.it _ _ _ a _) = _ at hga
  change arrivals _ ((X.tr (pThread _ _ _ a)).take (MbarRing.Unit.it _ _ _ a _).2) = _ at harr
  rw [e] at hga harr hobs
  rw [← ha] at harr
  have hcp := (H.rt.corr_p hh h8 h12 hst (arrive_lead hcl hga)).1
  unfold pArr at hcp
  rw [hcl, harr] at hcp
  have hg : j + 1 ≤ okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take
      (nthEv X (arrivesOn (pReadyBar L (ctaOf L y.1) st)) h (kvTiles L * (j + 1)))) := by
    by_contra hlt
    have := Nat.mul_le_mul_left (kvTiles L)
      (show okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take
          (nthEv X (arrivesOn (pReadyBar L (ctaOf L y.1) st)) h (kvTiles L * (j + 1)))) + 1 ≤
        j + 1 by omega)
    omega
  exact .head (poll_guard H (len_of_get hga) hg)
    ((Relation.TransGen.single (DepStep.of_witness L hobs)).trans hpath)

/-- Lane 0 of the MMA warp of a launched CTA. -/
theorem mmaIn_lane0 (hpre : Pre P L mem0) {c : Nat} (hc : c < L.grid) :
    mmaIn L c (c * L.block + 384) := by
  have hb := hpre.block
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ctaOf, warpOf, Launch.threads, hb] <;> [nlinarith; omega;
    omega]

/-- The leader of a launched thread's pair is launched. -/
theorem lead_lt {g : Nat} (hg : g < L.threads) :
    leadCta (ctaOf L g) < L.grid := by
  have := cta_lt hg
  unfold leadCta
  omega

/-- **`PReadyGated`**. -/
theorem pReadyGated (H : RouteCtx P L mem0 K A X) : Faults.PReadyGated L K A X := by
  intro c st hc hst
  refine MbarRing.Unit.gated_of_paths (A := A) fun {a i pc sc} he hpos => ?_
  have hg := event_thread_lt H.cons he
  obtain ⟨hl, -⟩ := H.pf.p_arrive hg hst he
  refine ⟨c * L.block + 384, ?_⟩
  rw [Nat.add_zero]
  exact arriveP H hst he (mmaIn_lane0 H.pre (by rw [← hl]; exact lead_lt hg)) (by omega)

/-- **`P2Gated`**. -/
theorem p2Gated (H : RouteCtx P L mem0 K A X) : Faults.P2Gated L K A X := by
  intro c st hc hst
  refine MbarRing.Unit.gated_of_paths (A := A) fun {a i pc sc} he hpos => ?_
  have hg := event_thread_lt H.cons he
  obtain ⟨hl, -⟩ := H.p2.p2_arrive hg hst he
  refine ⟨c * L.block + 384, ?_⟩
  rw [Nat.add_zero]
  exact arriveP2 H hst he (mmaIn_lane0 H.pre (by rw [← hl]; exact lead_lt hg)) (by omega)

/-- A target of a commit of a launched thread is a barrier of a launched CTA. -/
theorem target_lt (H : RouteCtx P L mem0 K A X) {g i pc c off : Nat} {sp : TcCommit.Spec}
    {rank : Fin 16} (he : X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp rank = some ⟨.shared, c, L.sharedBase + off⟩) : c < L.grid := by
  have hg : g < L.threads := event_thread_lt H.cons he
  have hcl : c / 2 = ctaOf L g / 2 := H.ini.commit_cluster he ht
  have := cta_lt hg
  have hgr := H.pre.grid
  omega

/-- **`SFullGated`**. -/
theorem sFullGated (H : RouteCtx P L mem0 K A X) : Faults.SFullGated L K A X := by
  intro c st g hst
  refine MbarRing.Notify.gated_of_paths (A := A) fun {i pc sp rank} he hm ht ⟨r, hr, hid⟩ hpos => ?_
  have hc := target_lt H he ht
  have hb := H.pre.block
  obtain ⟨h, hdef⟩ : ∃ h, h = c * L.block + 128 * st := ⟨_, rfl⟩
  have hh : h < L.threads := by
    simp only [hdef, Launch.threads, hb]
    nlinarith
  have hcta : ctaOf L h = c := by simp only [hdef, ctaOf, hb]; omega
  have hw : warpOf L h = 4 * st := by simp only [hdef, warpOf, hb]; omega
  have hws : warpOf L h / 4 = st := by omega
  have hw8 : warpOf L h < 8 := by omega
  refine ⟨h, ?_⟩
  rw [Nat.add_zero]
  have hr' : r ∈ X.objects (sFullBar L (ctaOf L h) (warpOf L h / 4)) := by rw [hcta, hws]; exact hr
  have hpos' : 1 ≤ ((X.tr g).take i).countP (commitsTo (sFullBar L (ctaOf L g) st)) := hpos
  have := notifyS (y := (g, i)) H hh hw8 hr' hid
    (j := ((X.tr g).take i).countP (commitsTo (sFullBar L (ctaOf L g) st)) - 1)
    (by
      show _ < ((X.tr g).take i).countP (commitsTo (sFullBar L (ctaOf L g) (warpOf L h / 4)))
      rw [hws]
      omega)
  rwa [hcta, hws] at this

/-- **`OFullGated`**. -/
theorem oFullGated (H : RouteCtx P L mem0 K A X) : Faults.OFullGated L K A X := by
  intro c st g hst
  refine MbarRing.Notify.gated_of_paths (A := A) fun {i pc sp rank} he hm ht ⟨r, hr, hid⟩ hpos => ?_
  have hc := target_lt H he ht
  have hb := H.pre.block
  obtain ⟨h, hdef⟩ : ∃ h, h = c * L.block + 256 := ⟨_, rfl⟩
  have hh : h < L.threads := by
    simp only [hdef, Launch.threads, hb]
    nlinarith
  have hcta : ctaOf L h = c := by simp only [hdef, ctaOf, hb]; omega
  have hw : warpOf L h = 8 := by simp only [hdef, warpOf, hb]; omega
  have h8 : 8 ≤ warpOf L h := by omega
  have h12 : warpOf L h < 12 := by omega
  refine ⟨h, ?_⟩
  rw [Nat.add_zero]
  have hr' : r ∈ X.objects (oFullBar L (ctaOf L h) st) := by rw [hcta]; exact hr
  have hpos' : 1 ≤ ((X.tr g).take i).countP (commitsTo (oFullBar L (ctaOf L g) st)) := hpos
  have := notifyO (y := (g, i)) H hh h8 h12 hst hr' hid
    (j := ((X.tr g).take i).countP (commitsTo (oFullBar L (ctaOf L g) st)) - 1)
    (by
      show _ < ((X.tr g).take i).countP (commitsTo (oFullBar L (ctaOf L g) st))
      omega)
  rwa [hcta] at this

end Score

namespace Faults

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The other barriers' records are fault-free**, with the gates from the reuse paths. -/
theorem otherFaultFree_of_route (H : Score.RouteCtx P L mem0 kernel asms X)
    (hc : ClusterFacts L X) (ha : AsyncFacts P L X) (hout : OutputFacts L X)
    (hspare : SpareUnused L X) : Safety.OtherFaultFree L X :=
  otherFaultFree H.pre H.cons hc H.tm H.ini ha H.sf H.ofa H.pf H.p2 H.stf hout H.soft H.spin
    (Score.sFullGated H) (Score.oFullGated H) (Score.pReadyGated H) (Score.p2Gated H) hspare

end Faults

end
end PTX.Kernels.FlashAttn4Fwd.Proof
