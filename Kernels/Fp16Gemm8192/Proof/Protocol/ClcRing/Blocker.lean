-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.BlockLedger
public import Lemmas.Order.CausalThreadCount
public import Kernels.Fp16Gemm8192.Proof.Protocol.Elected

@[expose] public section

/-! # The blocker of a failed response poll

A reader `g` at its CLC poll, stopped at a failed poll of its CTA's response barrier, sits in the
barrier's phase `N`, its successful polls (`reader_phase`). The barrier's ledger has three branches
(`ledger_branches`): a request of the cluster is not delivered; the CTA's arrivals are at most `N`;
or the leader's requests are at most `N`. In the last two, every warp-10 thread of the CTA in
question (the reader's, or the leader CTA) has arrived on its response barrier at most `N` times
(`arrivals_le_records`, and `arrivals_le_issues` with `issues_le_producer`).

Such a CTA has a blocking warp-10 thread (`lane_blocker`): a lane with no election (before its
election, `sched_unelected`), or the warp's elected lane (`ElectOk`). The elected lane is a prologue
state, a scheduler outside its exit stage (time at most `blockAt N + 4`, `sched_time`), or stopped
without its exit (an exit would complete the reader's cluster arrivals, `ClusterExitAll`). It is not
in its exit stage: an elected scheduler there has polled `M > 0` responses and read the last one
claiming no CTA (`sched_exit`), with `M` its arrivals, at most `N`; the reader read the same
response after its own poll numbered `M - 1` (`AllResponsesAgree`), and a reader at its CLC poll
read every response it polled claiming a CTA (`exit_contra`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.ClcRing

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event of a thread is below its trace's length. -/
theorem get_lt {g j : Nat} {e : Event} (he : X.get (g, j) = some e) : j < (X.tr g).length := by
  have h : (X.tr g)[j]? = some e := he
  exact (List.getElem?_eq_some_iff.mp h).1

/-- A state at its CLC poll has made its first cluster arrival only. -/
theorem clPhase_of_clcWait {d : ThreadD} (h : d.AtClcWait) : d.clPhase = 1 := by
  rcases d with pd | (l | m | s | c)
  · exact h.elim
  · simp only [ThreadD.AtClcWait] at h
    simp [ThreadD.clPhase, h]
  · simp only [ThreadD.AtClcWait] at h
    simp [ThreadD.clPhase, h]
  · simp only [ThreadD.AtClcWait] at h
    simp [ThreadD.clPhase, h]
  · simp only [ThreadD.AtClcWait] at h
    simp [ThreadD.clPhase, h]

/-- An exit-stage scheduler is at one of its three exit sites. -/
theorem exit_site {sd : Scheduler.D} (h : Scheduler.exitOff sd ≠ none) :
    sd.site = .exitArrive ∨ sd.site = .exitWait ∨ sd.site = .exit := by
  obtain ⟨site, ap, cp, r, x⟩ := sd
  cases site <;> simp_all [Scheduler.exitOff]

/-- **A reader at its CLC poll read every response it polled claiming a CTA.** The poll is not the
reader's last event (a failed poll), so its read follows (`poll_read`); the read's bytes are a
response (`ReaderValues`), which claims a CTA by the reader's role fact. -/
theorem reader_claims (ht : ThreadFacts L X) (hv : ReaderValues L X)
    {g pc p : Nat} {acq : Bool} {sc : MbarScope} {dg : ThreadD} (hg : g < L.threads)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some dg)) (hdg : dg.AtClcWait)
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false
      acq sc⟩)
    {j pcj pj : Nat} {acqj : Bool} {scj : MbarScope}
    (hj : X.get (g, j) = some ⟨pcj, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pj true acqj
      scj⟩) :
    ∃ pcr src bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  have hjl : j + 1 < (X.tr g).length := by
    have hlt := get_lt hj
    have hne : j ≠ (X.tr g).length - 1 := by
      intro hjeq
      have h2 : (X.tr g)[(X.tr g).length - 1]? = some
          ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false acq sc⟩ := by
        rw [← List.getLast?_eq_getElem?]
        exact hlast
      have h3 : (X.tr g)[j]? = some
          ⟨pcj, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pj true acqj scj⟩ := hj
      rw [hjeq, h2] at h3
      simp at h3
    omega
  obtain ⟨pcr, src, bs, hrd, hfp⟩ := ht.poll_read hg hj hjl
  obtain ⟨-, -, -, r, -, -, -, -, -, -, hbytes⟩ := hv (g / L.block / 2) g j pcj pj acqj scj rfl hj
  have hrr : Flow.responseOf bs = some r := by
    rw [hbytes pcr src bs hrd hfp]
    exact responseOf_clc r
  refine ⟨pcr, src, bs, r, hrd, hfp, hrr, ?_⟩
  rcases dg with pd | (l | m | s | c)
  · exact hdg.elim
  · exact ht.loader_fail_wait hg hσg hdg j pcj pj acqj scj pcr src bs r hj hrd hfp hrr
  · exact ht.mma_fail_wait hg hσg hdg j pcj pj acqj scj pcr src bs r hj hrd hfp hrr
  · exact ht.sched_fail_wait hg hσg hdg j pcj pj acqj scj pcr src bs r hj hrd hfp hrr
  · exact ht.cons_fail_wait hg hσg hdg j pcj pj acqj scj pcr src bs r hj hrd hfp hrr

/-- **A thread's arrivals on a response barrier are arrival records of it.** Each arrival of the
thread is a record of the barrier (`object_thread_arrival_count_window`), a fault-free arrival
expecting the response's bytes (`full_src`, the ring's fault freedom). -/
theorem arrivals_le_records (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {i : Fin 2} (h : Nat) :
    arrivals ((slot L c).full i) (X.tr h) ≤ (X.objects ((slot L c).full i)).countP isArrival := by
  have hm := (slot L c).full_mem i
  have hwin := hX.object_thread_arrival_count_window (m := (slot L c).full i) (g := h)
    (k := (X.tr h).length) (X.objects ((slot L c).full i)) (fun _ hq => hq)
    (hX.tma.2.2.1 ((slot L c).full i)).1.1 (fun q j hq hid => ⟨fun _ => ?_, fun _ => hq⟩)
  · rw [List.take_length] at hwin
    change (X.tr h).countP (sourceArrive _) ≤ _
    rw [← hwin]
    refine List.countP_mono_left fun q hq hthr => ?_
    obtain ⟨-, c', t', hact⟩ := threadArrival_iff.mp hthr
    rw [isArrival_iff]
    refine ⟨?_, fault_free hpre hX ht hm q hq⟩
    cases full_src hX ht hq with
    | arrive _ _ ha => rw [ha]; rfl
    | init ha => rw [ha] at hact; cases hact
    | poll _ _ ha => rw [ha] at hact; cases hact
    | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
    | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
    | clc _ _ _ ha => rw [ha] at hact; cases hact
  · cases record_source hX.tma.2.2.1 hq with
    | inval _ he _ => exact (no_inval hX ht ⟨_, he⟩).elim
    | init hid' he => rw [hid] at hid'; cases hid'; exact get_lt he
    | arrive hid' he => rw [hid] at hid'; cases hid'; exact get_lt he
    | wait hid' he => rw [hid] at hid'; cases hid'; exact get_lt he
    | increment hid' he => rw [hid] at hid'; cases hid'; exact get_lt he
    | arriveOn hid' => rw [hid] at hid'; cases hid'
    | tensor hid' => rw [hid] at hid'; cases hid'
    | bulk hid' => rw [hid] at hid'; cases hid'
    | commit hid' => rw [hid] at hid'; cases hid'
    | clc hid' => rw [hid] at hid'; cases hid'

/-- **A leader scheduler arrives on its response barrier no more often than it requests.** Its last
arrival follows one more request than its earlier arrivals (`lead_arrive_after_issue`). -/
theorem arrivals_le_issues (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {h : Nat}
    (hh : h < L.threads)
    (hlead : h / L.block % 2 = 0) :
    arrivals (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) ≤
      (X.tr h).countP (clcIssuesTo (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩)) := by
  rcases Nat.eq_zero_or_pos (arrivals (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h)) with
    h0 | hpos
  · omega
  obtain ⟨k, e, hk, hpe, hcnt⟩ := MbarRing.Slot.exists_nth_countP
    (arrivesOn (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩)) (xs := X.tr h)
    (c := arrivals (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) - 1)
    (by unfold arrivals at hpos ⊢; omega)
  obtain ⟨pce, kind⟩ := e
  cases kind <;> simp [arrivesOn, sourceArrive] at hpe
  case arrive target tx n rel sc =>
    subst hpe
    have hget : X.get (h, k) = some ⟨pce, .arrive (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) tx n
        rel sc⟩ := hk
    obtain ⟨r, hσ, hrw⟩ := arrive_role hX ht hh hget (b := ⟨.clc, 0, true⟩) rfl Nat.one_pos
    rcases r with l | mm | sd | cs
    · simp only [roleWarp] at hrw
      exact absurd (ht.ring_event hh hget hσ |>.arrive ⟨.clc, 0, true⟩ _ _ _ _ _ rfl Nat.one_pos).1
        (by simp [Bar.arriveBy])
    · exact absurd (ht.ring_event hh hget hσ |>.arrive ⟨.clc, 0, true⟩ _ _ _ _ _ rfl Nat.one_pos).1
        (by simp [Bar.arriveBy])
    · have hl := ht.lead_arrive_after_issue hh hget hσ (by simp [Loader.leader, hlead]) rfl
      have hmono : ((X.tr h).take k).countP
            (clcIssuesTo (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩)) ≤
          (X.tr h).countP (clcIssuesTo (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩)) :=
        (List.take_sublist _ _).countP_le
      unfold arrivals at hl hcnt ⊢
      omega
    · exact absurd (ht.ring_event hh hget hσ |>.arrive ⟨.clc, 0, true⟩ _ _ _ _ _ rfl Nat.one_pos).1
        (by simp [Bar.arriveBy])

/-- **A warp-10 thread of the leader CTA requests no more than the leader.** A thread with a request
is the leader (`issue_facts`, the request names the leader CTA by `clc_multicast`); one without has
none. -/
theorem issues_le_producer (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c h : Nat} (hcta : h / L.block = 2 * c) (hg2 : 2 * c < L.grid) :
    (X.tr h).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) ≤
      (X.tr (producer L X c)).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) := by
  by_cases hex : ∃ ki pc sp tg, X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩
  · obtain ⟨ki, pc, sp, tg, he⟩ := hex
    have hin := ht.clc_multicast h ki pc sp tg he (2 * c) hg2 (by omega)
    obtain ⟨hp, -⟩ := issue_facts (c := c) hpre hX ht he hin (by omega)
    rw [hp]
  · have h0 : (X.tr h).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) = 0 := by
      rw [List.countP_eq_zero]
      intro e he hce
      obtain ⟨ki, hki⟩ := List.mem_iff_getElem?.mp he
      obtain ⟨pce, kind⟩ := e
      cases kind <;> simp [clcIssuesTo] at hce
      case clcIssue sp tg => exact hex ⟨ki, pce, sp, tg, hki⟩
    omega

/-- **An elected scheduler in its exit stage contradicts a reader's poll.** It polled `M > 0`
responses and read the last claiming no CTA (`sched_exit`); the reader, with at least `M` polls,
read the same response after its poll numbered `M - 1` (`AllResponsesAgree`), claiming a CTA. -/
theorem exit_contra (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {g h : Nat}
    (hh : h < L.threads) (hcl : h / L.block / 2 = g / L.block / 2)
    (hclaim : ∀ j pcj pj acqj scj,
      X.get (g, j) = some ⟨pcj, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pj true acqj scj⟩ →
      ∃ pcr src bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr)
    {sd : Scheduler.D}
    (hσh : Frame.stateAt (code L) X h (X.tr h).length = some (some (.inr (.sched sd))))
    (hex : Scheduler.exitOff sd ≠ none)
    (hpos : 0 < okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h))
    (hle : okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) ≤
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) : False := by
  obtain ⟨j, pcj, pj, acqj, scj, pcr, src, bs, rr, hcnt, hw, hr, hfp, hrr, hnc⟩ :=
    ht.sched_exit hh hσh (exit_site hex) hpos
  obtain ⟨w, pcw, pw, acqw, scw, -, hwev, hwo⟩ := nth_poll (X := X) (g := g)
    (j := (X.tr g).length) (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
    (o := okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) - 1)
    (by rw [List.take_length]; omega)
  obtain ⟨pcr', src', bs', rr', hr', hfp', hrr', hcl'⟩ := hclaim w pcw pw acqw scw hwev
  have hbs := hag (g / L.block / 2) g h w j pcw pcj pw pj pcr' pcr acqw acqj scw scj src' src bs' bs
    rfl hcl hwev hw (by rw [hwo]; omega) hr' hfp' hr hfp
  subst hbs
  rw [hrr] at hrr'
  cases hrr'
  exact hnc hcl'

/-- **A CTA of the reader's cluster whose warp-10 threads have arrived at most `N` times blocks the
reader.** A warp-10 lane without an election is before it (time at most 58); otherwise the warp's
elected lane is a prologue state, a scheduler outside its exit stage (`sched_time`), or stopped
without its exit (`ClusterExitAll`, the reader's single cluster arrival); in its exit stage it would
contradict the reader (`exit_contra`). -/
theorem lane_blocker (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hag : AllResponsesAgree L X)
    (hce : ClusterExitAll L X) {g pc p : Nat} {acq : Bool} {sc : MbarScope} {dg : ThreadD}
    (hg : g < L.threads) (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some dg))
    (hdg : dg.AtClcWait)
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false
      acq sc⟩)
    (hclaim : ∀ j pcj pj acqj scj,
      X.get (g, j) = some ⟨pcj, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pj true acqj scj⟩ →
      ∃ pcr src bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr)
    {cta : Nat} (hcta : cta < L.grid) (hcc : cta / 2 = g / L.block / 2)
    (hB : ∀ h, h < L.threads → h / L.block = cta → h % L.block / 32 = 10 →
      arrivals (Bar.loc L cta ⟨.clc, 0, true⟩) (X.tr h) ≤
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) :
    ∃ h, h < L.threads ∧ h / L.block / 2 = g / L.block / 2 ∧ h % L.block / 32 = 10 ∧
      X.tr h ≠ [] ∧
      ((∃ d, Frame.stateAt (code L) X h (X.tr h).length = some (some d) ∧ d.exitOff = none ∧
          d.vtime L h (X.tr h) ≤
            blockAt (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) + 4) ∨
        (Frame.stateAt (code L) X h (X.tr h).length = none ∧ ∀ pc', (X.tr h).getLast? ≠
          some ⟨pc', .exit⟩)) := by
  have hblock := hpre.block
  have hgrid := hpre.grid
  -- the reader's last event fires from a role state: its cluster has started
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hget : X.get (g, ys.length) = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false acq sc⟩ := by
    have h1 : (X.tr g).length - 1 = ys.length := by
      rw [hys]
      simp
    change (X.tr g)[ys.length]? = _
    rw [← h1, ← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨r, hσr, -⟩ := wait_role hX ht hg hget rfl
  have hclu : ∀ h, h / L.block / 2 = g / L.block / 2 →
      L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) := by
    intro h hh'
    simp only [clusterOfCta_eq hpre]
    exact hh'
  have hstart : ∀ h, h < L.threads → h / L.block / 2 = g / L.block / 2 → X.tr h ≠ [] :=
    fun h hh hc => ht.cluster_started hg hget hσr hh (hclu h hc)
  have hcl1 : clArrives (X.tr g) = 1 := by
    rw [ht.cl_phase hg hσg]
    exact clPhase_of_clcWait hdg
  have hnoexit : ∀ h pc', h < L.threads → h / L.block / 2 = g / L.block / 2 →
      (X.tr h).getLast? ≠ some ⟨pc', .exit⟩ := by
    intro h pc' hh hc hl
    have h2 := hce h pc' hh hl g hg (hclu h hc).symm
    omega
  have hblk : 58 ≤ blockAt (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) + 4 := by
    unfold blockAt
    omega
  by_cases hno : ∃ h, h < L.threads ∧ h / L.block = cta ∧ h % L.block / 32 = 10 ∧
      ∀ j pc mask inst leader, ¬ X.Elect (h, j) pc mask inst leader
  · obtain ⟨h, hh, hhc, hhw, hnoel⟩ := hno
    obtain ⟨d, hσ, -, hex, hvt⟩ := ht.sched_unelected hh hhw hnoel
    have hcl : h / L.block / 2 = g / L.block / 2 := by rw [hhc]; exact hcc
    exact ⟨h, hh, hcl, hhw, hstart h hh hcl, .inl ⟨d, hσ, hex, by omega⟩⟩
  · -- the warp's first lane has an election, which names the warp's elected lane
    have hbt : cta * L.block + 320 < L.threads := by
      unfold Launch.threads
      rw [hblock]
      rw [hblock] at hno
      omega
    have hbc : (cta * L.block + 320) / L.block = cta := by
      rw [hblock]
      omega
    have hbw : (cta * L.block + 320) % L.block / 32 = 10 := by
      rw [hblock]
      omega
    obtain ⟨j0, pc0, mask, inst, leader, hev⟩ : ∃ j pc mask inst leader,
        X.Elect (cta * L.block + 320, j) pc mask inst leader := by
      by_contra hne
      push Not at hne
      exact hno ⟨_, hbt, hbc, hbw, hne⟩
    obtain ⟨h, j', hh, ⟨⟨-, -, hcta'⟩, hwarp⟩, hel'⟩ := elected_of_elect hpre hX hev
    have hhc : h / L.block = cta := by
      rw [← hcta', hbc]
    have hhw : h % L.block / 32 = 10 := by
      rw [← hwarp, hbw]
    have hcl : h / L.block / 2 = g / L.block / 2 := by rw [hhc]; exact hcc
    have helected : ∃ j pc mask inst, X.Elect (h, j) pc mask inst (laneOf L h) :=
      ⟨j', pc0, mask, inst, hel'⟩
    refine ⟨h, hh, hcl, hhw, hstart h hh hcl, ?_⟩
    match hs : Frame.stateAt (code L) X h (X.tr h).length with
    | none => exact .inr ⟨rfl, fun pc' hl => hnoexit h pc' hh hcl hl⟩
    | some none => exact absurd hs (ht.tracked h _ hh)
    | some (some (.inl pd)) =>
      refine .inl ⟨.inl pd, rfl, rfl, ?_⟩
      have := Prologue.site_vtime_le pd.site
      simp only [ThreadD.vtime]
      omega
    | some (some (.inr rr)) =>
      have hrw := ht.role_warp hh le_rfl hs
      rcases rr with l | mm | sd | cs
      · simp only [roleWarp] at hrw
        omega
      · simp only [roleWarp] at hrw
        omega
      · have harr := hB h hh hhc hhw
        rw [← hhc] at harr
        by_cases hx : Scheduler.exitOff sd = none
        · refine .inl ⟨_, rfl, hx, ?_⟩
          have hvt := ht.sched_time hh hs hx harr
          simp only [ThreadD.vtime, schedCount]
          exact hvt
        · exfalso
          have hpos := ht.sched_elected_exit hh helected hs hx
          have hsa := ht.sched_arrivals hh hs
          have hns : sd.site ≠ .clcWait := by
            rcases exit_site hx with h1 | h1 | h1 <;> rw [h1] <;> simp
          simp only [hns, ite_false, Nat.add_zero] at hsa
          exact exit_contra ht hag hh hcl hclaim hs hx hpos (by omega)
      · simp only [roleWarp] at hrw
        omega

/-- **The blocker of a failed response poll.** A reader `g` at its CLC poll, stopped at a failed
poll of its CTA's response barrier whose phase has the poll's parity, is blocked by an undelivered
request of the cluster, or by a warp-10 thread of the cluster that is outside its exit stage with
time at most `blockAt N + 4` (`N` the reader's successful polls), or stopped without its exit. The
barrier's phase is `N` (`reader_phase`); its ledger (`ledger_branches`) bounds the arrivals of the
reader's CTA's scheduler or the leader's requests by `N`, and `lane_blocker` gives the thread. -/
theorem clc_blocked_of (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X)
    (hag : AllResponsesAgree L X) (hce : ClusterExitAll L X)
    {g pc p : Nat} {acq : Bool} {sc : MbarScope} {before : MBarrier.State} {dg : ThreadD}
    (hg : g < L.threads) (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some dg))
    (hdg : dg.AtClcWait)
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p false
      acq sc⟩)
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).length = some before)
    (hpar : before.phase % 2 = p % 2) :
    (∃ i s tg, X.ClcIssue i s tg ∧ ¬ ∀ c ∈ tg, c ∈ (X.clc i).notified) ∨
      ∃ h, h < L.threads ∧ h / L.block / 2 = g / L.block / 2 ∧ h % L.block / 32 = 10 ∧
        X.tr h ≠ [] ∧
        ((∃ d, Frame.stateAt (code L) X h (X.tr h).length = some (some d) ∧ d.exitOff = none ∧
            d.vtime L h (X.tr h) ≤
              blockAt (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) + 4) ∨
          (Frame.stateAt (code L) X h (X.tr h).length = none ∧ ∀ pc', (X.tr h).getLast? ≠
            some ⟨pc', .exit⟩)) := by
  have hblock := hpre.block
  have hph := reader_phase hpre hX ht hag hg hlast hstate hpar
  have hclaim := fun j pcj pj acqj scj
      (hj : X.get (g, j) = some ⟨pcj, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pj true acqj
        scj⟩) => reader_claims ht hv hg hσg hdg hlast hj
  have hgcta : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  let i : Fin 2 := ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩
  have hi : 2 * (g / L.block / 2) + i.val < L.grid := by
    show 2 * (g / L.block / 2) + g / L.block % 2 < L.grid
    omega
  have hloc : (slot L (g / L.block / 2)).full i = Bar.loc L (g / L.block) ⟨.clc, 0, true⟩ := by
    show Bar.loc L (2 * (g / L.block / 2) + g / L.block % 2) _ = _
    congr 1
    omega
  have hstate' : stateBefore (X.objects ((slot L (g / L.block / 2)).full i))
      (X.objects ((slot L (g / L.block / 2)).full i)).length = some before := by
    rw [hloc]
    exact hstate
  rcases ledger_branches hpre hX ht (g / L.block / 2) ht.clc_multicast hi hstate' with
    hA | hU | hC
  · right
    refine lane_blocker hpre hX ht hag hce hg hσg hdg hlast hclaim hgcta rfl
      fun h _ _ _ => ?_
    have h1 := arrivals_le_records hpre hX ht (c := g / L.block / 2) (i := i) h
    rw [hloc] at h1 hA
    omega
  · exact .inl hU
  · right
    refine lane_blocker hpre hX ht hag hce hg hσg hdg hlast hclaim (cta := 2 * (g / L.block / 2))
      (by omega) (by omega) fun h hh hhc _ => ?_
    have h1 := arrivals_le_issues hX ht hh (by rw [hhc]; omega)
    have h2 := issues_le_producer hpre hX ht (c := g / L.block / 2) hhc (by omega)
    rw [hhc] at h1
    omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.ClcRing
