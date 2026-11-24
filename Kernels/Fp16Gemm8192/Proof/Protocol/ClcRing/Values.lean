-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Joint
public import Lemmas.Order.OrderNotAccess

@[expose] public section

/-! # The CLC responses by generation

Each response barrier completes one phase per response, and its completion before which `n`
completions precede is the notification of the leader's request numbered `n`
(`completion_ordinal`, `ordinal_eq`). A selected reader's poll with `n` earlier successful polls
observes the phase `n` (`sel_poll_phase`), whose completion is that request's notification
(`observed`). A selected consumer's acknowledgement of every generation before a request
synchronizes with the request (`ack_sync`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every record of a cluster's response and acknowledgement barriers is fault-free. -/
theorem fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {m : Loc} (hm : m ∈ (slot L c).objects) :
    ∀ q ∈ X.objects m, q.fault = none :=
  (clcFacts hpre hX ht).fault_free (i := c) hm

/-- Every completion on a response barrier is of 16 bytes. -/
theorem full_uniform (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {k : Fin 2} : ∀ q ∈ X.objects ((slot L c).full k), ∀ n, q.action = .completeTx n →
      q.fault = none → n = 16 := by
  intro q hq n ha _
  cases full_src hX ht hq with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive _ _ ha' => rw [ha] at ha'; cases ha'
  | notify _ _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ _ _ hby => exact absurd hby (by simp [Bar.copyBy])
  | clc _ _ _ ha' => rw [ha] at ha'; cases ha'; rfl

/-- The CTA of consumer `b` of cluster `c`. -/
abbrev ctaOfSel (c : Nat) (b : Fin 10) : Nat := 2 * c + ctaOf b

/-- The leader's request numbered `s` is the one its count names. -/
theorem issuesBefore_reqIdx {c s pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (he : X.get (producer L X c, reqIdx L X c s) = some ⟨pc, .clcIssue sp tg⟩) :
    issuesBefore L X c (producer L X c) (reqIdx L X c s) = s :=
  (req_spec he).2

/-- **The `q`-th completion of a response barrier is the notification of the leader's `q`-th
request.** -/
theorem ordinal_eq (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {k : Fin 2} :
    ∀ q {jd : Nat} {d : Record Ref} {h ki : Nat},
      (X.objects ((slot L c).full k))[jd]? = some d →
      d.id = .async (h, ki) (.notify (.cta (2 * c + k.val))) →
      completedTxCount ((X.objects ((slot L c).full k)).take jd) = q →
      issuesBefore L X c h ki = q := by
  intro q jd d h ki hd hid hq
  have hdm := List.mem_of_getElem? hd
  have hdf := fault_free hpre hX ht ((slot L c).full_mem k) d hdm
  obtain ⟨ha, -⟩ := item_rec hpre hX ht hd hid
  obtain ⟨s, hids, -, hcnt⟩ := completion_ordinal hpre hX ht hd hdf ha
  rw [hid] at hids
  simp only [item, Ref.async.injEq, Prod.mk.injEq] at hids
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hids
  obtain ⟨sp, tg, hci, -⟩ := hX.clc_notified hdm hid
  obtain ⟨pc, he⟩ := hci
  rw [issuesBefore_reqIdx he, ← hq, hcnt]

/-- A successful poll of a response barrier that observed phase `n` observed the completion of
the leader's request numbered `n`, which `n` completions precede. -/
theorem observes_request (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {f : Fin 2} {iw n : Nat} {w : Record Ref}
    (hw : (X.objects ((slot L c).full f))[iw]? = some w) (hww : w.reply.waited = some true)
    (ho : observedAt (X.objects ((slot L c).full f)) iw = some n) :
    ∃ jd d, jd < iw ∧ (X.objects ((slot L c).full f))[jd]? = some d ∧ d.fault = none ∧
      d.action = .completeTx 16 ∧ d.id = item L X c f n ∧
      phaseAt (X.objects ((slot L c).full f)) jd = some n ∧
      completedTxCount ((X.objects ((slot L c).full f)).take jd) = n := by
  have hch := (hX.tma.2.2.1 ((slot L c).full f)).1
  have hni := objects_noInval hX ht ((slot L c).full f)
  obtain ⟨st, p, hst, -, -, hcomp⟩ := hch.okPoll hw hww
  have hn : n < st.phase ∧ n = st.phase - 1 := by
    simp only [observedAt, hw, Option.bind_some, hcomp] at ho
    split_ifs at ho with hpos
    cases ho
    omega
  have hil : iw ≤ (X.objects ((slot L c).full f)).length := (List.getElem?_eq_some_iff.mp hw).1.le
  obtain ⟨jd, d, m, hjd, hd, hdf, ha, hq⟩ :=
    (resp_unitTx hpre hX ht (2 * c + f.val)).completion_in_phase (by norm_num) hch hni hil hst hn.1
  obtain ⟨s, hid, hph, hcnt⟩ := completion_ordinal hpre hX ht hd hdf ha
  have hsn : s = n := by
    have := hq.symm.trans hph
    exact (Option.some.inj this).symm
  subst hsn
  obtain ⟨ha16, -⟩ := item_rec hpre hX ht hd hid
  exact ⟨jd, d, hjd, hd, hdf, ha16, hid, hph, hcnt⟩

/-- A selected reader's successful poll of its response barrier observes the cancellation
request whose notification is the barrier's completion numbered by the reader's earlier
successful polls. -/
theorem observed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hsel : consumerSel L c b g = true)
    (he : X.get (g, j) = some ⟨pc, .wait ((slot L c).full ((slot L c).owner b)) p true acq sc⟩) :
    ∃ i jd d, (X.objects ((slot L c).full ((slot L c).owner b)))[jd]? = some d ∧
      d.id = .async i (.notify (.cta (ctaOfSel c b))) ∧
      completedTxCount ((X.objects ((slot L c).full ((slot L c).owner b))).take jd) =
        okPolls ((slot L c).full ((slot L c).owner b)) ((X.tr g).take j) ∧
      ClcObserved L X i (ctaOfSel c b) (g, j) := by
  obtain ⟨iw, w, st, hw, hwid, hww, -, -, ho⟩ := sel_poll_phase hpre hX ht hsel he
  obtain ⟨jd, d, hjd, hd, hdf, ha, hid, hph, hcnt⟩ := observes_request hpre hX ht hw hww ho
  have hg := Frame.lt_of_get hX he
  have hsel' := hsel
  simp only [consumerSel, decide_eq_true_eq] at hsel'
  have hdm := List.mem_of_getElem? hd
  have hid : d.id = .async (producer L X c, reqIdx L X c
      (okPolls ((slot L c).full ((slot L c).owner b)) ((X.tr g).take j)))
      (.notify (.cta (ctaOfSel c b))) := hid
  obtain ⟨s, tg, hi, hct, hnot, hloc⟩ := hX.clc_notified hdm hid
  obtain ⟨d0, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨hacq, -⟩ := (ht.sync_flags hg he hσ).1 _ _ _ _ _ rfl
  have hwf := (hX.tma.2.2.1 ((slot L c).full ((slot L c).owner b))).1.waited_no_fault hw hww
  refine ⟨_, jd, d, hd, hid, hcnt, hsel'.1.symm, hg, sc, _, _, ⟨rfl, s, tg, hi, hct, hnot, rfl⟩,
    ⟨⟨pc, p, ?_⟩, ?_⟩⟩
  · rw [he, ← hloc, hacq]
  · rw [← hloc]
    exact ⟨jd, iw, d, w, _, hd, hid, hdf, hw, hwid, hwf, hww, hjd, hph, ho,
      (objects_noInval hX ht _).sameLifetime jd iw⟩

/-- **Consumer `b`'s acknowledgement of every generation before a request synchronizes with the
request**: the leader's poll for the generation's next use, which guards the request, observed
the acknowledgement. -/
theorem ack_sync_thr (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} (b : Fin 10)
    {h ki pc cta : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hi : X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩) (hct : cta ∈ tg) (hcc : cta / 2 = c)
    {m : Nat} (hm : m < issuesBefore L X c h ki) :
    ∃ a ea, X.get (thr L X c b, a) = some ea ∧
      (∃ tx n rel sc, ea.kind = .arrive ((slot L c).empty 0) tx n rel sc) ∧
      arrivals ((slot L c).empty 0) ((X.tr (thr L X c b)).take a) = m ∧
      MSync L X (thr L X c b, a) (h, ki) := by
  have hacyc := hX.depAcyclic
  set R := ring hpre hX ht c with hR
  obtain ⟨hp, hmb, -, -⟩ := issue_facts hpre hX ht hi hct hcc
  subst hp
  set s := issuesBefore L X c (producer L X c) ki with hs
  have hki : reqIdx L X c s = ki := nthEv_eq (p := reqP L c) hi (by simp [clcIssuesTo, hmb])
  rw [← hki] at hi
  have hg := req_guard hpre hX ht hi hct hcc (n := m + 1) (by omega)
  rw [hki] at hg
  have hpres := MbarRing.Round.Slot.present_of_guard hg
  obtain ⟨hy, hphy⟩ := (R.content_empty hacyc (a := 0) (n := m) hpres).2 b
  obtain ⟨x, hx, hxid, hxf⟩ := (mem_SE hX).mp hy
  obtain ⟨ix, hix⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨-, q, hq⟩ := ack_rec hpre hX ht hix hxid
  obtain ⟨ea, hea⟩ : X.RefPresent (.thread (ackEv L X c b m)) :=
    hxid ▸ object_record_present hX.tma hx
  obtain ⟨pca, txa, na, rela, sca, rfl⟩ := ack_event hea
  have hga := Frame.lt_of_get hX hea
  obtain ⟨-, hcnt⟩ := ack_spec hea
  obtain ⟨iw, w, st, hw, hwid, hww, -, -, -, ho, hoi⟩ := epoll_rec hpre hX ht (n := m + 1)
    (by omega) hpres
  have hph : q = st.phase - 1 := by
    have h1 := MbarRing.Poll.phaseOf_eq hX hix hq
    rw [hxid] at h1
    have h2 : phE L X c (b, m) = oE L X c (m + 1) := hphy
    simp only [phE] at h2
    rw [← h1, h2, ho]
  rw [hph] at hq
  have hch := (hX.tma.2.2.1 ((slot L c).empty 0)).1
  have hni := objects_noInval hX ht ((slot L c).empty 0)
  have hub := MbarRing.Slot.updateBeforeWait_of_phase hch hni hix hxf hw
    (hch.waited_no_fault hw hww) hww hq hoi
  rw [hxid, hwid] at hub
  obtain ⟨-, hrel⟩ :=
    ht.sync_flags hga hea (Frame.event_state ht.sound hX ht.tracked hea (by simp)).choose_spec
  obtain ⟨hrelT, hrelS⟩ := hrel _ _ _ _ _ rfl
  obtain ⟨pcw, pw, acqw, scw, hew, -⟩ :=
    MbarRing.Poll.nth_spec (MbarRing.Poll.nth_present.mp hpres)
  have hew : X.get (epoll L X c (m + 1)) =
    some ⟨pcw, .wait ((slot L c).empty 0) pw true acqw scw⟩ :=
    hew
  have hh := Frame.lt_of_get hX hew
  obtain ⟨hacqT, hacqS⟩ := (ht.sync_flags hh hew
    (Frame.event_state ht.sound hX ht.tracked hew (by simp)).choose_spec).1 _ _ _ _ _ rfl
  subst hrelT hrelS hacqT hacqS
  have hpsel := producer_sel (X := X) hpre c
  have hsc : SameCluster L (thr L X c b) (producer L X c) := by
    have h1 := thr_sel (X := X) hpre c b
    simp only [consumerSel, decide_eq_true_eq] at h1
    have h2 := hpsel
    simp only [consumerSel, decide_eq_true_eq] at h2
    refine ⟨hga, hh, ?_⟩
    simp only [clusterOfCta_eq hpre]
    simp [ctaOf] at h2
    have := ctaOf_lt b
    omega
  obtain ⟨⟨-, hwk, hkl⟩, -⟩ := hg
  refine ⟨ackIdx L X c b m, _, hea, ⟨_, _, _, _, rfl⟩, hcnt, ⟨ackEv L X c b m,
    epoll L X c (m + 1), (slot L c).empty 0, .cluster, .cluster, ⟨_, _, _, hea⟩, ⟨⟨_, _, hew⟩, hub⟩,
    ⟨hsc, ⟨hsc.2.1, hsc.1, hsc.2.2.symm⟩⟩, rfl, hwk, hkl, rfl, le_rfl⟩⟩

/-- **A selected thread's acknowledgement of every generation before a request synchronizes with
the request.** -/
theorem ack_sync (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g j : Nat} {e : Event}
    (hsel : consumerSel L c b g = true) (he : X.get (g, j) = some e) (hke : ObjectKind e.kind)
    (hσ : ∃ r, Frame.stateAt (code L) X g j = some (some (.inr r)) ∧ roleWarp (g % L.block / 32) r)
    {h ki pc cta : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hi : X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩) (hct : cta ∈ tg) (hcc : cta / 2 = c)
    {m : Nat} (hm : m < issuesBefore L X c h ki) :
    ∃ a ea, X.get (g, a) = some ea ∧
      (∃ tx n rel sc, ea.kind = .arrive ((slot L c).empty 0) tx n rel sc) ∧
      arrivals ((slot L c).empty 0) ((X.tr g).take a) = m ∧ MSync L X (g, a) (h, ki) := by
  obtain ⟨a, ea, hea, ⟨tx, n, rel, sc, hka⟩, hcnt, hms⟩ := ack_sync_thr hpre hX ht b hi hct hcc hm
  have hga := Frame.lt_of_get hX hea
  have hgg : thr L X c b = g := sel_eq hpre hX ht hsel (thr_sel hpre c b) he hea hσ hke
    (by rw [hka]; trivial) (arrive_role hX ht hga hea hka Nat.one_pos)
  subst hgg
  exact ⟨a, ea, hea, ⟨tx, n, rel, sc, hka⟩, hcnt, hms⟩

/-- A selected thread's successful polls of its response barrier are increasing in its events. -/
theorem okPolls_mono {g a b : Nat} {m : Loc} (h : a ≤ b) :
    okPolls m ((X.tr g).take a) ≤ okPolls m ((X.tr g).take b) :=
  List.Sublist.countP_le (p := okPoll m) (List.take_sublist_take_left h)

/-- A selected thread's successful poll numbered `o` of its response barrier, before event `j`. -/
theorem nth_poll {g j o : Nat} {m : Loc} (h : o < okPolls m ((X.tr g).take j)) :
    ∃ w pc p acq sc, w < j ∧ X.get (g, w) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr g).take w) = o := by
  obtain ⟨w, ev, hw, hev, hcw⟩ := MbarRing.Slot.exists_nth_countP (okPoll m)
    (xs := (X.tr g).take j) (c := o) h
  have hwl : w < j := by
    have := (List.getElem?_eq_some_iff.mp hw).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hwl] at hw
  rw [List.take_take, Nat.min_eq_left hwl.le] at hcw
  obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form hev
  refine ⟨w, ev.pc, p, acq, sc, hwl, ?_, hcw⟩
  change (X.tr g)[w]? = _
  rw [hw, ← hk]

/-- The observing poll of a CLC response is a cluster-scope wait in the issuer's cluster, so
the response's cluster-scope completion and the poll meet (MEM-OBSERVED-COMPLETION). -/
theorem clcObs_scopes (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {i : EvId} {c : Nat} {w : EvId} (ho : ClcObserved L X i c w) :
    ScopesMeet L .cluster i.1 ho.2.2.choose w.1 := by
  obtain ⟨s1, tg1, hi1, hct1, -⟩ := ho.2.2.choose_spec.clc
  obtain ⟨-, -, hT⟩ := hX.clc.2.2.2.1 i s1 tg1 hi1
  obtain ⟨-, hit, -, -, -, -, -, hcl⟩ := (hT c).mp hct1
  obtain ⟨n, m, -, ⟨pc, parity, hget⟩, -⟩ := ho.2.2.choose_spec
  have hwt := ho.2.1
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
  obtain ⟨-, hsc⟩ := (ht.sync_flags hwt hget hσ).1 _ _ _ _ _ rfl
  rw [hsc]
  have hcl' : L.clusterOfCta (i.1 / L.block) = L.clusterOfCta (w.1 / L.block) := by
    rw [← ho.1]
    split at hcl
    · exact hcl.symm
    · rw [hcl]
  exact ⟨⟨hit, hwt, hcl'⟩, ⟨hwt, hit, hcl'.symm⟩⟩

/-- **The CLC responses by generation, for the selected readers.** A selected consumer `b` of
cluster `c` observes, at its `n`-th successful response poll, the request that the leader
scheduler issued after `n` earlier ones, and a read of its response buffer right after the poll
reads that request's response. Internal to this file: `sel_observed` is the exported form. -/
private theorem clcValues (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hw : ResponseWriters L X) :
    ∀ (c : Nat) (b : Fin 10) (g j pc p : Nat) (acq : Bool) (sc : MbarScope),
      consumerSel L c b g = true →
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (2 * c + ctaOf b) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ∃ i s tg r, X.ClcIssue i s tg ∧ i.1 / L.block = 2 * c ∧ i.1 % L.block / 32 = 10 ∧
        ((X.tr i.1).take i.2).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) =
          okPolls (Bar.loc L (2 * c + ctaOf b) ⟨.clc, 0, true⟩) ((X.tr g).take j) ∧
        ClcObserved L X i (2 * c + ctaOf b) (g, j) ∧ (X.clc i).resolved = some r ∧
        ∀ pcr (src : Acc) bs, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
          src.SameFootprint ⟨⟨.shared, 2 * c + ctaOf b, L.sharedBase + 144⟩, 16, false, false,
            .cta, 0, false⟩ →
          bs = (Value.clc r).toBytes.map some := by
  intro c b g j pc p acq sc hsel he
  have hblock := hpre.block
  have he' : X.get (g, j) = some ⟨pc, .wait ((slot L c).full ((slot L c).owner b)) p true acq sc⟩ :=
    he
  have hg := Frame.lt_of_get hX he
  have hσw := wait_role hX ht hg he rfl
  obtain ⟨⟨h, ki⟩, jd, d, hd, hdid, hcount, ho⟩ := observed hpre hX ht hsel he'
  have hord := ordinal_eq hpre hX ht _ hd hdid hcount
  have ho0 := ho
  obtain ⟨-, -, ws, hob⟩ := ho
  obtain ⟨s, tg, ⟨pci, hei⟩, hct, -, -⟩ := hob.clc
  have hsel1 := hsel
  simp only [consumerSel, decide_eq_true_eq] at hsel1
  have hctab := ctaOf_lt b
  obtain ⟨hp, -, hresp, -⟩ :=
    issue_facts (c := c) hpre hX ht hei hct (by simp only [ctaOfSel]; omega)
  have hpsel : consumerSel L c 2 h = true := hp ▸ producer_sel hpre c
  have hpsel1 := hpsel
  simp only [consumerSel, decide_eq_true_eq] at hpsel1
  simp [ctaOf, warpOf] at hpsel1
  obtain ⟨r0, hres0, -, -⟩ := hob.clc_response_write hX.clc ⟨pci, hei⟩
  refine ⟨(h, ki), s, tg, r0, ⟨pci, hei⟩, by simpa [ctaOf] using hpsel1.1,
    by simpa [warpOf] using hpsel1.2.1, hord.trans rfl, ho0, hres0, fun pcr src bs hr hfoot => ?_⟩
  have hfoot' : src.SameFootprint ⟨{ s.response with cta := ctaOfSel c b }, 16, false, false, .cta,
    0, false⟩ := by
    rw [hresp]
    exact hfoot
  have hread : X.MemReads (.thread (g, j + 1)) src bs := .inl ⟨pcr, hr⟩
  have hjr : j + 1 < (X.tr g).length := len_of_get hr
  have hhb : baseCausality L X (g, j) (g, j + 1) :=
    .single (.inl (po_of_source_not_access rfl (by omega) hjr (by simp [he', Event.acc])))
  have hsc : ∀ h', h' / L.block = 2 * c → h' < L.threads → SameCluster L g h' := by
    intro h' hh' hlt
    refine ⟨hg, hlt, ?_⟩
    simp only [clusterOfCta_eq hpre]
    omega
  -- an acknowledgement of generation `m` follows the poll of generation `m`
  have hackpoll : ∀ {a : Nat} {ea : Event} {tx n : Nat} {rel : Bool} {scc : MbarScope},
      X.get (g, a) = some ea → ea.kind = .arrive ((slot L c).empty 0) tx n rel scc →
      arrivals ((slot L c).empty 0) ((X.tr g).take a) + 1 ≤
        okPolls ((slot L c).full ((slot L c).owner b)) ((X.tr g).take a) := by
    intro a ea tx n rel scc hea hka
    obtain ⟨da, hσa⟩ := Frame.event_state ht.sound hX ht.tracked hea (by rintro pc f rfl; cases hka)
    have hab := ht.arrival_budget (b := ⟨.clc, 0, false⟩) (cta := 2 * c) hg hea hσa
      (by rw [hka]; rfl) Nat.one_pos
    simp only [Bar.gate, Bar.gateSlack] at hab
    have hloc : Bar.loc L (g / L.block) ⟨.clc, 0, true⟩ = (slot L c).full ((slot L c).owner b) := by
      rw [show (slot L c).full ((slot L c).owner b) = Bar.loc L (2 * c + ctaOf b) ⟨.clc, 0, true⟩
        from rfl, hsel1.1]
    rw [hloc] at hab
    exact hab
  have horder : ∀ k < src.size, ∀ other footprint bytes,
      X.MemWrites other footprint bytes → footprint.Covers (src.loc.at k) →
      other = .async (h, ki) (.write (.cta (ctaOfSel c b))) ∨
        modelCausality L X (src.loc.at k) other (.async (h, ki) (.write (.cta (ctaOfSel c b)))) ∨
          modelCausality L X (src.loc.at k) (.thread (g, j + 1)) other := by
    intro k hk other fp bytes hwr hc
    have hk16 : k < 16 := by rw [hfoot.2] at hk; exact hk
    have hl : src.loc.at k = ⟨.shared, ctaOfSel c b, L.sharedBase + 144 + k⟩ := by
      rw [hfoot.1]
      rfl
    obtain ⟨⟨h', ki'⟩, s', tg', rfl, ⟨pc', hei'⟩, hct'⟩ :=
      hw (ctaOfSel c b) k hk16 other fp bytes hwr (hl ▸ hc)
    obtain ⟨hp', -, -, -⟩ :=
      issue_facts (c := c) hpre hX ht hei' hct' (by simp only [ctaOfSel]; omega)
    have hhh : h' = h := hp'.trans hp.symm
    subst hhh
    have hcovers : AsyncCovers X (h', ki') (.write (.cta (ctaOfSel c b))) (src.loc.at k) :=
      ⟨fp, true, hwr.intent, hc⟩
    rcases Nat.lt_trichotomy (issuesBefore L X c h' ki') (issuesBefore L X c h' ki) with
      hlt | heq | hgt
    · -- an earlier request: its response was observed before this request
      right; left
      obtain ⟨wo, pco, po, acqo, sco, hwo, heo, hcwo⟩ := nth_poll (g := g) (j := j)
        (m := (slot L c).full ((slot L c).owner b)) (o := issuesBefore L X c h' ki')
        (by rw [← hord]; exact hlt)
      obtain ⟨⟨h'', ki''⟩, jd'', d'', hd'', hdid'', hcount'', ho''⟩ := observed hpre hX ht hsel heo
      have hord'' := ordinal_eq hpre hX ht _ hd'' hdid'' hcount''
      obtain ⟨hp'', ⟨pc'', sp'', tg'', he'', hmb''⟩, -⟩ := issuer hpre hX ht
        (List.mem_of_getElem? hd'') hdid''
      have hhh : h'' = h' := hp''.trans hp'.symm
      subst hhh
      obtain ⟨-, hmb', -, -⟩ := issue_facts (c := c) hpre hX ht hei' hct'
        (by simp only [ctaOfSel]; omega)
      have hkk := issues_inj he'' hei' (by simp [clcIssuesTo, hmb'']) (by simp [clcIssuesTo, hmb'])
        (hord''.trans hcwo)
      subst hkk
      obtain ⟨a, ea, hea, ⟨tx, n, rel, scc, hka⟩, harr, hms⟩ := ack_sync hpre hX ht hsel he trivial
        hσw hei hct (by simp only [ctaOfSel]; omega) hlt
      have hap := hackpoll hea hka
      rw [harr] at hap
      have hwa : wo < a := by
        by_contra hn
        have := okPolls_mono (X := X) (g := g) (m := (slot L c).full ((slot L c).owner b))
          (show a ≤ wo by omega)
        omega
      obtain ⟨-, hwr0, -⟩ := ho''.2.2.choose_spec.clc_response_write hX.clc ⟨pc'', he''⟩
      refine ⟨.inl ⟨Frame.lt_of_get hX hei', Frame.lt_of_get hX hei', rfl⟩,
        .direct ⟨hcovers, ?_,
          .inl ⟨(g, wo), .inr ⟨_, ho''.2.2.choose_spec, clcObs_scopes hX ht ho''⟩, ?_⟩⟩⟩
      · obtain ⟨r0, -, -, hw0⟩ := ho0.2.2.choose_spec.clc_response_write hX.clc ⟨pci, hei⟩
        exact ⟨_, true, hw0.intent, (hfoot'.covers _).mp (Acc.covers_at hk)⟩
      · exact (Relation.TransGen.single (.inl (po_of_not_access rfl hwa (len_of_get hea)
          (Execution.get_not_access hea hka (fun _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun _ _ h => by cases h) (fun _ _ _ h => by cases h))))).tail
          (.inr (.inr (.inl hms)))
    · -- this request
      left
      obtain ⟨-, hmb', -, -⟩ := issue_facts (c := c) hpre hX ht hei' hct'
        (by simp only [ctaOfSel]; omega)
      obtain ⟨-, hmb, -, -⟩ := issue_facts (c := c) hpre hX ht hei hct
        (by simp only [ctaOfSel]; omega)
      have hkk := issues_inj hei' hei (by simp [clcIssuesTo, hmb']) (by simp [clcIssuesTo, hmb]) heq
      rw [hkk]
    · -- a later request: this read was released to it through a proxy fence
      right; right
      obtain ⟨a, ea, hea, ⟨tx, n, rel, scc, hka⟩, harr, hms⟩ := ack_sync hpre hX ht hsel he trivial
        hσw hei' hct' (by simp only [ctaOfSel]; omega) hgt
      obtain ⟨da, hσa⟩ :=
        Frame.event_state ht.sound hX ht.tracked hea (by rintro pc f rfl; cases hka)
      obtain ⟨r', hσr⟩ : ∃ r', Frame.stateAt (code L) X g a = some (some (.inr r')) := by
        obtain ⟨rr, hrr, -⟩ := arrive_role hX ht hg hea (b := ⟨.clc, 0, false⟩) (cta := 2 * c)
          (by rw [hka]; rfl) Nat.one_pos
        exact ⟨rr, hrr⟩
      obtain ⟨jf, f, hjf, hfe, hfk, hfc⟩ := ht.ack_fenced hg hea hσr
        (show ea.kind = .arrive (Bar.loc L (2 * (g / L.block / 2)) ⟨.clc, 0, false⟩) tx n rel scc by
          rw [hka]
          have : 2 * (g / L.block / 2) = 2 * c := by omega
          rw [this]
          rfl)
      have hap := hackpoll hea hka
      rw [harr] at hap
      have hloc : Bar.loc L (g / L.block) ⟨.clc, 0, true⟩ = (slot L c).full ((slot L c).owner b) :=
        by
        rw [show (slot L c).full ((slot L c).owner b) = Bar.loc L (2 * c + ctaOf b) ⟨.clc, 0, true⟩
          from rfl, hsel1.1]
      rw [hloc] at hfc
      have hj1 : okPolls ((slot L c).full ((slot L c).owner b)) ((X.tr g).take (j + 1)) =
          issuesBefore L X c h' ki + 1 := by
        rw [Flow.okPolls, List.take_add_one, List.countP_append]
        have : (X.tr g)[j]? =
          some ⟨pc, .wait ((slot L c).full ((slot L c).owner b)) p true acq sc⟩ :=
          he
        rw [this]
        simp only [Option.toList_some, List.countP_singleton]
        rw [okPoll_wait rfl]
        simp only [Bool.true_and, decide_true, ↓reduceIte]
        rw [hord]
        rfl
      have hjf1 : j + 1 < jf := by
        rcases Nat.lt_or_ge (j + 1) jf with h1 | h1
        · exact h1
        · exfalso
          rcases Nat.lt_or_eq_of_le h1 with h2 | h2
          · have := okPolls_mono (X := X) (g := g) (m := (slot L c).full ((slot L c).owner b))
              (show jf ≤ j by omega)
            rw [← hord] at this
            omega
          · subst h2
            rw [hr] at hfe
            cases hfe
            cases hfk
      refine ⟨hcovers, .inl ⟨(g, jf), some (.shared .cta), none, ⟨f.pc, ?_⟩, hg, ⟨?_, ?_⟩,
        hsc h' (by omega) (Frame.lt_of_get hX hei'), ?_, ?_⟩⟩
      · rw [hfe]
        cases f
        simp only at hfk
        rw [hfk]
      · rw [hl]
      · rw [hl]
        simp only [ctaOfSel]
        omega
      · exact .single (.inl (po_of_not_access rfl hjf1 (len_of_get hfe)
          (Execution.get_not_access hfe hfk (fun _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun _ _ h => by cases h) (fun _ _ _ h => by cases h))))
      · exact (Relation.TransGen.single (.inl (po_of_not_access rfl hjf (len_of_get hea)
          (Execution.get_not_access hea hka (fun _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun _ _ h => by cases h) (fun _ _ _ h => by cases h))))).tail
          (.inr (.inr (.inl hms)))
  obtain ⟨r, hres, -, hbytes, -⟩ :=
    ho0.2.2.choose_spec.clc_read_rebuild_of_ordered_reuse hX ⟨pci, hei⟩ hread hfoot'
    (clcObs_scopes hX ht ho0) hhb horder
  rw [hres0] at hres
  cases hres
  exact hbytes

/-- **A selected reader's poll observes the request numbered by its earlier successful polls**, and
its read holds that request's response. -/
theorem sel_observed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrw : ResponseWriters L X) {g j pc p : Nat} {acq : Bool}
    {sc : MbarScope} {b : Fin 10} (hsel : consumerSel L (g / L.block / 2) b g = true)
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩) :
    ∃ i s tg r, X.ClcIssue i s tg ∧ i.1 / L.block = 2 * (g / L.block / 2) ∧
      i.1 % L.block / 32 = 10 ∧
      ((X.tr i.1).take i.2).countP
          (clcIssuesTo (Bar.loc L (2 * (g / L.block / 2)) ⟨.clc, 0, true⟩)) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) ∧
      ClcObserved L X i (g / L.block) (g, j) ∧ (X.clc i).resolved = some r ∧
      ∀ pcr (src : Acc) bs, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ →
        bs = (Value.clc r).toBytes.map some := by
  have hcta : 2 * (g / L.block / 2) + ctaOf b = g / L.block := by
    simp only [consumerSel, decide_eq_true_eq] at hsel
    omega
  have he' : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (2 * (g / L.block / 2) + ctaOf b)
      ⟨.clc, 0, true⟩) p true acq sc⟩ := by
    rw [hcta]
    exact he
  obtain ⟨i, s, tg, r, hi, h1, h2, h3, hO, hres, hread⟩ :=
    clcValues hpre hX ht hrw (g / L.block / 2) b g j pc p acq sc hsel he'
  rw [hcta] at h3 hO hread
  exact ⟨i, s, tg, r, hi, h1, h2, h3, hO, hres, hread⟩

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
