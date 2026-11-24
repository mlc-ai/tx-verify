-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Values

@[expose] public section

/-! # A request happens before every observer of its notification

The leader's request numbered `n` is notified to its own CTA's response barrier as the phase-`n`
completion of that barrier (`completion_ordinal`). A successful wait that observes the
notification observes phase `n`, which holds one arrival (`card_unit_arrivals_phase`): the
leader's arrival with `n` earlier ones (`resp_units`), which is po-after the request
(`ThreadFacts.lead_arrive_after_issue`). That arrival releases to the observer's acquire wait
(`MSync`), so the request happens before the observer's later events. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The leader's issue at `ki` is by a scheduler: its state there is a scheduler's. -/
theorem issue_sched (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {h ki pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (hei : X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩) :
    ∃ sd, Frame.stateAt (code L) X h ki = some (some (.inr (.sched sd))) := by
  have hblock := hpre.block
  have hh := Frame.lt_of_get hX hei
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hei (by simp)
  obtain ⟨b, hb, hby, hmb, hresp, hcl⟩ := (ht.ring_event hh hei hσ).clc _ _ rfl
  obtain ⟨rg, s, f⟩ := b
  simp only [Bar.Valid] at hb
  cases rg <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
  obtain rfl : s = 0 := by omega
  obtain ⟨⟨sd, rfl⟩, -⟩ := hby
  exact ⟨sd, hσ⟩

/-- The arrival units before an arrival on a response barrier are its thread's earlier
arrivals: every arrival there is that thread's and does not fault. -/
theorem resp_units (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {f : Fin 2} {ix : Nat} {x : Record Ref}
    (hix : (X.objects ((slot L c).full f))[ix]? = some x) {g jj : Nat}
    (hid : x.id = .thread (g, jj))
    (hsel : consumerSel L c ⟨2 + f.val, by have := f.isLt; omega⟩ g = true)
    {e : Event} (he : X.get (g, jj) = some e)
    (hσ : ∃ r, Frame.stateAt (code L) X g jj = some (some (.inr r)) ∧ roleWarp (g % L.block / 32) r)
    (hke : ObjectKind e.kind) :
    unitsBefore (X.objects ((slot L c).full f)) ix =
      Flow.arrivals ((slot L c).full f) ((X.tr g).take jj) := by
  have hch := (hX.tma.2.2.1 ((slot L c).full f)).1
  have hclean := fault_free hpre hX ht ((slot L c).full_mem f)
  have hunit : ∀ r ∈ (X.objects ((slot L c).full f)).take ix, ∀ c' tx, r.fault = none →
      r.action = .arrive c' tx → c' = 1 := fun r hr c' tx _ ha =>
    (resp_unitTx hpre hX ht (2 * c + f.val)).arrive r (List.mem_of_mem_take hr)
      (hclean r (List.mem_of_mem_take hr)) c' tx ha |>.1
  unfold unitsBefore
  rw [arrivalUnits_eq_length hunit, ← List.countP_eq_length_filter]
  have hwin := hX.object_thread_arrival_count_window (m := (slot L c).full f) (g := g) (k := jj)
    ((X.objects ((slot L c).full f)).take ix) (fun _ hq => List.mem_of_mem_take hq)
    (hch.1.sublist ((List.take_sublist ix _).map _))
    (fun q j hq hqid => hX.object_thread_take_mem_iff hix hid hq hqid)
  unfold Flow.arrivals
  rw [← hwin]
  refine List.countP_congr fun q hq => ?_
  have hqm := List.mem_of_mem_take hq
  rw [countedArrive_iff, threadArrival_iff]
  constructor
  · rintro ⟨hf, c', tx, ha⟩
    obtain ⟨g', jj', _, _, _, _, hqid, hqe, rfl, rfl, hsel', hσ'⟩ := resp_arrival hX ht hqm ha
    have hgg : g' = g := sel_eq hpre hX ht hsel hsel' he hqe hσ hke trivial
      ⟨_, hσ', ht.role_warp (Frame.lt_of_get hX hqe) (idx_le hqe) hσ'⟩
    subst hgg
    exact ⟨objectThreadSelected_iff.mpr ⟨_, hqid⟩, _, _, ha⟩
  · rintro ⟨-, c', tx, ha⟩
    exact ⟨hclean q hqm, c', tx, ha⟩

/-- **A request happens before every observer of its notification on its own CTA's response
barrier, from the observer's next event on.** -/
theorem issue_baseCausality_observer (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i : EvId} {s : Clc.Spec} {tg : List Nat} (hi : X.ClcIssue i s tg)
    {w : EvId} (ho : ClcObserved L X i (i.1 / L.block) w) :
    ∀ f2, w.2 < f2 → f2 < (X.tr w.1).length → baseCausality L X i (w.1, f2) := by
  classical
  obtain ⟨h, ki⟩ := i
  obtain ⟨wt, wk⟩ := w
  intro f2 hw2 hf2
  obtain ⟨hcw, hwlt, ws0, n0, m0, ⟨rfl, s', targets, ⟨pc', hei'⟩, hctaT, hnot, rfl⟩,
    ⟨⟨pcw, parw, hew⟩, hnbw⟩⟩ := ho
  obtain ⟨pc, hei⟩ := hi
  have key := Option.some.inj (hei.symm.trans hei')
  simp only [Event.mk.injEq, Kind.clcIssue.injEq] at key
  obtain ⟨-, rfl, rfl⟩ := key
  obtain ⟨c, hcdef⟩ : ∃ c, h / L.block / 2 = c := ⟨_, rfl⟩
  obtain ⟨hp, hmb, -, -⟩ := issue_facts (c := c) hpre hX ht hei hctaT hcdef
  have hselh : consumerSel L c 2 h = true := hp ▸ producer_sel hpre c
  have hcta2 : h / L.block = 2 * c := by
    have h1 := hselh
    simp only [consumerSel, decide_eq_true_eq] at h1
    simp [ctaOf] at h1
    omega
  have hobj : ({ s.mbar with cta := h / L.block } : Loc) = (slot L c).full 0 := by
    rw [hmb, hcta2]
    rfl
  rw [hobj] at hnbw
  obtain ⟨ic, jw, rc, rwr, phase, hic, hrcid, -, hjw, hwid, -, hwwait, hlt, hphc, hobsw, -⟩ :=
    hnbw
  have hrcact := (item_rec hpre hX ht (f := 0) hic hrcid).1
  have hch := (hX.tma.2.2.1 ((slot L c).full 0)).1
  have hni := objects_noInval hX ht ((slot L c).full 0)
  have hclean := fault_free hpre hX ht ((slot L c).full_mem 0)
  -- the notification is the completion of the request numbered `phase`
  obtain ⟨s0, hid0, hph0, -⟩ := completion_ordinal hpre hX ht hic
    (hclean rc (List.mem_of_getElem? hic)) hrcact
  have hs0 : s0 = phase := Option.some.inj (hph0.symm.trans hphc)
  subst hs0
  have hki : reqIdx L X c s0 = ki := by
    rw [hrcid] at hid0
    simp only [item, Ref.async.injEq, Prod.mk.injEq] at hid0
    exact hid0.1.2.symm
  have hp' : h = producer L X c := hp
  subst hp'
  rw [← hki] at hei
  have hn : issuesBefore L X c (producer L X c) (reqIdx L X c s0) = s0 := issuesBefore_reqIdx hei
  -- the observer's wait found phase `s0 + 1`; the phase `s0` holds one arrival
  obtain ⟨stw, pw, hstw, -, -, hcomp⟩ := hch.okPoll hjw hwwait
  have hstw1 : stw.phase = s0 + 1 := by
    simp only [observedAt, hjw, Option.bind_some, hcomp] at hobsw
    split_ifs at hobsw with hpos
    cases hobsw
    omega
  have hjwl : jw ≤ (X.objects ((slot L c).full 0)).length := (List.getElem?_eq_some_iff.mp hjw).1.le
  have hu := resp_unitTx hpre hX ht (2 * c + 0)
  have hcard := hch.card_unit_arrivals_phase hni (n := 1) (q := s0)
    (fun k r c' tx hk hf ha => (hu.arrive r (List.mem_of_getElem? hk) hf c' tx ha).1)
    (fun k st _ hst => hu.expected k st hst) (incrementsBefore_zero hX ht _) hjwl hstw (by omega)
  obtain ⟨ix, hixm⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num)
  obtain ⟨-, x, tx, hxi, hxa, hxf, hphx⟩ := Finset.mem_filter.mp hixm
  obtain ⟨g, jj, pcx, rel, scx, sdx, hidx, heidx, -, rfl, hselg, hσx⟩ :=
    resp_arrival hX ht (List.mem_of_getElem? hxi) hxa
  have hgg : g = producer L X c := sel_eq hpre hX ht hselh hselg hei heidx
    ⟨_, (issue_sched hpre hX ht hei).choose_spec, ht.role_warp (Frame.lt_of_get hX hei) (idx_le hei)
      (issue_sched hpre hX ht hei).choose_spec⟩ trivial trivial
    ⟨_, hσx, ht.role_warp (Frame.lt_of_get hX heidx) (idx_le heidx) hσx⟩
  subst hgg
  -- the leader's arrival opening phase `s0` follows `s0` earlier arrivals of its own
  obtain ⟨stx, hstx⟩ := ring_state_at (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hxi
    (ring_pos (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hxi (by rw [hxa]; intro m h; cases h))
  have hstx : stateBefore (X.objects ((slot L c).full 0)) ix = some stx := hstx
  have hphs : stx.phase = s0 := by
    have : phaseAt (X.objects ((slot L c).full 0)) ix = some stx.phase := by simp [phaseAt, hstx]
    rw [hphx] at this
    exact (Option.some.inj this).symm
  have hux := hch.unit_arrival_phase hni hxi hstx hxa hxf
  rw [hu.expected ix stx hstx, hphs,
    incrementsBefore_eq_zero _ (incrementsBefore_zero hX ht _)] at hux
  have hunits := resp_units hpre hX ht hxi hidx hselg heidx
    ⟨_, hσx, ht.role_warp (Frame.lt_of_get hX heidx) (idx_le heidx) hσx⟩ trivial
  have harr : Flow.arrivals ((slot L c).full 0) ((X.tr (producer L X c)).take jj) = s0 := by
    omega
  have hkind : (⟨pcx, .arrive ((slot L c).full 0) 16 1 rel scx⟩ : Event).kind =
      .arrive (Bar.loc L ((producer L X c) / L.block) ⟨.clc, 0, true⟩) 16 1 rel scx := by
    simp [hcta2]
    rfl
  have hfield := ht.lead_arrive_after_issue (Frame.lt_of_get hX heidx) heidx hσx
    (show Loader.leader L (producer L X c) = true by simp [Loader.leader, hcta2]) hkind
  rw [hcta2] at hfield
  have harr' : arrivals (Bar.loc L (2 * c) ⟨.clc, 0, true⟩) ((X.tr (producer L X c)).take jj) =
      s0 := harr
  have hltk : reqIdx L X c s0 < jj := by
    by_contra hle
    have hsub := List.Sublist.countP_le (p := clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩))
      (List.take_sublist_take_left (l := X.tr (producer L X c)) (show jj ≤ reqIdx L X c s0 by
        omega))
    have hiss : issuesBefore L X c (producer L X c) (reqIdx L X c s0) =
        ((X.tr (producer L X c)).take (reqIdx L X c s0)).countP
          (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) := rfl
    omega
  -- the release and the acquire
  obtain ⟨hrelt, hrels⟩ := (ht.sync_flags (Frame.lt_of_get hX heidx) heidx
    (Frame.event_state ht.sound hX ht.tracked heidx (by simp)).choose_spec).2 _ _ _ _ _ rfl
  subst hrelt hrels
  obtain ⟨dw, hσw⟩ := Frame.event_state ht.sound hX ht.tracked hew (by simp)
  obtain ⟨-, hacqs⟩ := (ht.sync_flags hwlt hew hσw).1 _ _ _ _ _ rfl
  subst hacqs
  rw [hobj] at hew
  have hsc1 : SameCluster L (producer L X c) wt := ⟨Frame.lt_of_get hX heidx, hwlt, by rw [hcw]⟩
  have hsc2 : SameCluster L wt (producer L X c) := ⟨hwlt, Frame.lt_of_get hX heidx, by rw [hcw]⟩
  have hub := MbarRing.Slot.updateBeforeWait_of_phase hch hni hxi hxf hjw
    (hch.waited_no_fault hjw hwwait) hwwait hphx hobsw
  rw [hidx, hwid] at hub
  have hms : MSync L X (producer L X c, reqIdx L X c s0) (wt, f2) :=
    ⟨(producer L X c, jj), (wt, wk), (slot L c).full 0, .cluster, .cluster, ⟨16, 1, pcx, heidx⟩,
      ⟨⟨pcw, parw, hew⟩, hub⟩, ⟨hsc1, hsc2⟩, rfl, hw2, hf2, rfl, by omega⟩
  rw [hki] at hms
  exact Relation.TransGen.single (Or.inr (Or.inr (Or.inl hms)))

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
