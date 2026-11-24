-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Lemmas.Order.OrderNotAccess

@[expose] public section

/-! # The CLC response buffer is ordered

A response buffer byte of CTA `C` is read by threads of `C`, each right after a successful poll of
`C`'s response barrier (`ThreadFacts.read_poll`), and written by the cancellation requests
targeting `C` (`regions`), all the leader scheduler's of the cluster, numbered by its earlier
requests (`ClcRing.issue_facts`). A reader's poll numbered `p` observes request `p`
(`ReaderValues`).

* A request numbered `n ≤ p` is observed by the reader's poll numbered `n`, before its read
  (`read_write_ordered`).
* A request numbered `n > p` is issued after the reader's read reached a proxy fence of `C`: a
  selected reader's fence before its acknowledgement of response `p`, which the leader polled
  before requesting again (`sel_later`); a consumer's fence before its group's arrival of ordinal
  `p`, whose first thread acknowledged it (`cons_later`).
* Of two requests numbered `n < n'`, the first is observed in `C` by the loader of `C`, whose
  acknowledgement of response `n` precedes the second (`write_write_ordered`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy ClcRing

noncomputable section

namespace Region

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The leader's request numbered after a selected reader's poll comes after the reader's read
reached a proxy fence: the fence before the reader's acknowledgement of that response. -/
theorem sel_later (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hsel : consumerSel L c b g = true)
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    {pcr : Nat} {src : Acc} {bs : List (Option Byte)}
    (hrd : X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩) {h ki pci cta : Nat} {s : Clc.Spec}
    {tg : List Nat} (hei : X.get (h, ki) = some ⟨pci, .clcIssue s tg⟩) (hct : cta ∈ tg)
    (hcc : cta / 2 = c)
    (hgt : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) <
      issuesBefore L X c h ki)
    {l : Loc} (hls : l.space = .shared) (hlc : l.cta = g / L.block) :
    ProxyBefore L X (g, j + 1) (h, ki) l := by
  have hblock := hpre.block
  have hg := Frame.lt_of_get hX he
  have hsel1 := hsel
  simp only [consumerSel, decide_eq_true_eq] at hsel1
  have hctab := ctaOf_lt b
  obtain ⟨a, ea, hea, ⟨tx, n, rel, scc, hka⟩, harr, hms⟩ :=
    ack_sync hpre hX ht hsel he trivial (wait_role hX ht hg he rfl) hei hct hcc hgt
  have hka' : ea.kind = .arrive (Bar.loc L (2 * c) ⟨.clc, 0, false⟩) tx n rel scc := by
    rw [hka]; rfl
  obtain ⟨r', hσr, -⟩ := arrive_role hX ht hg hea hka' Nat.one_pos
  obtain ⟨jf, f, hjf, hfe, hfk, hfc⟩ := ht.ack_fenced hg hea hσr
    (show ea.kind = .arrive (Bar.loc L (2 * (g / L.block / 2)) ⟨.clc, 0, false⟩) tx n rel scc by
      rw [hka']
      have : 2 * (g / L.block / 2) = 2 * c := by omega
      rw [this])
  have hab := ht.arrival_budget (b := ⟨.clc, 0, false⟩) (cta := 2 * c) hg hea hσr hka'
    Nat.one_pos
  simp only [Bar.gate, Bar.gateSlack] at hab
  change arrivals ((slot L c).empty 0) ((X.tr g).take a) + 1 ≤ _ at hab
  rw [harr] at hab
  have hjf1 : j + 1 < jf := by
    rcases Nat.lt_or_ge (j + 1) jf with h1 | h1
    · exact h1
    · exfalso
      rcases Nat.lt_or_eq_of_le h1 with h2 | h2
      · have := okPolls_mono (X := X) (g := g) (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
          (show jf ≤ j by omega)
        omega
      · subst h2
        rw [hrd] at hfe
        cases hfe
        cases hfk
  obtain ⟨hp, -, -, -⟩ := issue_facts (c := c) hpre hX ht hei hct hcc
  have hhc : h / L.block = 2 * c := by rw [hp]; exact producer_cta hpre c
  refine ⟨(g, jf), some (.shared .cta), none, ⟨f.pc, ?_⟩, hg, ⟨hls, hlc⟩,
    ⟨hg, Frame.lt_of_get hX hei, ?_⟩, ?_, ?_⟩
  · rw [hfe]
    cases f
    simp only at hfk
    rw [hfk]
  · simp only [clusterOfCta_eq hpre]
    omega
  · exact .single (.inl (po_of_not_access rfl hjf1 (len_of_get hfe)
      (Execution.get_not_access hfe hfk (fun _ _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ h => by cases h) (fun _ _ _ h => by cases h))))
  · exact (Relation.TransGen.single (.inl (po_of_not_access rfl hjf (len_of_get hea)
      (Execution.get_not_access hea hka' (fun _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ _ _ h => by cases h))))).tail
      (.inr (.inr (.inl hms)))

/-- The leader's request numbered after a consumer's poll comes after the consumer's read reached
a proxy fence: the fence before its group's arrival of that ordinal. -/
theorem cons_later (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j : Nat} (hg : g < L.threads) (hw : g % L.block / 32 < 8)
    {pcr : Nat} {src : Acc} {bs : List (Option Byte)}
    (hrd : X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩) {h ki pci : Nat} {s : Clc.Spec}
    {tg : List Nat} (hei : X.get (h, ki) = some ⟨pci, .clcIssue s tg⟩) (hct : g / L.block ∈ tg)
    (hgt : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) <
      issuesBefore L X (g / L.block / 2) h ki)
    {l : Loc} (hls : l.space = .shared) (hlc : l.cta = g / L.block) :
    ProxyBefore L X (g, j + 1) (h, ki) l := by
  have hblock := hpre.block
  have hq2 : Consumer.tidOf L g / 32 / 4 < 2 := by
    show g % L.block / 32 / 4 < 2
    omega
  obtain ⟨in_, pcn, hIBn, hcountn, hbn⟩ := grp_group hpre hX ht hg hw hei hct rfl hgt
    (OutputRing.ResponsesAgreeBelow.of_all
      (allResponsesAgree hpre hX ht (responseWriters hpre hX ht)) _)
  obtain ⟨cn, hσn, hsiten⟩ := group_arrival_site hX ht hq2 hIBn hg
  have hcl := ht.cons_clc hg hIBn hσn
  have hclc1 : cn.clcHold = 1 := by simp [Consumer.D.clcHold, hsiten]
  rw [hclc1, hcountn] at hcl
  obtain ⟨jf, fe, hjfl, hfe, hfk, hokf⟩ := ht.cons_clc_fence hg hIBn hσn hsiten
  have hjf1 : j + 1 < jf := by
    rcases Nat.lt_or_ge (j + 1) jf with h1 | h1
    · exact h1
    · exfalso
      rcases Nat.lt_or_eq_of_le h1 with h2 | h2
      · have hmono := okPolls_mono (X := X) (g := g)
          (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (show jf ≤ j by omega)
        omega
      · subst h2
        rw [hrd] at hfe
        cases hfe
        cases hfk
  obtain ⟨hp, -, -, -⟩ := issue_facts hpre hX ht hei hct rfl
  have hhc : h / L.block = 2 * (g / L.block / 2) := by rw [hp]; exact producer_cta hpre _
  refine ⟨(g, jf), some (.shared .cta), none, ⟨fe.pc, ?_⟩, hg, ⟨hls, hlc⟩,
    ⟨hg, Frame.lt_of_get hX hei, ?_⟩,
    .single (.inl (po_of_not_access rfl hjf1 (len_of_get hfe)
      (Execution.get_not_access hfe hfk (fun _ _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)))), hbn jf hjfl⟩
  · rw [hfe]
    cases fe
    simp only at hfk
    rw [hfk]
  · simp only [clusterOfCta_eq hpre]
    omega

/-- The selector of a reader that is not a consumer: its role's warp in its CTA. -/
theorem reader_sel (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g j pc p : Nat}
    {acq : Bool} {sc : MbarScope}
    (hg : g < L.threads)
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hw : 8 ≤ g % L.block / 32) : ∃ b, consumerSel L (g / L.block / 2) b g = true := by
  obtain ⟨ro, hσ, hwr⟩ := wait_role hX ht hg he rfl
  rcases ro with l | mm | sd | cc
  · have hwl : g % L.block / 32 = 11 := hwr
    exact ⟨_, consumerSel_of L (loadB ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩)
      (by
        rw [(loadB_facts _).1]
        show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
        omega) (by rw [(loadB_facts _).2.1]; exact hwl)
      (by rw [(loadB_facts _).2.2]; simp)⟩
  · have hwm : mm.w = g % L.block / 32 ∧ (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) := hwr
    rcases Nat.mod_two_eq_zero_or_one (g / L.block) with h0 | h1
    · exact ⟨_, consumerSel_of L (mmaB ⟨g % L.block / 32 - 8, by have := hwm.2; omega⟩)
        (by rw [(mmaB_facts _).1]; omega)
        (by
          rw [(mmaB_facts _).2.1]
          show g % L.block / 32 = 8 + (g % L.block / 32 - 8)
          have := hwm.2
          omega)
        (by rw [(mmaB_facts _).2.2]; simp)⟩
    · exact absurd rfl (ht.mma_odd_quiet hg he hσ ⟨mm, rfl⟩ h1 p true acq sc)
  · have hws : g % L.block / 32 = 10 := hwr
    exact ⟨_, consumerSel_of L (schedB ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩)
      (by
        rw [(schedB_facts _).1]
        show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
        omega) (by rw [(schedB_facts _).2.1]; exact hws)
      (by rw [(schedB_facts _).2.2]; simp)⟩
  · have : g % L.block / 32 < 8 := hwr
    omega

/-- **A read and a request writing its buffer are ordered**: the poll numbered `n` observes request
`n ≤ p` before the read; request `n > p` follows the read's proxy fence. -/
theorem read_write_ordered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) {g j pc p : Nat} {acq : Bool}
    {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    {pcr : Nat} {src : Acc} {bs : List (Option Byte)}
    (hrd : X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩) {i : EvId} {s : Clc.Spec} {tg : List Nat}
    (hi : X.ClcIssue i s tg) (hct : g / L.block ∈ tg) {l : Loc}
    (hcov : AsyncCovers X i (.write (.cta (g / L.block))) l) (hls : l.space = .shared)
    (hlc : l.cta = g / L.block) :
    modelCausality L X l (.async i (.write (.cta (g / L.block)))) (.thread (g, j + 1)) ∨
      modelCausality L X l (.thread (g, j + 1)) (.async i (.write (.cta (g / L.block)))) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨h, ki⟩ := i
  obtain ⟨pci, hei⟩ := hi
  obtain ⟨hp, hmb, -, -⟩ := issue_facts (c := g / L.block / 2) hpre hX ht hei hct rfl
  -- the request a poll observes, by its number
  have obs : ∀ {w pcw pw acqw scw}, X.get (g, w) =
    some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pw
      true acqw scw⟩ → okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take w) =
        issuesBefore L X (g / L.block / 2) h ki → ClcObserved L X (h, ki) (g / L.block) (g, w) := by
    intro w pcw pw acqw scw hew hcw
    obtain ⟨⟨h0, k0⟩, s0, tg0, r0, ⟨pc0, he0⟩, -, -, hcnt0, hobs0, -⟩ :=
      hv (g / L.block / 2) g w pcw pw acqw scw rfl hew
    have hct0 := clcObs_mem hobs0 ⟨pc0, he0⟩
    obtain ⟨hp0, hmb0, -, -⟩ := issue_facts (c := g / L.block / 2) hpre hX ht he0 hct0 rfl
    have hh : h0 = h := hp0.trans hp.symm
    subst hh
    have hk := issues_inj (c := g / L.block / 2) he0 hei (by simp [clcIssuesTo, hmb0])
      (by simp [clcIssuesTo, hmb])
      (hcnt0.trans hcw)
    subst hk
    exact hobs0
  rcases Nat.lt_or_ge (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j))
      (issuesBefore L X (g / L.block / 2) h ki) with hgt | hle
  · -- a later request
    right
    refine ⟨hcov, ?_⟩
    by_cases hw : g % L.block / 32 < 8
    · exact .inl (cons_later hpre hX ht hg hw hrd hei hct hgt hls hlc)
    · obtain ⟨b, hsel⟩ := reader_sel hX ht hg he (by omega)
      exact .inl (sel_later hpre hX ht hsel he hrd hei hct rfl hgt hls hlc)
  · left
    obtain ⟨w, pcw, pw, acqw, scw, hwj, hew, hcw⟩ : ∃ w pcw pw acqw scw, w ≤ j ∧
        X.get (g, w) =
          some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pw true acqw scw⟩ ∧
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take w) =
          issuesBefore L X (g / L.block / 2) h ki := by
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨w, pcw, pw, acqw, scw, hw, hew, hcw⟩ := nth_poll (X := X) (g := g) (j := j)
          (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) hlt
        exact ⟨w, pcw, pw, acqw, scw, hw.le, hew, hcw⟩
      · exact ⟨j, pc, p, acq, sc, le_rfl, he, heq.symm⟩
    refine ⟨hcov, (g, w), .inr ⟨_, (obs hew hcw).2.2.choose_spec,
      clcObs_scopes hX ht (obs hew hcw)⟩,
      .inl (.single (.inl (po_of_source_not_access rfl (by omega) (len_of_get hrd)
      (by simp [hew, Event.acc]))))⟩

/-- **Two requests writing a buffer are ordered**: the earlier is observed in the buffer's CTA by
its loader, whose acknowledgement of it precedes the later. -/
theorem write_write_ordered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) {C h ki ki' pci pci' : Nat} {s s' : Clc.Spec}
    {tg tg' : List Nat} (hei : X.get (h, ki) = some ⟨pci, .clcIssue s tg⟩)
    (hei' : X.get (h, ki') = some ⟨pci', .clcIssue s' tg'⟩) (hct : C ∈ tg) (hct' : C ∈ tg')
    (hlt : issuesBefore L X (C / 2) h ki < issuesBefore L X (C / 2) h ki') {l : Loc}
    (hcov : AsyncCovers X (h, ki) (.write (.cta C)) l)
    (hcov' : AsyncCovers X (h, ki') (.write (.cta C)) l) :
    modelCausality L X l (.async (h, ki) (.write (.cta C)))
        (.async (h, ki') (.write (.cta C))) := by
  have hblock := hpre.block
  set c := C / 2 with hc
  obtain ⟨hp, hmb, -, -⟩ := issue_facts (c := c) hpre hX ht hei hct rfl
  -- the loader of `C` acknowledged response `n` before request `n'`
  obtain ⟨g, a, ea, hsel, hea, ⟨tx, n, rel, scc, hka⟩, harr, hms⟩ :=
    ack_sync_sel (b := loadB ⟨C % 2, Nat.mod_lt _ (by norm_num)⟩) hpre hX ht hei' hct' rfl hlt
  have hsel1 := hsel
  simp only [consumerSel, decide_eq_true_eq, (loadB_facts _).1] at hsel1
  have hgC : g / L.block = C := by omega
  have hg := Frame.lt_of_get hX hea
  have hka' : ea.kind = .arrive (Bar.loc L (2 * c) ⟨.clc, 0, false⟩) tx n rel scc := by
    rw [hka]; rfl
  obtain ⟨da, hσa⟩ := Frame.event_state ht.sound hX ht.tracked hea (by rintro pc f rfl; cases hka)
  have hab := ht.arrival_budget (b := ⟨.clc, 0, false⟩) (cta := 2 * c) hg hea hσa hka'
    Nat.one_pos
  simp only [Bar.gate, Bar.gateSlack] at hab
  change arrivals ((slot L c).empty 0) ((X.tr g).take a) + 1 ≤ _ at hab
  rw [harr, hgC] at hab
  obtain ⟨w, pcw, pw, acqw, scw, hwa, hew, hcw⟩ := nth_poll (X := X) (g := g) (j := a)
    (m := Bar.loc L C ⟨.clc, 0, true⟩) (o := issuesBefore L X c h ki) (by omega)
  rw [← hgC] at hew hcw
  obtain ⟨⟨h0, k0⟩, s0, tg0, r0, ⟨pc0, he0⟩, -, -, hcnt0, hobs0, -⟩ :=
    hv c g w pcw pw acqw scw (by omega) hew
  have hct0 := clcObs_mem hobs0 ⟨pc0, he0⟩
  obtain ⟨hp0, hmb0, -, -⟩ := issue_facts (c := c) hpre hX ht he0 hct0 (by omega)
  have hh : h0 = h := hp0.trans hp.symm
  subst hh
  have hk := issues_inj (c := c) he0 hei (by simp [clcIssuesTo, hmb0]) (by simp [clcIssuesTo, hmb])
    (hcnt0.trans hcw)
  subst hk
  rw [hgC] at hobs0
  exact ⟨.inl ⟨Frame.lt_of_get hX hei, Frame.lt_of_get hX hei, rfl⟩,
    .direct ⟨hcov, hcov', .inl ⟨(g, w), .inr ⟨_, hobs0.2.2.choose_spec, clcObs_scopes hX ht hobs0⟩,
    (Relation.TransGen.single (.inl (po_of_not_access rfl hwa (len_of_get hea)
      (Execution.get_not_access hea hka (fun _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ _ _ h => by cases h))))).tail
      (.inr (.inr (.inl hms)))⟩⟩⟩

/-- The accessors of a response buffer byte: a thread's read right after its successful response
poll, or a request's write targeting the byte's CTA. -/
theorem response_access (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {ref : Ref} {a : Acc} {w : Bool} {l : Loc} (h : X.Intent ref a w)
    (hc : a.Covers l) (hl : IsResponse L l) :
    (∃ g j pc p acq sc pcr bs, ref = .thread (g, j + 1) ∧ w = false ∧ l.cta = g / L.block ∧
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩) ∨
    (∃ h ki pci s tg, ref = .async (h, ki) (.write (.cta l.cta)) ∧
      X.get (h, ki) = some ⟨pci, .clcIssue s tg⟩ ∧ l.cta ∈ tg) := by
  rcases regions hpre hX ht h hc hl.1 with ⟨⟨-, h1, -⟩, -⟩ | ⟨⟨-, h1, -⟩, -⟩ |
      ⟨-, ⟨⟨g, k⟩, rfl, rfl⟩ | ⟨⟨h', ki⟩, s, tg, rfl, ⟨pci, hei⟩, hm⟩⟩ | ⟨⟨-, -, h2⟩, -⟩
  · exfalso; obtain ⟨-, -, h2⟩ := hl; omega
  · exfalso; obtain ⟨-, -, h2⟩ := hl; omega
  · left
    rcases h with ⟨bs, ⟨pc, hget⟩, -⟩ | ⟨bs, -, h'⟩ | ⟨old, new, pc, hget⟩
    rotate_right
    · exact (Safety.no_rmw hX ht hget).elim
    · have hg := Frame.lt_of_get hX hget
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
      obtain ⟨-, hct, hlo, hhi⟩ := hc
      rcases ht.read_poll hg hget hσ rfl with hb | ⟨hk, pcw, pw, acqw, scw, hew⟩
      · obtain ⟨-, h1, -⟩ := hl
        rcases (ht.access_region hg hget hσ).1 a bs rfl with ⟨hl', hs'⟩ | ⟨hl', hs'⟩
        · rw [hl'] at hb
          simp at hb
        · rw [hb, hs'] at hhi
          simp only at hhi
          omega
      · have hcta : l.cta = g / L.block := by
          rcases (ht.access_region hg hget hσ).1 a bs rfl with ⟨hl', -⟩ | ⟨hl', -⟩ <;>
            rw [hct, hl']
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact ⟨g, j, pcw, pw, acqw, scw, pc, bs, rfl, rfl, hcta, hew, hget⟩
    · cases h'
  · exact .inr ⟨h', ki, pci, s, tg, rfl, hei, hm⟩
  · exfalso; obtain ⟨-, h1, -⟩ := hl; omega

/-- **The CLC response buffer is ordered.** -/
theorem responseOrdered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ResponseOrdered L X := by
  have hv := readerValues hpre hX ht (responseWriters hpre hX ht)
  intro e f a b l hcon ha hb hl
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  have hcovW : ∀ {i : EvId} {c : Acc} {w : Bool} {C : Nat},
      X.Intent (.async i (.write (.cta C))) c w → c.Covers l →
        AsyncCovers X i (.write (.cta C)) l :=
    fun h hc => ⟨_, _, h, hc⟩
  rcases response_access hpre hX ht he ha hl with
      ⟨g, j, pc, p, acq, sc, pcr, bs, rfl, rfl, hlc, hpoll, hrd⟩ |
      ⟨h, ki, pci, s, tg, rfl, hei, hct⟩ <;>
    rcases response_access hpre hX ht hf hb hl with
      ⟨g', j', pc', p', acq', sc', pcr', bs', rfl, rfl, hlc', hpoll', hrd'⟩ |
      ⟨h', ki', pci', s', tg', rfl, hei', hct'⟩
  · rcases hw with h | h <;> cases h
  · rw [hlc] at hct' hf ⊢
    exact (read_write_ordered hpre hX ht hv hpoll hrd ⟨pci', hei'⟩ hct' (hcovW hf hb) hl.1
      hlc).symm
  · rw [hlc'] at hct he ⊢
    exact read_write_ordered hpre hX ht hv hpoll' hrd' ⟨pci, hei⟩ hct (hcovW he ha) hl.1 hlc'
  · obtain ⟨hp, hmb, -, -⟩ := issue_facts (c := l.cta / 2) hpre hX ht hei hct rfl
    obtain ⟨hp', hmb', -, -⟩ := issue_facts (c := l.cta / 2) hpre hX ht hei' hct' rfl
    have hh : h' = h := hp'.trans hp.symm
    subst hh
    rcases Nat.lt_trichotomy (issuesBefore L X (l.cta / 2) h' ki)
        (issuesBefore L X (l.cta / 2) h' ki') with hlt | heq | hgt
    · exact .inl (write_write_ordered hpre hX ht hv hei hei' hct hct' hlt (hcovW he ha)
        (hcovW hf hb))
    · exfalso
      apply hne
      rw [issues_inj (c := l.cta / 2) hei hei' (by simp [clcIssuesTo, hmb])
        (by simp [clcIssuesTo, hmb']) heq]
    · exact .inr (write_write_ordered hpre hX ht hv hei' hei hct' hct hgt (hcovW hf hb)
        (hcovW he ha))

end Region

end

end PTX.Kernels.Fp16Gemm8192.Proof
