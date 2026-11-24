-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Values
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Kernel.SharedLifetime
public import Lemmas.Kernel.ExitChain

@[expose] public section

/-! # The exit protocol

A CTA's first consumer thread (warp 0, lane 0) is a selected reader of its cluster's response
ring, and it exits only after reading a response that claims no CTA (`ThreadFacts.consumer_exit`).
That response is the cluster's request numbered by the reader's successful polls (`ReaderValues`).
The leader scheduler reads every response before requesting again and stops after one that claims
no CTA (`ThreadFacts.sched_issue`), so every request is numbered at most that one. The reader
therefore observed every request before exiting, and each request's notification of its CTA
finished before that exit (`exitNotified`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The selector of a CTA's first consumer thread. -/
def firstSel (c : Nat) : Fin 10 := if c % 2 = 0 then 6 else 8

/-- The response a read decodes to is the one `ReaderValues` gives for it. -/
theorem read_response {r rr : ClcResponse} {bs : List (Option Byte)}
    (hb : bs = (Value.clc r).toBytes.map some) (hr : Flow.responseOf bs = some rr) : rr = r := by
  rw [hb, responseOf_clc] at hr
  exact (Option.some.inj hr).symm

/-- The requests of cluster `c`'s leader, numbered by its earlier requests, are at most the
number of a response that claims no CTA. -/
theorem issues_le_failed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) {c ki pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    {cta : Nat} (hei : X.get (producer L X c, ki) = some ⟨pc, .clcIssue sp tg⟩) (hct : cta ∈ tg)
    (hcc : cta / 2 = c) {i : EvId} {s : Clc.Spec} {tg' : List Nat} {r : ClcResponse}
    (hi : X.ClcIssue i s tg') (hcta' : ∃ c' ∈ tg', c' / 2 = c) (hres : (X.clc i).resolved = some r)
    (hfail : ¬ Loader.claims r) :
    issuesBefore L X c (producer L X c) ki ≤ issuesBefore L X c i.1 i.2 := by
  have hblock := hpre.block
  set h := producer L X c
  have hpsel : consumerSel L c 2 h = true := producer_sel hpre c
  have hpsel1 := hpsel
  simp only [consumerSel, decide_eq_true_eq] at hpsel1
  have hhcta : h / L.block = 2 * c := by simpa [ctaOf] using hpsel1.1
  have hh := Frame.lt_of_get hX hei
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hei (by simp)
  obtain ⟨b, hb, hby, -, -, -⟩ := (ht.ring_event hh hei hσ).clc _ _ rfl
  obtain ⟨rg, sl, f⟩ := b
  simp only [Bar.Valid] at hb
  cases rg <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
  obtain ⟨⟨sd, rfl⟩, -⟩ := hby
  obtain ⟨hcount, hreads⟩ := ht.sched_issue hh hei hσ rfl
  obtain ⟨hpi, hmb, -, -⟩ := issue_facts (c := c) hpre hX ht hei hct hcc
  obtain ⟨⟨hi1, hi2⟩, pci', hei'⟩ : (i.1, i.2) = i ∧ ∃ pc', X.get (i.1, i.2) =
    some ⟨pc', .clcIssue s tg'⟩ := by
    obtain ⟨pc', he'⟩ := hi
    exact ⟨rfl, pc', he'⟩
  obtain ⟨c', hc', hcc'⟩ := hcta'
  obtain ⟨hpi', hmb', -, -⟩ := issue_facts (c := c) hpre hX ht hei' hc' hcc'
  by_contra hlt
  push Not at hlt
  -- the leader polled the response numbered `issuesBefore i` before this request
  have hcnt : issuesBefore L X c h ki ≤
      okPolls (Bar.loc L (2 * c) ⟨.clc, 0, true⟩) ((X.tr h).take ki) := by
    unfold issuesBefore
    rw [← hhcta]
    exact hcount
  obtain ⟨w, pcw, pw, acqw, scw, hw, hew, hcw⟩ := nth_poll (X := X) (g := h) (j := ki)
    (m := Bar.loc L (2 * c) ⟨.clc, 0, true⟩) (o := issuesBefore L X c i.1 i.2) (by omega)
  obtain ⟨pcr, src, bs, rr, hr, hfoot, hrr, hcl⟩ :=
    hreads w pcw pw acqw scw hw (by rw [hhcta]; exact hew)
  obtain ⟨i2, s2, tg2, r2, -, -, -, hord2, ho2, hres2, hbytes2⟩ :=
    hv c h w pcw pw acqw scw (by rw [hhcta]; omega) (by rw [hhcta]; exact hew)
  rw [hhcta] at hord2
  have hb2 := hbytes2 pcr src bs hr hfoot
  obtain rfl := read_response hb2 hrr
  -- that response is the one `i` resolved, by the numbering of requests
  obtain ⟨s2', tg2', ⟨pc2, he2⟩, hct2, -⟩ := ho2.2.2.choose_spec.clc
  obtain ⟨hp2, hmb2, -, -⟩ := issue_facts (c := c) hpre hX ht he2 hct2 (by rw [hhcta]; omega)
  have hiq : i2 = i := by
    obtain ⟨i21, i22⟩ := i2
    simp only at hp2 he2 hord2
    have h1 : i21 = i.1 := hp2.trans hpi'.symm
    subst h1
    have := issues_inj (L := L) (c := c) he2 hei' (by simp [clcIssuesTo, hmb2])
      (by simp [clcIssuesTo, hmb']) (hord2.trans hcw)
    rw [this]
  subst hiq
  rw [hres] at hres2
  cases hres2
  exact hfail hcl

/-- **The exit protocol.** -/
theorem exitNotified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) : ExitNotified L X := by
  intro ⟨h, ki⟩ s tg c ⟨pci, hei⟩ hct hexit
  have hblock := hpre.block
  have hgrid := hpre.grid
  set cl := c / 2 with hcl
  obtain ⟨hp, hmb, -, -⟩ := issue_facts (c := cl) hpre hX ht hei hct rfl
  have hcg : c < L.grid :=
    ((hX.clc.2.2.2.1 (h, ki) s tg ⟨pci, hei⟩).2.2 c).mp hct |>.2.2.2.2.2.2.1
  -- the CTA's first consumer thread and its exit
  set g0 := c * L.block with hg0
  have hg0t : g0 < L.threads := by
    simp only [Launch.threads, hg0, hblock] at *; omega
  have hg0c : g0 / L.block = c := by simp only [hg0, hblock]; omega
  obtain ⟨pcx, hlast⟩ := hexit g0 hg0t hg0c
  have hlen : (X.tr g0).length - 1 < (X.tr g0).length := by
    have := List.getLast?_eq_some_iff.mp hlast
    obtain ⟨ys, hys⟩ := this
    rw [hys]; simp
  set k0 := (X.tr g0).length - 1
  have hex : X.get (g0, k0) = some ⟨pcx, .exit⟩ := by
    change (X.tr g0)[k0]? = _
    rw [← List.getLast?_eq_getElem?]; exact hlast
  obtain ⟨d0, hσ0⟩ := Frame.event_state ht.sound hX ht.tracked hex (by simp)
  obtain ⟨jf, pcf, pf, acqf, scf, pcr, src, bs, rr, hjf, hwf, hrf, hfoot, hrr, hfail⟩ :=
    ht.consumer_exit hg0t hex hσ0 rfl (by simp only [hg0, hblock]; omega)
  have hcta0 : g0 / L.block = 2 * cl + ctaOf (firstSel c) := by
    rw [hg0c]; simp only [firstSel]; split_ifs <;> simp [ctaOf] <;> omega
  have hg0cl : g0 / L.block / 2 = cl := by rw [hg0c, hcl]
  obtain ⟨i_f, s_f, tg_f, r_f, -, -, -, hord_f, ho_f, hres_f, hbytes_f⟩ :=
    hv cl g0 jf pcf pf acqf scf hg0cl hwf
  rw [hcta0] at hord_f
  obtain rfl := read_response (hbytes_f pcr src bs hrf hfoot) hrr
  -- every request is numbered at most the failed one
  obtain ⟨s_f', tg_f', hif, hct_f, -⟩ := ho_f.2.2.choose_spec.clc
  have hle := issues_le_failed hpre hX ht hv (c := cl) (hp ▸ hei) hct rfl hif
    ⟨_, hct_f, hg0cl⟩ hres_f hfail
  rw [← hp] at hle
  have hord' : issuesBefore L X cl h ki <
    okPolls (Bar.loc L (2 * cl + ctaOf (firstSel c)) ⟨.clc, 0, true⟩)
      ((X.tr g0).take (jf + 1)) := by
    have h1 : issuesBefore L X cl i_f.1 i_f.2 =
        okPolls (Bar.loc L (2 * cl + ctaOf (firstSel c)) ⟨.clc, 0, true⟩) ((X.tr g0).take jf) :=
      hord_f
    rw [Flow.okPolls, List.take_add_one, List.countP_append]
    have : (X.tr g0)[jf]? =
      some ⟨pcf, .wait (Bar.loc L (2 * cl + ctaOf (firstSel c)) ⟨.clc, 0, true⟩)
        pf true acqf scf⟩ := by rw [← hcta0]; exact hwf
    rw [this]
    simp only [Option.toList_some, List.countP_singleton]
    rw [okPoll_wait rfl]
    simp only [Bool.true_and, decide_true, ↓reduceIte]
    change _ < okPolls _ _ + 1
    omega
  -- the reader's poll numbered by this request observed it
  obtain ⟨jo, pco, po, acqo, sco, hjo, heo, hco⟩ := nth_poll hord'
  obtain ⟨i_o, s_o, tg_o, -, -, -, -, hord_o, ho_o, -, -⟩ :=
    hv cl g0 jo pco po acqo sco hg0cl (by rw [hcta0]; exact heo)
  rw [hcta0] at hord_o
  have hiq : i_o = (h, ki) := by
    obtain ⟨s_o', tg_o', ⟨pc_o, he_o⟩, hct_o, -⟩ := ho_o.2.2.choose_spec.clc
    obtain ⟨hp_o, hmb_o, -, -⟩ := issue_facts (c := cl) hpre hX ht he_o hct_o hg0cl
    obtain ⟨i1, i2⟩ := i_o
    simp only at hp_o he_o hord_o
    have h1 : i1 = h := hp_o.trans hp.symm
    subst h1
    have := issues_inj (L := L) (c := cl) he_o hei (by simp [clcIssuesTo, hmb_o])
      (by simp [clcIssuesTo, hmb]) (hord_o.trans hco)
    rw [this]
  subst hiq
  obtain ⟨-, -, wso, hobo⟩ := ho_o
  obtain ⟨s', tg', hi', -, hnot, hbefore⟩ := hobo.clc
  have hbefore := hbefore.before
  rw [hg0c] at hnot hbefore
  refine ⟨hnot, (g0, k0), pcx, hg0t, hg0c, hex, ?_⟩
  obtain ⟨ex, hspin⟩ := ht.wait_spins (Frame.lt_of_get hX heo) heo
  exact CompletedBefore.of_before hbefore
    (.single (DepStep.of_resumes L (Resumes.of_spin heo hspin rfl (by omega) hlen)))

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
