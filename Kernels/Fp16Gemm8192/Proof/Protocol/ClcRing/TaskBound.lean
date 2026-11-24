-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Exit
public import Lemmas.Protocol.ClcOwner

@[expose] public section

/-! # The number of a cluster's tasks

The leader scheduler of a cluster requests again only after reading, for each earlier request, a
response that claims a CTA (`ThreadFacts.sched_issue`, `ReaderValues`). A claiming response is a
successful one, and it names a valid task, a cluster of the grid; two successful responses name
different tasks (`Clc.Owned.response_inj`). So a request has at most as many earlier requests as the
grid has clusters (`issues_le`). Every thread's `n`-th successful poll of its CTA's response barrier
observes the request with `n` earlier ones, so it polls successfully at most once more
(`polls_le`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A response that claims a CTA is a successful response, naming a valid task. -/
theorem claims_valid (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {i : EvId}
    {s : Clc.Spec} {tg : List Nat} (hi : X.ClcIssue i s tg) {r : ClcResponse}
    (hr : (X.clc i).resolved = some r) (hc : Loader.claims r) :
    ∃ t, X.clcState.response (Clc.requestId i) = some (some t) ∧ t < 512 := by
  obtain ⟨task, htask, rfl⟩ := (hX.clc.2.2.2.1 i s tg hi).1.result r hr
  cases task with
  | none => exact absurd hc (by simp [Loader.claims, Clc.responseOf])
  | some t =>
    have hv := (Clc.owned_of_reachable hX.clc.1).response_valid _ t htask
    have hlt := hv.2.1
    rw [hpre.oneDimLaunch.1.2.2.2.1, hpre.grid, hpre.cluster] at hlt
    exact ⟨t, htask, by omega⟩

/-- The leader's `n`-th earlier request, for `n` below a request's number, was answered with a
valid task. -/
theorem request_valid (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) {c ki pc : Nat} {sp : Clc.Spec}
    {tg : List Nat} (hei : X.get (producer L X c, ki) = some ⟨pc, .clcIssue sp tg⟩) {n : Nat}
    (hn : n < issuesBefore L X c (producer L X c) ki) :
    ∃ i t, (∃ s tg', X.ClcIssue i s tg') ∧ i.1 = producer L X c ∧ issuesBefore L X c i.1 i.2 = n ∧
      X.clcState.response (Clc.requestId i) = some (some t) ∧ t < 512 := by
  set h := producer L X c
  have hpsel : consumerSel L c 2 h = true := producer_sel hpre c
  simp only [consumerSel, decide_eq_true_eq] at hpsel
  have hhcta : h / L.block = 2 * c := by simpa [ctaOf] using hpsel.1
  have hh := Frame.lt_of_get hX hei
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hei (by simp)
  obtain ⟨b, hb, hby, -, -, -⟩ := (ht.ring_event hh hei hσ).clc _ _ rfl
  obtain ⟨rg, sl, f⟩ := b
  simp only [Bar.Valid] at hb
  cases rg <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
  obtain ⟨⟨sd, rfl⟩, -⟩ := hby
  obtain ⟨hcount, hreads⟩ := ht.sched_issue hh hei hσ rfl
  have hcnt : issuesBefore L X c h ki ≤
      okPolls (Bar.loc L (2 * c) ⟨.clc, 0, true⟩) ((X.tr h).take ki) := by
    unfold issuesBefore
    rw [← hhcta]
    exact hcount
  obtain ⟨w, pcw, pw, acqw, scw, hw, hew, hcw⟩ := nth_poll (X := X) (g := h) (j := ki)
    (m := Bar.loc L (2 * c) ⟨.clc, 0, true⟩) (o := n) (by omega)
  obtain ⟨pcr, src, bs, rr, hr, hfoot, hrr, hcl⟩ :=
    hreads w pcw pw acqw scw hw (by rw [hhcta]; exact hew)
  obtain ⟨i2, s2, tg2, r2, -, -, -, hord2, ho2, hres2, hbytes2⟩ :=
    hv c h w pcw pw acqw scw (by rw [hhcta]; omega) (by rw [hhcta]; exact hew)
  rw [hhcta] at hord2
  obtain rfl := read_response (hbytes2 pcr src bs hr hfoot) hrr
  obtain ⟨s2', tg2', hi2, hct2, -⟩ := ho2.2.2.choose_spec.clc
  obtain ⟨pc2, he2⟩ := hi2
  obtain ⟨hp2, -, -, -⟩ := issue_facts (c := c) hpre hX ht he2 hct2 (by rw [hhcta]; omega)
  obtain ⟨t, hres, htl⟩ := claims_valid hpre hX ⟨pc2, he2⟩ hres2 hcl
  refine ⟨i2, t, ⟨s2', tg2', pc2, he2⟩, hp2, ?_, hres, htl⟩
  rw [hp2]
  unfold issuesBefore
  rw [← hp2]
  exact hord2.trans hcw

/-- **A request has at most as many earlier requests as the grid has clusters.** -/
theorem issues_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) {c ki pc : Nat} {sp : Clc.Spec}
    {tg : List Nat} (hei : X.get (producer L X c, ki) = some ⟨pc, .clcIssue sp tg⟩) :
    issuesBefore L X c (producer L X c) ki ≤ 512 := by
  set n0 := issuesBefore L X c (producer L X c) ki
  have hex : ∀ n, n < n0 → ∃ t, ∃ i, (∃ s tg', X.ClcIssue i s tg') ∧ i.1 = producer L X c ∧
      issuesBefore L X c i.1 i.2 = n ∧ X.clcState.response (Clc.requestId i) = some (some t) ∧
      t < 512 := fun n hn => by
    obtain ⟨i, t, h⟩ := request_valid hpre hX ht hv hei hn
    exact ⟨t, i, h⟩
  let f : Nat → Nat := fun n => if hn : n < n0 then Classical.choose (hex n hn) else 0
  have hf : ∀ n (hn : n < n0), ∃ i, (∃ s tg', X.ClcIssue i s tg') ∧ i.1 = producer L X c ∧
      issuesBefore L X c i.1 i.2 = n ∧ X.clcState.response (Clc.requestId i) = some (some (f n)) ∧
      f n < 512 := fun n hn => by
    simp only [f, hn, ↓reduceDIte]
    exact Classical.choose_spec (hex n hn)
  have hmaps : Set.MapsTo f (Finset.range n0 : Set Nat) (Finset.range 512 : Set Nat) := by
    intro n hn
    obtain ⟨i, -, -, -, -, hlt⟩ := hf n (Finset.mem_range.mp hn)
    exact Finset.mem_range.mpr hlt
  have hinj : Set.InjOn f (Finset.range n0 : Set Nat) := by
    intro n hn m hm hnm
    obtain ⟨i, ⟨s, tg1, pci, hei1⟩, hpi, hni, hri, -⟩ := hf n (Finset.mem_range.mp hn)
    obtain ⟨j, ⟨s', tg2, pcj, hej⟩, hpj, hnj, hrj, -⟩ := hf m (Finset.mem_range.mp hm)
    rw [hnm] at hri
    have hid := (Clc.owned_of_reachable hX.clc.1).response_inj hri hrj
    simp only [Clc.requestId, Nat.pair_eq_pair] at hid
    obtain ⟨i1, i2⟩ := i
    obtain ⟨j1, j2⟩ := j
    simp only at hid hni hnj
    obtain ⟨rfl, rfl⟩ := hid
    exact hni.symm.trans hnj
  have := Finset.card_le_card_of_injOn f hmaps hinj
  simpa using this

/-- **Every thread polls its CTA's response barrier successfully at most once per task of its
cluster**: at most once more than the grid has clusters. -/
theorem polls_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) (g : Nat) :
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ≤ 513 := by
  by_contra hlt
  push Not at hlt
  have hlen : (X.tr g).take (X.tr g).length = X.tr g := List.take_length
  obtain ⟨w, pcw, pw, acqw, scw, -, hew, hcw⟩ := nth_poll (X := X) (g := g) (j := (X.tr g).length)
    (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (o := 513) (by rw [hlen]; omega)
  obtain ⟨i, s, tg, r, ⟨pci, hei⟩, hic, -, hord, ho, -, -⟩ :=
    hv (g / L.block / 2) g w pcw pw acqw scw rfl hew
  obtain ⟨s', tg', ⟨pc', he'⟩, hct', -⟩ := ho.2.2.choose_spec.clc
  rw [hei] at he'
  cases he'
  obtain ⟨hp, -, -, -⟩ := issue_facts (c := g / L.block / 2) hpre hX ht hei hct' rfl
  obtain ⟨i1, i2⟩ := i
  simp only at hp hei hord
  subst hp
  have hle := issues_le hpre hX ht hv hei
  unfold issuesBefore at hle
  omega

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
