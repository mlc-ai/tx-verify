-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The cluster launch control branches of `Unsafe`, from the interface

A vertical slice of `SafeGoal`: the CLC branches of `Unsafe` (`ClcUnsafe`), stated from the
thread facts and the CLC protocol's interface only.

* A request's response barrier lies in the launch's shared allocation of each target CTA
  (`clc_barrier_allocated`), and each target's barrier was initialized and published to the request
  (`barrier_published`). Both follow from `RingEvent.clc` (the request completes on the table's
  CLC barrier of the requester's CTA, targeting its cluster) and `ring_initialized`.
* The remaining branch needs the query facts. A failed `isCanceled` query in the requester's CTA
  must follow every request of that CTA. Every thread's query reports the response it read right
  after its latest successful poll (`ThreadFacts.clc_query`), and the leader stops requesting after
  reading a response that claims no CTA (`ThreadFacts.sched_issue`). The protocol layer proves
  `ReaderValues` (`ClcRing.readerValues`).

`failed_query_of_observed` below reduces the branch to `QueryInRole` (a query sits in a role state)
and `ReaderValues` (a read of a response right after a thread's successful poll returns the
response of the request that poll observed). `failed_query_safe` takes those query facts together
with the interface's `IssueBeforeObservers` and `RequestsBeforeFailure`; composing it with
`ClcRing.readerValues` needs a layer allowed to import both files. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A request comes from a scheduler state of its thread, on the CLC barrier of its CTA, and
targets CTAs of its cluster. -/
theorem request_source (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {i : EvId} {s : Clc.Spec} {tg : List Nat} (hi : X.ClcIssue i s tg) :
    ∃ sd, Frame.stateAt (code L) X i.1 i.2 = some (some (.inr (.sched sd))) ∧
      s.mbar = Bar.loc L (i.1 / L.block) ⟨.clc, 0, true⟩ ∧
      ∀ c ∈ tg, c / 2 = i.1 / L.block / 2 ∧ c < L.grid := by
  obtain ⟨pc, he⟩ := hi
  have hg : i.1 < L.threads := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨b, hb, hby, hmb, -, hcl⟩ := (ht.ring_event hg he hσ).clc _ _ rfl
  obtain ⟨rg, sl, f⟩ := b
  simp only [Bar.Valid] at hb
  cases rg <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
  obtain rfl : sl = 0 := by omega
  obtain ⟨⟨sd, rfl⟩, -⟩ := hby
  refine ⟨sd, hσ, hmb, fun c hc => ⟨hcl c hc, ?_⟩⟩
  exact ((hX.clc.2.2.2.1 i s tg ⟨pc, he⟩).2.2 c).mp hc |>.2.2.2.2.2.2.1

/-! ## The failure branch, reduced to the query facts it needs

The failed query `q` reports the response of a request `i'` that its own latest successful poll
observed (`ReaderValues`). `IssueBeforeObservers` puts `i'` before every later event of the
observer, so before `q`. `RequestsBeforeFailure` puts the request `i` of `q`'s CTA before `i'`
(or makes them equal), so `i` is before `q`, contradicting `¬ hb i q`. -/

/-- A request is issued by a leader CTA: the issuer's CTA is even. -/
theorem issuer_leader (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {i : EvId} {s : Clc.Spec} {tg : List Nat} (hi : X.ClcIssue i s tg) :
    i.1 / L.block % 2 = 0 := by
  obtain ⟨pc, he⟩ := hi
  have hg : i.1 < L.threads := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨b, hb, hby, -, -, -⟩ := (ht.ring_event hg he hσ).clc _ _ rfl
  obtain ⟨rg, sl, f⟩ := b
  simp only [Bar.Valid] at hb
  cases rg <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
  exact hby.2

/-- A request's target list contains its issuer's own CTA. -/
theorem issuer_mem (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i : EvId} {s : Clc.Spec} {tg : List Nat} (hi : X.ClcIssue i s tg) :
    i.1 / L.block ∈ tg := by
  obtain ⟨pc, he⟩ := hi
  have hg : i.1 < L.threads := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨b, -, -, hmb, hresp, -⟩ := (ht.ring_event hg he hσ).clc _ _ rfl
  have hblock : 0 < L.block := by rw [hpre.block]; decide
  refine ((hX.clc.2.2.2.1 i s tg ⟨pc, he⟩).2.2 (i.1 / L.block)).mpr ?_
  refine ⟨?_, hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch
  · simp [hresp]
  · simp [hmb, Bar.loc]
  · simp [hresp]
  · simp [hmb, Bar.loc]
  · exact (Nat.div_lt_iff_lt_mul hblock).2 (show i.1 < L.grid * L.block from hg)
  · cases s.multicast <;> simp

/-- The CLC query facts that the interface does not state yet. A query event sits in a role's
state: `ThreadFacts.clc_query` is given for role states only, and the prologue has no query site
(a code fact of the thread layer). -/
def QueryInRole (L : Launch) (X : Execution) : Prop :=
  ∀ (g k pc : Nat) (q : ClcQuery) (rr : ClcResponse), g < L.threads →
    X.get (g, k) = some ⟨pc, .clcQuery q rr⟩ → ∃ r, Frame.stateAt (code L) X g k =
      some (some (.inr r))

/-- Queries fire from role states (`ThreadFacts.query_role`). -/
theorem queryInRole (ht : ThreadFacts L X) : QueryInRole L X :=
  fun _ _ _ _ _ hg he => ht.query_role hg he

/-- The failure branch of `ClcUnsafe`, given the two query facts `QueryInRole` and
`ReaderValues`. -/
theorem failed_query_of_observed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hobs : IssueBeforeObservers L X) (hreq : RequestsBeforeFailure L X)
    (hrole : QueryInRole L X) (hquery : ReaderValues L X) :
    ¬ ∃ i s targets q pc r, X.ClcIssue i s targets ∧
      X.get q = some ⟨pc, .clcQuery .isCanceled r⟩ ∧ r.firstCta = none ∧
      SameCta L i.1 q.1 ∧ ¬ baseCausality L X i q := by
  rintro ⟨i, s, tg, ⟨g, k⟩, pc, r, hi, hq, hr, hsame, hnhb⟩
  have hk : k < (X.tr g).length := len_of_get hq
  have hgt : g < L.threads := Frame.lt_of_get hX hq
  obtain ⟨_r0, hσ⟩ := hrole g k pc .isCanceled r hgt hq
  obtain ⟨j, pc', p, acq, sc, pcr, src, bs, -, hk2, hw, hr1, hs, hres⟩ :=
    ht.clc_query hgt hq hσ rfl
  obtain ⟨i', -, -, rq, -, -, -, -, hobsv, hres', hread⟩ :=
    hquery (g / L.block / 2) g j pc' p acq sc rfl hw
  have hrq : rq = r := by
    rw [hread pcr src bs hr1 hs, PTX.Flow.responseOf_clc] at hres
    exact Option.some.inj hres
  rw [hrq] at hres'
  obtain ⟨s'', tg'', hi'', hmemo, -⟩ :=
    (show ClcObserved L X i' (g / L.block) (g, j) from hobsv).2.2.choose_spec.clc
  have hCi : i.1 / L.block = g / L.block := hsame.2.2
  have hpar_i : i.1 / L.block % 2 = 0 := issuer_leader hX ht hi
  have hmem_i : i.1 / L.block ∈ tg := issuer_mem hpre hX ht hi
  obtain ⟨-, -, -, hcl2⟩ := request_source hX ht hi''
  have hcta : i'.1 / L.block = g / L.block := by
    have hpar_o : i'.1 / L.block % 2 = 0 := issuer_leader hX ht hi''
    have hpar_g : g / L.block % 2 = 0 := by rw [← hCi]; exact hpar_i
    have h2 := (hcl2 _ hmemo).1
    omega
  have hobsv2 : ClcObserved L X i' (i'.1 / L.block) (g, j) := by
    rw [hcta]
    exact hobsv
  have hlen : j + 1 < (X.tr g).length := len_of_get hr1
  have hbi' : baseCausality L X i' (g, j + 1) :=
    hobs i' s'' tg'' (g, j) hi'' hobsv2 (j + 1) (Nat.lt_succ_self j) hlen
  have hpo : po X (g, j + 1) (g, k) :=
    po_of_not_access rfl (by show j + 1 < k; omega) hk (by simp [hq, Event.acc])
  have hbk : baseCausality L X i' (g, k) :=
    Relation.TransGen.trans hbi' (Relation.TransGen.single (Or.inl hpo))
  have hcl : ∃ c ∈ tg, ∃ c' ∈ tg'', c / 2 = c' / 2 :=
    ⟨i.1 / L.block, hmem_i, g / L.block, hmemo, by rw [hCi]⟩
  rcases hreq i s tg i' s'' tg'' r hi hi'' hcl hres' hr with rfl | hii'
  · exact hnhb hbk
  · exact hnhb (Relation.TransGen.trans hii' hbk)

/-- The failure branch of `ClcUnsafe` is excluded, from the protocol's query facts. -/
theorem failed_query_safe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hobs : IssueBeforeObservers L X) (hreq : RequestsBeforeFailure L X)
    (hquery : ReaderValues L X) :
    ¬ ∃ i s targets q pc r, X.ClcIssue i s targets ∧
      X.get q = some ⟨pc, .clcQuery .isCanceled r⟩ ∧ r.firstCta = none ∧
      SameCta L i.1 q.1 ∧ ¬ baseCausality L X i q :=
  failed_query_of_observed hpre hX ht hobs hreq (queryInRole ht) hquery

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
