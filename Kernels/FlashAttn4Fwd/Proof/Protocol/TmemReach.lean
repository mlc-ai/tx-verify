-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemReachContent

@[expose] public section

/-! # The reuse of the P-ready, S-full and O-full objects

The reuse paths of four object families are proved together, by well-founded induction along
the dependency order (`DepStep`, DEP-ORDER) over the issues of the thread events and their commit
notifications (`reach_all`, `induction_of_acyclic`): at each node, the paths ending there
(`Reach4`), knowing them at every node that precedes it.

* **S-full** (`stepS`): the notification of the commit of tile `t` follows each softmax
  poll for a tile `j < t`: the commit follows the committing lane's poll of phase `j` of the
  P-ready object (`mma_commit`), which observes the softmax's arrival of tile `j` (`contentP`),
  which follows its S-full poll of tile `j` (`soft_p`).
* **O-full** (`stepO`): the notification of the commit of item `I` follows each correction
  poll for an item `j < I`: the commit follows the poll of phase `n (j + 1)` of the P-ready object,
  which observes the correction's arrival of that credit, which follows its O-full poll of item
  `j` (`corr_p`).
* **P-ready** (`stepP`): a softmax arrival of tile `t` follows `t + 1` S-full polls
  (`soft_reach`). A correction arrival of credit `t ≥ 1` is a rescale's, after its statistics
  `bar.sync` of an ordinal whose softmax arrival follows `t + 1` S-full polls (`soft_gen`,
  `soft_partner`, `stats_rendezvous`: a witness of the `bar.sync`, then `soft_reach`), or a final
  pass's, after its O-full poll observing the commit of the item (`contentO`), which follows the
  committing lane's election at `n (I + 1) ≥ t` P-ready polls, where every lane of the MMA warp
  takes part (`lane_to_commit`).
* **second P-ready** (`stepP2`): a softmax arrival of tile `t` on it follows `t + 1` S-full
  polls (`P2Facts.p2_arrive`, then `soft_reach`).

Exports: `pReadyReach` (`PReadyReach`), `p2Reach` (`P2Reach`), `sFullReach` (`SFullReach`),
`oFullReach` (`OAcc.OFullReach`), under the premises `RouteCtx`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- An arrival of a pair's producer on its leader's object, in the form the thread facts name. -/
theorem arrive_lead {g i pc c st : Nat} {sc : MbarScope} (hc : leadCta (ctaOf L g) = c)
    (h : X.get (g, i) = some ⟨pc, .arrive (pReadyBar L c st) 0 1 true sc⟩) :
    X.get (g, i) = some ⟨pc, .arrive (pReadyBar L (leadCta (ctaOf L g)) st) 0 1 true sc⟩ := by
  rw [hc]
  exact h

/-- A producer's arrival of use `t`, at its thread. -/
theorem unit_it_eq {m : Loc} {N : Nat} {prod : Fin N → Nat} {a : Fin N} {h : Nat}
    (ha : h = prod a) (t : Nat) :
    MbarRing.Unit.it X m prod a t = (h, nthEv X (arrivesOn m) h t) := by
  subst ha
  rfl

set_option maxRecDepth 20000 in
/-- **The S-full step.** -/
theorem stepS (H : RouteCtx P L mem0 K A X) {n : Ref × Bool} (ih : IH L K X n) :
    RSn L K X n := by
  intro h hh hw y rank ⟨r, hr, hid, hf⟩ hn j hj
  subst hn
  have hX := H.cons
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
/-- **The O-full step.** -/
theorem stepO (H : RouteCtx P L mem0 K A X) {n : Ref × Bool} (ih : IH L K X n) :
    ROn L K X n := by
  intro h st hh h8 h12 hst y rank ⟨r, hr, hid, hf⟩ hn j hj
  subst hn
  have hX := H.cons
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

set_option maxRecDepth 20000 in
/-- **The P-ready step.** -/
theorem stepP (H : RouteCtx P L mem0 K A X) {n : Ref × Bool} (ih : IH L K X n) :
    RPn L K X n := by
  intro c st hc hst x hx hn h0 hh0 j hj
  subst hn
  have hX := H.cons
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (pObj H.pre hX H.pf H.tm H.pinit hc hst).S_rec hx
  set p := pThread L c st x.1 with hpdef
  set i := nthEv X (arrivesOn (pReadyBar L c st)) p x.2 with hidef
  change X.get (p, i) = _ at hga
  change arrivals _ ((X.tr p).take i) = x.2 at harr
  have hgp : p < L.threads := event_thread_lt hX hga
  have hlen : i < (X.tr p).length := len_of_get hga
  obtain ⟨hl, hrole, -⟩ := H.pf.p_arrive (g := p) (i := i) hgp hst hga
  show Relation.TransGen (DepStep L K X) _ (.thread (p, i), false)
  rcases hrole with ⟨hw, hws⟩ | ⟨h8, h12⟩
  · -- a softmax arrival of tile `x.2`
    have hsp := H.rt.soft_p (g := p) (i := i) hgp hw (by rw [hl, hws]; exact hga)
    unfold pArr at hsp
    rw [hl, hws, harr] at hsp
    exact (soft_reach H ih hst hh0 hgp hw hws hl hlen (by omega) .refl).1
  · -- a correction arrival of credit `x.2`
    obtain ⟨-, hq⟩ := H.rt.corr_p (h := p) (i := i) hgp h8 h12 hst (arrive_lead hl hga)
    have hpa : pArr L X p st i = x.2 := by unfold pArr; rw [hl]; exact harr
    rw [hpa] at hq
    rcases hq with hq | ⟨y, pcy, hyi, hyget, hG⟩ | ⟨jo, pco, po, acq, sco, hjo, hoget, hq⟩
    · omega
    · -- a rescale: the statistics partner's arrival follows `x.2 + 1` S-full polls
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
/-- **The second P-ready step.** -/
theorem stepP2 (H : RouteCtx P L mem0 K A X) {n : Ref × Bool} (ih : IH L K X n) :
    RP2n L K X n := by
  intro c st hc hst x hx hn h0 hh0 j hj
  subst hn
  have hX := H.cons
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (p2Obj H.pre hX H.p2 H.tm H.p2init hc hst).S_rec hx
  set p := p2Prod L X c st x.1 with hpdef
  set i := nthEv X (arrivesOn (pReady2Bar L c st)) p x.2 with hidef
  change X.get (p, i) = _ at hga
  change arrivals _ ((X.tr p).take i) = x.2 at harr
  have hgp : p < L.threads := event_thread_lt hX hga
  have hlen : i < (X.tr p).length := len_of_get hga
  obtain ⟨hl, hw, hws, -, -, -, -, hcnt, -⟩ := H.p2.p2_arrive (g := p) (k := i) hgp hst hga
  rw [harr] at hcnt
  show Relation.TransGen (DepStep L K X) _ (.thread (p, i), false)
  exact (soft_reach H ih hst hh0 hgp hw hws hl hlen
    (show j + 2 ≤ sPolls L X p st i by omega) .refl).2

/-- **The reuse paths of the four objects at every node.** -/
theorem reach_all (H : RouteCtx P L mem0 K A X) : ∀ n ∈ nodes L X, Reach4 L K X n :=
  induction_of_acyclic (DepStepAcyclic.of_dependency H.cons.dependency) (nodes L X) _
    (fun _ _ ih => ⟨stepP H ih, stepP2 H ih, stepS H ih, stepO H ih⟩)

set_option maxRecDepth 20000 in
/-- **PReadyReach.** -/
theorem pReadyReach (H : RouteCtx P L mem0 K A X) : PReadyReach L K A X := by
  intro c st hc hst h hh x hx j hj
  obtain ⟨-, ⟨pc, sc, hget⟩, -⟩ := (pObj H.pre H.cons H.pf H.tm H.pinit hc hst).S_rec hx
  exact (reach_all H _ (thread_mem H.cons hget)).1 c st hc hst x hx rfl h hh j hj

set_option maxRecDepth 20000 in
/-- **P2Reach.** -/
theorem p2Reach (H : RouteCtx P L mem0 K A X) : P2Reach L K A X := by
  intro c st hc hst h hh x hx j hj
  obtain ⟨-, ⟨pc, sc, hget⟩, -⟩ := (p2Obj H.pre H.cons H.p2 H.tm H.p2init hc hst).S_rec hx
  exact (reach_all H _ (thread_mem H.cons hget)).2.1 c st hc hst x hx rfl h hh j hj

/-- **SFullReach.** -/
theorem sFullReach (H : RouteCtx P L mem0 K A X) : SFullReach L K X := by
  intro h hh hw y rank ⟨r, hr, hid, hf⟩ j hj
  obtain ⟨pc, sp, hy, -⟩ := notify_rec H.cons hr hid
  exact (reach_all H _ (notify_mem H.cons rank hy)).2.2.1 h hh hw y rank ⟨r, hr, hid, hf⟩ rfl j hj

/-- **OFullReach.** -/
theorem oFullReach (H : RouteCtx P L mem0 K A X) : OAcc.OFullReach L K X := by
  intro h st hh h8 h12 hst y rank ⟨r, hr, hid, hf⟩ j hj
  obtain ⟨pc, sp, hy, -⟩ := notify_rec H.cons hr hid
  exact (reach_all H _ (notify_mem H.cons rank hy)).2.2.2 h st hh h8 h12 hst y rank
    ⟨r, hr, hid, hf⟩ rfl j hj

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
