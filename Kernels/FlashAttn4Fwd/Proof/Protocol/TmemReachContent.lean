-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemReachPath

@[expose] public section

/-! # The content of the polls inside the joint induction

The joint induction over dependency paths (`TmemReach`, `DepStep`) proves at each node `n` the
reuse paths of the P-ready, second P-ready, S-full and O-full objects that end at `n` (`Reach4`),
knowing them at every node that precedes `n` (`IH`). Inside it, a poll that precedes `n`, with
the polls of its thread before it, observes the units of its use (`contentP`, `contentS`,
`contentO`): the units
those polls observe precede `n`, so their reuse paths are the induction hypothesis
(`MbarRing.Multi.Obs.content_of_reach`).

**From an MMA lane's poll to a softmax event** (`soft_reach`): an MMA lane's poll of phase `j` of
either P-ready object of a stage precedes every softmax event of the stage in the pair with more
than `j + 1` S-full polls before it: the softmax's S-full poll of tile `j + 1` observes the commit
of tile `j + 1` (`contentS`), which follows the committing lane's election where it had polled
phase `j` of both objects (`RouteFacts.mma_commit`), and the lane takes part in that election at
the same P-ready counts (`lane_to_commit`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- The reuse paths of the P-ready objects that end at node `n`. -/
def RPn (L : Launch) (K : Kernel) (X : Execution) (n : Ref × Bool) :
    Prop :=
  ∀ c st, leadCta c = c → st < 2 → ∀ x ∈ MbarRing.Unit.S X (pReadyBar L c st) (pThread L c st),
    n = (.thread (MbarRing.Unit.it X (pReadyBar L c st) (pThread L c st) x.1 x.2), false) →
    ∀ h, mmaIn L c h → ∀ j < x.2, Relation.TransGen (DepStep L K X)
      (.thread (h, MbarRing.Poll.nth X (pReadyBar L c st) h (j + 0)), true) n

/-- The reuse paths of the second P-ready objects that end at node `n`. -/
def RP2n (L : Launch) (K : Kernel) (X : Execution) (n : Ref × Bool) :
    Prop :=
  ∀ c st, leadCta c = c → st < 2 →
    ∀ x ∈ MbarRing.Unit.S X (pReady2Bar L c st) (p2Prod L X c st),
    n = (.thread (MbarRing.Unit.it X (pReady2Bar L c st) (p2Prod L X c st) x.1 x.2), false) →
    ∀ h, mmaIn L c h → ∀ j < x.2, Relation.TransGen (DepStep L K X)
      (.thread (h, MbarRing.Poll.nth X (pReady2Bar L c st) h (j + 0)), true) n

/-- The reuse paths of the S-full objects that end at node `n`. -/
def RSn (L : Launch) (K : Kernel) (X : Execution) (n : Ref × Bool) :
    Prop :=
  ∀ h, h < L.threads → warpOf L h < 8 → ∀ (y : EvId) (rank : Fin 16),
    (∃ r ∈ X.objects (sFullBar L (ctaOf L h) (warpOf L h / 4)),
      r.id = .async y (.tcNotify rank) ∧ r.fault = none) →
    n = (.async y (.tcNotify rank), false) →
    ∀ j < sCommits L X y.1 (warpOf L h / 4) y.2, Relation.TransGen (DepStep L K X)
      (.thread (h, MbarRing.Poll.nth X (sFullBar L (ctaOf L h) (warpOf L h / 4)) h j), true) n

/-- The reuse paths of the O-full objects that end at node `n`. -/
def ROn (L : Launch) (K : Kernel) (X : Execution) (n : Ref × Bool) :
    Prop :=
  ∀ h st, h < L.threads → 8 ≤ warpOf L h → warpOf L h < 12 → st < 2 →
    ∀ (y : EvId) (rank : Fin 16), (∃ r ∈ X.objects (oFullBar L (ctaOf L h) st),
      r.id = .async y (.tcNotify rank) ∧ r.fault = none) →
    n = (.async y (.tcNotify rank), false) →
    ∀ j < OAcc.oCommits L X y.1 st y.2, Relation.TransGen (DepStep L K X)
      (.thread (h, MbarRing.Poll.nth X (oFullBar L (ctaOf L h) st) h j), true) n

/-- The reuse paths of the four objects that end at node `n`. -/
def Reach4 (L : Launch) (K : Kernel) (X : Execution) (n : Ref × Bool) :
    Prop :=
  RPn L K X n ∧ RP2n L K X n ∧ RSn L K X n ∧ ROn L K X n

/-- The induction hypothesis at node `n`. -/
def IH (L : Launch) (K : Kernel) (X : Execution) (n : Ref × Bool) :
    Prop :=
  ∀ p ∈ nodes L X, Relation.TransGen (DepStep L K X) p n → Reach4 L K X p

set_option maxRecDepth 20000 in
/-- **The content of an MMA lane's P-ready poll** that precedes `n`. -/
theorem contentP (H : RouteCtx P L mem0 K A X) {n : Ref × Bool} (ih : IH L K X n)
    {c st y J : Nat} (hc : leadCta c = c) (hst : st < 2) (hy : mmaIn L c y)
    (hJ : J < okPolls (pReadyBar L c st) (X.tr y))
    (hpath : Relation.TransGen (DepStep L K X)
      (.thread (y, MbarRing.Poll.nth X (pReadyBar L c st) y J), true) n) (a : Fin 512) :
    (a, J) ∈ MbarRing.Unit.S X (pReadyBar L c st) (pThread L c st) ∧
      Witness L X (.thread (MbarRing.Unit.it X (pReadyBar L c st) (pThread L c st) a J))
        (y, MbarRing.Poll.nth X (pReadyBar L c st) y J) := by
  have O := pObj H.pre H.cons H.pf H.tm H.pinit hc hst
  obtain ⟨t, hS, hu, hobs⟩ :=
    (O.obs H.cons y).content_of_reach (DepStepAcyclic.of_dependency H.cons.dependency)
    (J := J) (n := n) (MbarRing.Poll.nth_present.mpr hJ)
    (fun j hj => MbarRing.Poll.enables_earlier H.spin hj hJ hpath)
    (fun x hx hxn j hj => by
      change x ∈ MbarRing.Unit.S X (pReadyBar L c st) (pThread L c st) at hx
      obtain ⟨-, ⟨pc, sc, hget⟩, -⟩ := O.S_rec hx
      exact (ih _ (thread_mem H.cons hget) hxn).1 c st hc hst x hx rfl y hy j hj) a
  change t = J at hu
  subst hu
  change (a, t) ∈ MbarRing.Unit.S X (pReadyBar L c st) (pThread L c st) at hS
  exact ⟨hS, hobs⟩

/-- **The content of a softmax thread's S-full poll** that precedes `n`. -/
theorem contentS (H : RouteCtx P L mem0 K A X) {n : Ref × Bool} (ih : IH L K X n)
    {g J : Nat} (hg : g < L.threads) (hw : warpOf L g < 8)
    (hJ : J < okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) (X.tr g))
    (hpath : Relation.TransGen (DepStep L K X)
      (.thread (g, MbarRing.Poll.nth X (sFullBar L (ctaOf L g) (warpOf L g / 4)) g J), true) n) :
    ∃ (y : EvId) (pc : Nat) (sp : TcCommit.Spec) (rank : Fin 16),
      X.get y = some ⟨pc, .tc (.commit sp)⟩ ∧
      sp.mbar = sFullBar L (ctaOf L y.1) (warpOf L g / 4) ∧
      sCommits L X y.1 (warpOf L g / 4) y.2 = J ∧
      leadCta (ctaOf L y.1) = leadCta (ctaOf L g) ∧ rank ∈ X.tcNotified y ∧
      Witness L X (.async y (.tcNotify rank))
        (g, MbarRing.Poll.nth X (sFullBar L (ctaOf L g) (warpOf L g / 4)) g J) := by
  have hst : warpOf L g / 4 < 2 := by omega
  have hX := H.cons
  obtain ⟨G, O⟩ := fullObj hX H.tm H.scom hst (H.sinit _ _ hst) (H.sf.s_arrive hst)
    (H.sf.s_tensor hst) (fun he => (H.sf.s_poll (event_thread_lt hX he) hst he).2.2.2.1)
  obtain ⟨t, hS, hu, hobs⟩ :=
    (O.obs hX g).content_of_reach (DepStepAcyclic.of_dependency hX.dependency)
    (J := J) (n := n) (MbarRing.Poll.nth_present.mpr hJ)
    (fun j hj => MbarRing.Poll.enables_earlier H.spin hj hJ hpath)
    (fun x hx hxn j hj => by
      obtain ⟨⟨k, r, hk, hid, hf, -⟩, pc, sp, hget, -, -, hcnt⟩ := O.S_rec hx
      exact (ih _ (notify_mem hX _ hget) hxn).2.2.1 g hg hw _ _
        ⟨r, List.mem_of_getElem? hk, hid, hf⟩ rfl j (lt_of_lt_of_eq hj hcnt.symm)) 0
  change t = J at hu
  subst hu
  obtain ⟨⟨k, r, hk, hid, -, -⟩, pc, sp, hget, hm, ht, hcnt⟩ := O.S_rec hS
  have hp := object_record_present hX.tma (List.mem_of_getElem? hk)
  rw [hid] at hp
  exact ⟨_, pc, sp, _, hget, hm, hcnt, commit_lead H hget (.inl ht), hp, hobs⟩

/-- **The content of a correction thread's O-full poll** that precedes `n`. -/
theorem contentO (H : RouteCtx P L mem0 K A X) {n : Ref × Bool} (ih : IH L K X n)
    {g st J : Nat} (hg : g < L.threads) (h8 : 8 ≤ warpOf L g) (h12 : warpOf L g < 12)
    (hst : st < 2) (hJ : J < okPolls (oFullBar L (ctaOf L g) st) (X.tr g))
    (hpath : Relation.TransGen (DepStep L K X)
      (.thread (g, MbarRing.Poll.nth X (oFullBar L (ctaOf L g) st) g J), true) n) :
    ∃ (y : EvId) (pc : Nat) (sp : TcCommit.Spec) (rank : Fin 16),
      X.get y = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = oFullBar L (ctaOf L y.1) st ∧
      OAcc.oCommits L X y.1 st y.2 = J ∧
      leadCta (ctaOf L y.1) = leadCta (ctaOf L g) ∧ rank ∈ X.tcNotified y ∧
      Witness L X (.async y (.tcNotify rank))
        (g, MbarRing.Poll.nth X (oFullBar L (ctaOf L g) st) g J) := by
  have hX := H.cons
  obtain ⟨G, O⟩ := fullObj hX H.tm H.ocom hst (H.oinit _ _ hst) (H.ofa.o_arrive hst)
    (H.ofa.o_tensor hst) (fun he => (H.ofa.o_poll (event_thread_lt hX he) hst he).2.2.2.1)
  obtain ⟨t, hS, hu, hobs⟩ :=
    (O.obs hX g).content_of_reach (DepStepAcyclic.of_dependency hX.dependency)
    (J := J) (n := n) (MbarRing.Poll.nth_present.mpr hJ)
    (fun j hj => MbarRing.Poll.enables_earlier H.spin hj hJ hpath)
    (fun x hx hxn j hj => by
      obtain ⟨⟨k, r, hk, hid, hf, -⟩, pc, sp, hget, -, -, hcnt⟩ := O.S_rec hx
      exact (ih _ (notify_mem hX _ hget) hxn).2.2.2 g st hg h8 h12 hst _ _
        ⟨r, List.mem_of_getElem? hk, hid, hf⟩ rfl j (lt_of_lt_of_eq hj hcnt.symm)) 0
  change t = J at hu
  subst hu
  obtain ⟨⟨k, r, hk, hid, -, -⟩, pc, sp, hget, hm, ht, hcnt⟩ := O.S_rec hS
  have hp := object_record_present hX.tma (List.mem_of_getElem? hk)
  rw [hid] at hp
  exact ⟨_, pc, sp, _, hget, hm, hcnt, commit_lead H hget (.inr ht), hp, hobs⟩

/-- **From an MMA lane's poll to a softmax event**: the lane's poll of phase `j` of either P-ready
object of stage `st` precedes every softmax event of the stage in the pair with more than `j + 1`
S-full polls before it, and what that event precedes. -/
theorem soft_reach (H : RouteCtx P L mem0 K A X) {n : Ref × Bool} (ih : IH L K X n)
    {c st h0 j g e : Nat} (hst : st < 2) (h0c : mmaIn L c h0)
    (hg : g < L.threads) (hw : warpOf L g < 8) (hgs : warpOf L g / 4 = st)
    (hgc : leadCta (ctaOf L g) = c) (he : e < (X.tr g).length)
    (hs : j + 2 ≤ sPolls L X g st e)
    (hn : Relation.ReflTransGen (DepStep L K X) (.thread (g, e), false) n) :
    Relation.TransGen (DepStep L K X)
        (.thread (h0, MbarRing.Poll.nth X (pReadyBar L c st) h0 j), true) n ∧
      Relation.TransGen (DepStep L K X)
        (.thread (h0, MbarRing.Poll.nth X (pReady2Bar L c st) h0 j), true) n := by
  subst hgs
  obtain ⟨hh0, rfl, hh12⟩ := h0c
  have hs' : j + 1 + 1 ≤ okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take e) :=
    hs
  have hpoll := (Relation.TransGen.single (poll_guard H he hs')).trans_left hn
  obtain ⟨y, pc, sp, rank, hy, hm, hcnt, hlead, hr, hobs⟩ :=
    contentS H ih hg hw (poll_lt he.le hs') hpoll
  obtain ⟨hY, hY12, hYl, k, pck, inst, l, hk, hel, hS, -⟩ :=
    H.rt.mma_commit ⟨pc, hy⟩ hst (.inl hm)
  obtain ⟨hP, hP2⟩ := hS hm
  obtain ⟨eh, hehl, hp1, hp2, hpath⟩ := lane_to_commit H hY hY12 hel hk (len_of_get hy) hh0
    hh12 (by rw [← hYl, hlead, hgc]) hst
  have htail : Relation.TransGen (DepStep L K X) (.thread (h0, eh), false) n :=
    hpath.trans (((Relation.TransGen.single (commit_notify hy hr)).tail
      (DepStep.of_witness L hobs)).trans hpoll)
  refine ⟨.head (poll_guard H hehl ?_) htail, .head (poll_guard H hehl ?_) htail⟩
  · change j + 1 ≤ pPolls L X h0 (warpOf L g / 4) eh
    omega
  · change j + 1 ≤ p2Polls L X h0 (warpOf L g / 4) eh
    omega

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
