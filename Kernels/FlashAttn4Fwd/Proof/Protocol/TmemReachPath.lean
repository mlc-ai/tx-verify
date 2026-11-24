-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.OFullHandoff
public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Obj
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsCreditGate
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute
public import Lemmas.Protocol.MultiObs
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # The edges of the routes through the Tensor Memory objects

The dependency paths (`DepStep`, DEP-ORDER) of the reuse of the P-ready, second P-ready, S-full
and O-full objects (`TmemReach`) and the routes of the correction's loads (`ORoute`) are made of
these edges, under the premises gathered in `RouteCtx`:

* **lane to commit** (`lane_to_commit`): a lane of the MMA warp takes part in the full-mask
  election before a commit of the warp's committing lane (DEP-WARP-ELECT), at the election of the
  same ordinal (`ElectOrdinal`), where it has polled the P-ready objects as often (`mma_elect`); its
  election precedes the commit (`elect_depStep`);
* **commit to notification** (`commit_notify`): the issue of a commit precedes its recorded
  notification;
* **statistics partner** (`soft_partner`, `stats_rendezvous`): a correction thread's passed
  `bar.sync` on its statistics barrier has a softmax lane of the partner warp with its arrival of
  the same ordinal (`Stats.SoftArrives`), counted by the release the `bar.sync` waits for, so a
  witness of its return (`Witness.of_ctaBarCounted`);
* **commit records** (`notify_rec`): a record of a notification is a commit's, present. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof CtaBarrier
open AsyncCopy

noncomputable section

namespace Score

/-- The premises of the routes through the Tensor Memory objects. -/
structure RouteCtx (P : Params) (L : Launch) (mem0 : Mem0) (K : Kernel) (A : List Assumption)
    (X : Execution) : Prop where
  pre : Pre P L mem0
  cons : Consistent L K A mem0 X
  rt : RouteFacts L X
  pf : PReadyFacts L X
  p2 : P2Facts L X
  sf : SFullFacts L X
  ofa : OFullFacts L X
  stf : StatsFacts L X
  tm : TmemFacts L X
  ini : InitFacts L X
  pinit : PReadyInit L X
  p2init : P2Init L X
  sinit : SFullInit L X
  oinit : OFullInit L X
  scom : FullCommit L X (sFullBar L)
  ocom : FullCommit L X (oFullBar L)
  soft : Stats.SoftArrives L X
  spin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  /-- Every election uses the full mask (each `elect.sync` of the kernel names `-1`). -/
  efull : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l → mask = fullMask

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- The elections of one instance in one warp have one ordinal (`electOrdinal`). -/
theorem RouteCtx.eord (H : RouteCtx P L mem0 K A X) : ElectOrdinal L X :=
  electOrdinal H.cons (ElectMutual.of_full H.efull)

/-- A spinning successful poll resumes each later event with more successful polls before it. -/
theorem poll_guard (H : RouteCtx P L mem0 K A X) {g k n : Nat} {m : Loc}
    (hk : k < (X.tr g).length) (h : n + 1 ≤ okPolls m ((X.tr g).take k)) :
    DepStep L K X (.thread (g, MbarRing.Poll.nth X m g n), true) (.thread (g, k), false) :=
  DepStep.of_resumes L (MbarRing.Poll.guard H.spin hk h)

/-- A thread with more than `n` successful polls of `m` before an event made the poll with `n`
earlier ones. -/
theorem poll_lt {g k n : Nat} {m : Loc} (hk : k ≤ (X.tr g).length)
    (h : n + 1 ≤ okPolls m ((X.tr g).take k)) : n < okPolls m (X.tr g) := by
  have := MbarRing.Poll.okPolls_mono m (X.tr g) hk
  rw [List.take_of_length_le (le_refl _)] at this
  omega

/-- **The issue of a commit precedes its notification.** -/
theorem commit_notify {y : EvId} {pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (hy : X.get y = some ⟨pc, .tc (.commit sp)⟩) (hr : rank ∈ X.tcNotified y) :
    DepStep L K X (.thread y, false) (.async y (.tcNotify rank), false) :=
  DepStep.issue ⟨_, hy⟩ hr (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)

/-- **A record of a notification is a present commit's** targeting the object. -/
theorem notify_rec (hX : Consistent L K A mem0 X) {m : Loc} {r : MBarrier.Record Ref}
    {y : EvId} {rank : Fin 16} (hr : r ∈ X.objects m) (hid : r.id = .async y (.tcNotify rank)) :
    ∃ pc sp, X.get y = some ⟨pc, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m ∧
      rank ∈ X.tcNotified y := by
  have hp := object_record_present hX.tma hr
  rw [hid] at hp
  cases record_source hX.tma.2.2.1 hr with
  | init hid' => rw [hid] at hid'; cases hid'
  | inval hid' => rw [hid] at hid'; cases hid'
  | arrive hid' => rw [hid] at hid'; cases hid'
  | wait hid' => rw [hid] at hid'; cases hid'
  | tensor hid' => rw [hid] at hid'; cases hid'
  | increment hid' => rw [hid] at hid'; cases hid'
  | arriveOn hid' => rw [hid] at hid'; cases hid'
  | bulk hid' => rw [hid] at hid'; cases hid'
  | clc hid' => rw [hid] at hid'; cases hid'
  | commit hid' he ht =>
    rw [hid] at hid'
    cases hid'
    exact ⟨_, _, he, ht, hp⟩

/-- A commit notifying a stage's object of a pair's CTA is of a thread of the pair. -/
theorem commit_lead (H : RouteCtx P L mem0 K A X) {y : EvId} {pc st c : Nat}
    {sp : TcCommit.Spec} {rank : Fin 16} (hy : X.get y = some ⟨pc, .tc (.commit sp)⟩)
    (hb : TcCommit.target sp rank = some (sFullBar L c st) ∨
      TcCommit.target sp rank = some (oFullBar L c st)) :
    leadCta (ctaOf L y.1) = leadCta c := by
  rcases hb with ht | ht
  · have hcl := H.ini.commit_cluster hy ht
    simp only [sFullBar] at hcl
    unfold leadCta
    omega
  · have hcl := H.ini.commit_cluster hy ht
    simp only [oFullBar] at hcl
    unfold leadCta
    omega

/-- **Lane to commit**: a lane of the committing lane's warp has an election, with as many
P-ready polls before it as the committing lane's election, that precedes each later event of the
committing lane in the dependency order. -/
theorem lane_to_commit (H : RouteCtx P L mem0 K A X) {Y k pc inst l f h st : Nat}
    (hY : Y < L.threads) (hY12 : warpOf L Y = 12)
    (hel : X.Elect (Y, k) pc fullMask inst l) (hkf : k < f) (hf : f < (X.tr Y).length)
    (hh : h < L.threads) (hh12 : warpOf L h = 12) (hc : ctaOf L h = ctaOf L Y) (hst : st < 2) :
    ∃ e, e < (X.tr h).length ∧ pPolls L X h st e = pPolls L X Y st k ∧
      p2Polls L X h st e = p2Polls L X Y st k ∧
      Relation.TransGen (DepStep L K X) (.thread (h, e), false) (.thread (Y, f), false) := by
  have hX := H.cons
  have hwY : SameWarp L Y h := ⟨⟨hY, hh, by unfold ctaOf at hc; exact hc.symm⟩, by
    unfold warpOf at hY12 hh12; omega⟩
  -- the election returned, so lane `h`'s election of its instance is one of its filled needs
  obtain ⟨e, pc0, pc', mask0, mask', inst', l0, l', hel0, hel'⟩ :=
    ElectOrd.partner hX hwY hel (electMember_full (Nat.mod_lt _ (by decide)))
  have hinst : inst = inst' := by
    have h0 : X.get (Y, k) = some ⟨pc0, .elect mask0 inst' l0⟩ := hel0
    have h1 : X.get (Y, k) = some ⟨pc, .elect fullMask inst l⟩ := hel
    rw [h1] at h0
    simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at h0
    exact h0.2.2.1
  subst hinst
  have hord := H.eord (e := (Y, k)) (f := (h, e)) hwY hel hel'
  obtain ⟨h1, h2⟩ := H.rt.mma_elect hY hY12 hwY hst hel hel' hord
  exact ⟨e, len_of_get hel', h1.symm, h2.symm,
    elect_depStep hX (sameWarp_symm hwY) hel' hel hkf hf⟩

/-- The softmax lane of the partner warp of a correction thread's statistics barrier. -/
def partnerLane (L : Launch) (p st : Nat) : Nat :=
  ctaOf L p * L.block + 32 * (warpOf L p - 8 + 4 * st)

/-- **The statistics partner**: a correction thread's passed `bar.sync` on its statistics
barrier of stage `st` has the partner warp's softmax lane's event of the same ordinal. -/
theorem soft_partner (H : RouteCtx P L mem0 K A X) {p y pc st : Nat} (hp : p < L.threads)
    (h8 : 8 ≤ warpOf L p) (h12 : warpOf L p < 12) (hst : st < 2)
    (hy : X.get (p, y) = some ⟨pc, .bar (statsId st (warpOf L p - 8)) (some 64) .sync⟩)
    (hpass : y + 1 < (X.tr p).length) :
    partnerLane L p st < L.threads ∧ ctaOf L (partnerLane L p st) = ctaOf L p ∧
      warpOf L (partnerLane L p st) = warpOf L p - 8 + 4 * st ∧
      ∃ a pc' cnt md, X.get (partnerLane L p st, a) =
          some ⟨pc', .bar (statsId st (warpOf L p - 8)) cnt md⟩ ∧
        barOrd X (partnerLane L p st) a (statsId st (warpOf L p - 8)) =
          barOrd X p y (statsId st (warpOf L p - 8)) := by
  have hb := H.pre.block
  have hc : ctaOf L (partnerLane L p st) = ctaOf L p := by
    unfold partnerLane ctaOf warpOf
    rw [hb]
    unfold warpOf at h12
    rw [hb] at h12
    omega
  have hw : warpOf L (partnerLane L p st) = warpOf L p - 8 + 4 * st := by
    unfold partnerLane warpOf ctaOf
    rw [hb]
    unfold warpOf at h12 h8
    rw [hb] at h12 h8
    omega
  have hlt := Stats.thread_lt_of_cta hp hc
  refine ⟨hlt, hc, hw, ?_⟩
  obtain ⟨a, pc', cnt, md, ha, hord⟩ :=
    H.soft hst (by omega) hy hpass hlt hc hw
  exact ⟨a, pc', cnt, md, ha, hord⟩

/-- **The statistics witness**: the partner lane's event of the ordinal of a passed `bar.sync` is
an arrival counted by the release the `bar.sync` waits for, so a witness of its return. -/
theorem stats_rendezvous (H : RouteCtx P L mem0 K A X) {p y pc st g a pc' : Nat}
    {cnt : Option Nat} {md : BarMode} (hp : p < L.threads) (h8 : 8 ≤ warpOf L p)
    (h12 : warpOf L p < 12) (hst : st < 2) (hg : g < L.threads) (hc : ctaOf L g = ctaOf L p)
    (hy : X.get (p, y) = some ⟨pc, .bar (statsId st (warpOf L p - 8)) (some 64) .sync⟩)
    (hpass : y + 1 < (X.tr p).length)
    (ha : X.get (g, a) = some ⟨pc', .bar (statsId st (warpOf L p - 8)) cnt md⟩)
    (hord : barOrd X g a (statsId st (warpOf L p - 8)) =
      barOrd X p y (statsId st (warpOf L p - 8))) :
    Witness L X (.thread (g, a)) (p, y) := by
  have hX := H.cons
  have hk : warpOf L p - 8 < 4 := by omega
  have hS := Stats.sources H.stf (st := st) hk
  have hG := Stats.shape H.pre hst hk
  have hsame : SameCta L g p := ⟨hg, hp, by unfold ctaOf at hc; exact hc⟩
  have hf : X.IsBarrier (p, y) (statsId st (warpOf L p - 8)) (some 64) pc := hy
  have hke := hS.arrive_key_of_credit hX hG ha hg hsame.2.2.symm hf hpass
    (by unfold barOrd at hord; exact hord.symm)
  obtain ⟨key, hkf, hdone⟩ := ctaBarDone_of_returned hX hf hpass
  have hkey := hS.arrival_key hX hG hf (CtaBarK.arrival hkf)
  simp only at hkey hke
  unfold barOrd at hord
  rw [hkey, ← hord] at hkf hdone
  obtain ⟨ic, hcomp⟩ := hdone
  exact Witness.of_ctaBarCounted hkf hcomp hke hsame.2.2

/-- A witness of a `bar.sync`'s return precedes each later event of its thread. -/
theorem rendezvous_path {e f : EvId} {pc id : Nat} {cnt : Option Nat}
    (hf : X.get f = some ⟨pc, .bar id cnt .sync⟩) (hr : Witness L X (.thread e) f) {k : Nat}
    (hfk : f.2 < k) (hk : k < (X.tr f.1).length) :
    Relation.TransGen (DepStep L K X) (.thread e, false) (.thread (f.1, k), false) :=
  (Relation.TransGen.single (DepStep.of_witness L hr)).tail
    (DepStep.of_resumes L (Resumes.of_blocking (b := false) hf rfl ⟨rfl, hfk, hk⟩))

/-! ### The nodes of the induction -/

/-- The thread events of the launch (with a bound on the trace lengths). -/
def evs (L : Launch) (X : Execution) : Finset EvId :=
  Finset.range L.threads ×ˢ
    Finset.range (∑ g ∈ Finset.range L.threads, (X.tr g).length + 1)

open Classical in
/-- The nodes of the induction: the issues of the thread events and their commit
notifications. -/
def nodes (L : Launch) (X : Execution) : Finset (Ref × Bool) :=
  (evs L X).image (fun e => ((.thread e : Ref), false)) ∪
    (evs L X ×ˢ (Finset.univ : Finset (Fin 16))).image
      (fun q => ((.async q.1 (.tcNotify q.2) : Ref), false))

theorem evs_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : e ∈ evs L X := by
  have hg := event_thread_lt hX he
  have hl := len_of_get he
  have h3 := Finset.single_le_sum (f := fun g => (X.tr g).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hg)
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hg, Finset.mem_range.mpr (by omega)⟩

theorem thread_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : ((.thread e : Ref), false) ∈ nodes L X := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (evs_mem hX he))

theorem notify_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event} (rank : Fin 16)
    (he : X.get e = some ev) : ((.async e (.tcNotify rank) : Ref), false) ∈ nodes L X := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(e, rank),
    Finset.mem_product.mpr ⟨evs_mem hX he, Finset.mem_univ _⟩, rfl⟩)

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
