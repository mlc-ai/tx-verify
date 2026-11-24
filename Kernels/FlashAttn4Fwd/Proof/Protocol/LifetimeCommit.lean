-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.LifetimeMma
public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlotFacts
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreHandoff
public import Lemmas.Protocol.PairTmaRing.CopyExists
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PollIndex
public import Lemmas.Kernel.CommitNextExit
public import Lemmas.Order.GuardOrder
public import Lemmas.Async.AsyncOrigins

@[expose] public section

/-! # A commit's arrive-ons finish before the target CTA exits

The premise `CommitFinished` of `Safety.no_sharedLifetimeUnsafe` (`commitFinished`): the
arrive-on of a commit at each target rank completes before an exit of the target barrier's CTA,
once that CTA exited. A commit notifies a ring empty barrier, an S-full or an O-full object
(`ExitFacts.commit_target`), multicast to both CTAs of the pair:

* **O-full** (`ofull_finished`): the commit of item `n` (its earlier commits there) is of an item
  that passed the loop test (`ExitFacts.ofull_commit`); the target CTA's correction thread of warp
  8, lane 0 polled the object for every such item before its exit (`ExitFacts.corr_exit`), and its
  poll for item `n` observes the notification of the commit with `n` earlier ones
  (`OAcc.OFullHandoff`), which is this commit (one elected MMA lane commits,
  `Rings.lead_unique`) at this rank (`target_rank`).
* **S-full** (`sfull_finished`): the same with the softmax thread of the stage's first warp, the
  score tiles (`ExitFacts.sfull_commit`, `soft_exit`) and `Score.SFullHandoff`.
* **A ring empty barrier but `qEmpty 0`** (`empty_finished`): the commit of use `n` follows the
  MMA lane's poll of the full barrier for use `n` (`RingFacts.commit`), which observed each
  loader's copies of use `n` (`PairTmaRing.copy_exists`); the target CTA's loader, which exited
  after its drain (`RingFacts.drain`), then polled the empty barrier at least `n + 2` times, and
  its poll for use `n + 1` observes the commit's notification (`PairTmaRing.producer_observes`).
* **`qEmpty 0`** (`empty_finished`, its second case): the loader does not drain stage 0. Its
  polls of `qEmpty 0` are at least `n + 1` for the commit of use `n` (`RingFacts.issue_use` of
  its copy of use `n`), so
  it polled `qEmpty 1` at least `n + 2` times (`ExitFacts.loader_q`): it observed the MMA lane's
  commit to `qEmpty 1` of use `n`, the thread's next commit (`ExitFacts.q_next`). The commit is at
  site 995, selected by the commit-order assumption (`Assumptions.commitOrder`), so its arrive-on
  is finished through the next one's (`SharedFinished.of_commitNext`), once it is performed: the
  premise `SelectedPerformed`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The premise of the commit-order assumption's use**: the arrive-on at a rank of a commit at a
site the assumptions select with `commitInOrder` is performed once the arrive-on at that rank of
its thread's next commit is. -/
def SelectedPerformed (A : List Assumption) (X : Execution) : Prop :=
  ∀ (g j j' pc : Nat) (sp : TcCommit.Spec) (r : Fin 16),
    X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → A.any (·.commitInOrder pc) = true →
    j < j' → (∃ s, X.Commit (g, j') s) → (∀ k, j < k → k < j' → ¬ ∃ s, X.Commit (g, k) s) →
    r ∈ X.tcNotified (g, j') → r ∈ X.tcNotified (g, j)

/-- **The commit-order assumption's constraint gives the premise** (`Assumptions.commitOrder`'s
`wf`, `Assumption.commitPerformedAt`). -/
theorem selectedPerformed (hX : Consistent L kernel asms mem0 X) : SelectedPerformed asms X := by
  intro g j j' pc sp r he hs hjj hc hk hr
  have hw := hX.asm Assumptions.commitOrder (by simp [asms, Assumptions.all])
  rw [show asms = Assumptions.all from rfl, Assumptions.all_commitInOrder] at hs
  exact hw g j j' pc sp r he hs hjj hc hk hr

/-- A commit's targets at two ranks agree only at one rank. -/
theorem target_rank {s : TcCommit.Spec} {r r' : Fin 16} {m : Loc}
    (h : TcCommit.target s r = some m) (h' : TcCommit.target s r' = some m) : r = r' := by
  unfold TcCommit.target at h h'
  split_ifs at h h'
  have := congrArg Loc.cta ((Option.some.inj h).trans (Option.some.inj h').symm)
  simp only at this
  exact Fin.ext (by omega)

/-- **An arrive-on observed by a spinning poll of a thread of CTA `c` before that thread's exit is
finished.** -/
theorem notify_finished (hX : Consistent L kernel asms mem0 X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit)
    {i w : EvId} {r : Fin 16} {m : Loc} {acq : Bool} {ws : MbarScope} {c kx pcx : Nat}
    (hp : X.AsyncPresent i (.tcNotify r)) (hwo : WaitObserves X (.async i (.tcNotify r)) w m acq ws)
    (hw1 : w.1 < L.threads) (hwc : ctaOf L w.1 = c)
    (hk : X.get (w.1, kx) = some ⟨pcx, .exit⟩) (hwk : w.2 < kx) :
    SharedFinished L kernel asms X (.async i (.tcNotify r)) c := by
  obtain ⟨pc, p, hget⟩ := hwo.1
  have hobs : Witness L X (.async i (.tcNotify r)) w :=
    Witness.of_mbarObserved (mbarObserved_of_waitObserves hX.tma.2.2.1 hp hwo)
  obtain ⟨ex, hsp⟩ := hspin _ _ _ _ _ _ hget
  exact SharedFinished.of_observer_exit (finish := (w.1, kx)) hp hobs
    (Resumes.of_spin hget hsp rfl hwk (len_of_get hk))
    ⟨hw1, hwc, pcx, hk⟩

/-- Two commits of one elected MMA lane to one object with as many earlier commits there are one
commit. -/
theorem commit_eq (hX : Consistent L kernel asms mem0 X) {g g' j j' pc pc' : Nat}
    {sp sp' : TcCommit.Spec} {m : Loc} (hg : g < L.threads) (hg' : g' < L.threads)
    (hc : ctaOf L g = ctaOf L g') (hw : warpOf L g = warpOf L g') (hl : LeadAt L X g j)
    (hl' : LeadAt L X g' j') (he : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩)
    (he' : X.get (g', j') = some ⟨pc', .tc (.commit sp')⟩) (hm : sp.mbar = m)
    (hm' : sp'.mbar = m)
    (hn : ((X.tr g').take j').countP (commitsTo m) = ((X.tr g).take j).countP (commitsTo m)) :
    g' = g ∧ j' = j := by
  have hgg := Rings.lead_unique hX hg' hg hc.symm hw.symm hl' hl
  subst hgg
  exact ⟨rfl, nthEv_unique he' (by simp [commitsTo, hm']) he (by simp [commitsTo, hm]) hn⟩

/-! ### The S-full and O-full objects -/

/-- **An O-full commit's arrive-on** is observed by the target CTA's correction thread before its
exit. -/
theorem ofull_finished (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ho : OFullFacts L X) (hx : ExitFacts P L X) (hO : OAcc.OFullHandoff L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit)
    {g jc pc st c : Nat} {sp : TcCommit.Spec} {r : Fin 16} (hg : g < L.threads) (hst : st < 2)
    (he : X.get (g, jc) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp r = some (oFullBar L c st)) (hex : CtaExited L X c) :
    SharedFinished L kernel asms X (.async (g, jc) (.tcNotify r)) c := by
  obtain ⟨hw12, hlc, hlead, hmb⟩ := ho.o_commit hg hst he htg
  have hcg : c / 2 = ctaOf L g / 2 := by unfold leadCta at hlc; omega
  have hc : c < L.grid := pair_lt hpre (cta_lt hg) hcg
  obtain ⟨hh, hch, hwh⟩ := lane_place hpre hc (w := 8) (by decide)
  set h := c * L.block + 32 * 8
  obtain ⟨kh, pch, hkh⟩ := exit_of_exited hex hh hch
  have hu := hx.corr_exit hh (by omega) (by omega) hkh hst
    (u := ((X.tr g).take jc).countP (commitsTo sp.mbar)) (by
      rw [workOf_pair (g := g) hpre (by rw [hch]; exact hcg)]
      exact hx.ofull_commit hg hst he hmb)
  obtain ⟨j, pcj, pj, acq, sc, hjk, hget, hcnt⟩ :=
    MbarRing.UnitHandoff.exists_poll (m := oFullBar L (ctaOf L h) st) hu
  obtain ⟨⟨xg, xj⟩, s', rank', ws, ⟨pcx, hxget⟩, -, hmbx, hcntx, htgx, hrank, hwo, -⟩ :=
    hO hh (by omega) (by omega) hst hget
  have hxg := Frame.lt_of_get hX hxget
  rw [hch] at htgx hwo
  obtain ⟨hwx, hlcx, hleadx, -⟩ := ho.o_commit hxg hst hxget htgx
  have e1 : ctaOf L xg = ctaOf L g := hlcx.symm.trans hlc
  obtain ⟨rfl, rfl⟩ := commit_eq hX hg hxg e1.symm (by rw [hw12, hwx]) hlead hleadx he hxget hmb
    (by rw [hmbx]; show oFullBar L (ctaOf L xg) st = _; rw [e1])
    (by
      unfold OAcc.oCommits at hcntx
      simp only at hcntx
      rw [e1] at hcntx
      rw [hcntx, hcnt, hmb])
  rw [hxget] at he
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at he
  obtain ⟨-, rfl⟩ := he
  obtain rfl := target_rank htgx htg
  exact notify_finished hX hspin hrank hwo hh hch hkh hjk

/-- **An S-full commit's arrive-on** is observed by the target CTA's softmax thread of the
stage's first warp before its exit. -/
theorem sfull_finished (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hsf : SFullFacts L X) (hx : ExitFacts P L X) (hS : Score.SFullHandoff L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit)
    {g jc pc st c : Nat} {sp : TcCommit.Spec} {r : Fin 16} (hg : g < L.threads) (hst : st < 2)
    (he : X.get (g, jc) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp r = some (sFullBar L c st)) (hex : CtaExited L X c) :
    SharedFinished L kernel asms X (.async (g, jc) (.tcNotify r)) c := by
  obtain ⟨hw12, hlc, hlead, hmb⟩ := hsf.s_commit hg hst he htg
  have hcg : c / 2 = ctaOf L g / 2 := by unfold leadCta at hlc; omega
  have hc : c < L.grid := pair_lt hpre (cta_lt hg) hcg
  obtain ⟨hh, hch, hwh⟩ := lane_place hpre hc (w := 4 * st) (by omega)
  set h := c * L.block + 32 * (4 * st)
  have hws : warpOf L h / 4 = st := by rw [hwh]; omega
  obtain ⟨kh, pch, hkh⟩ := exit_of_exited hex hh hch
  have hu := hx.soft_exit hh (by omega) hkh
    (u := ((X.tr g).take jc).countP (commitsTo sp.mbar)) (by
      rw [workOf_pair (g := g) hpre (by rw [hch]; exact hcg)]
      exact hx.sfull_commit hg hst he hmb)
  obtain ⟨j, pcj, pj, acq, sc, hjk, hget, hcnt⟩ :=
    MbarRing.UnitHandoff.exists_poll (m := sFullBar L (ctaOf L h) (warpOf L h / 4)) hu
  obtain ⟨⟨xg, xj⟩, s', rank', ws, ⟨pcx, hxget⟩, -, hmbx, hcntx, htgx, hrank, hwo, -⟩ :=
    hS hh (by omega) hget
  have hxg := Frame.lt_of_get hX hxget
  rw [hch, hws] at htgx hwo
  rw [hws] at hmbx hcntx
  obtain ⟨hwx, hlcx, hleadx, -⟩ := hsf.s_commit hxg hst hxget htgx
  have e1 : ctaOf L xg = ctaOf L g := hlcx.symm.trans hlc
  obtain ⟨rfl, rfl⟩ := commit_eq hX hg hxg e1.symm (by rw [hw12, hwx]) hlead hleadx he hxget hmb
    (by rw [hmbx]; show sFullBar L (ctaOf L xg) st = _; rw [e1])
    (by
      unfold sCommits sPolls at hcntx
      simp only at hcntx
      rw [e1] at hcntx
      rw [hws] at hcnt
      rw [hcntx, hcnt, hmb])
  rw [hxget] at he
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at he
  obtain ⟨-, rfl⟩ := he
  obtain rfl := target_rank htgx htg
  exact notify_finished hX hspin hrank hwo hh hch hkh hjk

/-! ### The ring empty barriers -/

theorem isEmpty_ring {b : FBar} (h : b.isEmpty) : b.ring := by
  cases b <;> simp_all [FBar.ring, FBar.isEmpty]

/-- A commit's target at rank `r` is in CTA `clusterBase + r`, of the commit's cluster. -/
theorem target_cta {s : TcCommit.Spec} {r : Fin 16} {m : Loc} (h : TcCommit.target s r = some m) :
    m.cta = s.clusterBase + r.val ∧ r.val < s.clusterSize := by
  unfold TcCommit.target at h
  split_ifs at h with hr
  exact ⟨by rw [← Option.some.inj h], hr.1⟩

/-- The site-995 commit is selected by the commit-order assumption. -/
theorem commitOrder_995 : asms.any (·.commitInOrder 995) = true :=
  List.any_eq_true.mpr ⟨Assumptions.commitOrder, by simp [asms, Assumptions.all], rfl⟩

/-- A loader lane elected before an event is elected before every later one. -/
theorem leadAt_mono {g k k' : Nat} (h : LeadAt L X g k) (hk : k ≤ k') : LeadAt L X g k' := by
  obtain ⟨j, hj, rest⟩ := h
  exact ⟨j, by omega, rest⟩

/-- **A ring empty commit's arrive-on** is observed by the target CTA's elected loader lane before
its exit: through its drain on every barrier but `qEmpty 0`; through the next commit's arrive-on,
on `qEmpty 1`, for `qEmpty 0`. -/
theorem empty_finished (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (htm : TmemFacts L X) (hx : ExitFacts P L X)
    (hinit : Rings.RingInit L X) (hsel : SelectedPerformed asms X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit)
    {g jc pc c : Nat} {b : FBar} {sp : TcCommit.Spec} {r : Fin 16} (hg : g < L.threads)
    (hbE : b.isEmpty) (he : X.get (g, jc) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp r = some (b.loc L c)) (hex : CtaExited L X c) :
    SharedFinished L kernel asms X (.async (g, jc) (.tcNotify r)) c := by
  obtain ⟨-, hw12, heven, hlead, hmb, hbase, hsize, hcnt⟩ := hr.commit hg he htg (isEmpty_ring hbE)
  set bf := b.partner with hbfdef
  have hbf : bf.isFull := Rings.partner_isFull hbE
  have hbb : bf.partner = b := Rings.partner_partner' hbE
  set p := ctaOf L g / 2 with hp
  have hcg2 : ctaOf L g = 2 * p := by omega
  have H := Rings.hyp hpre hX hr htm hinit hbf p
  set S := Rings.slot L X p bf with hS
  obtain ⟨hcta, hrc⟩ := target_cta htg
  simp only [FBar.loc] at hcta
  rw [hbase, hsize] at *
  set a : Fin 2 := ⟨r.val, by omega⟩ with ha
  have hca : c = 2 * p + a.val := by rw [hcta, hcg2]
  have hcons : S.cons 0 = g := by
    show Rings.leadOf L X (2 * p) 12 = g
    rw [← hcg2, ← hw12]
    exact Rings.leadOf_eq hX hg hlead
  have hempty0 : S.empty 0 = sp.mbar := by
    show bf.partner.loc L (2 * p + 0) = _
    rw [hbb, hmb, hcg2]
    rfl
  have hemptya : S.empty a = b.loc L c := by
    show bf.partner.loc L (2 * p + a.val) = _
    rw [hbb, hca]
  set n := ((X.tr g).take jc).countP (commitsTo sp.mbar) with hn
  have hnf : n < okPolls S.full (X.tr (S.cons 0)) := by
    rw [hcons]
    have := PairTmaRing.okPolls_take_le (bf.loc L (ctaOf L g)) (X.tr g) jc
    have hfull : S.full = bf.loc L (ctaOf L g) := by
      show bf.loc L (2 * p) = _
      rw [hcg2]
    rw [hfull]
    omega
  have hnpos := H.n_pos
  obtain ⟨k, pck, al, spk, hk, hmk, hck⟩ :=
    PairTmaRing.copy_exists hX H (b := 0) hnf a (j := S.n - 1) (by omega)
  set prod := S.prod a with hprod
  have hpl := Frame.lt_of_get hX hk
  obtain ⟨-, -, hw14, hleadk, -⟩ := hr.issue hpl hk hmk (Rings.isFull_ring hbf)
  have hcx : ctaOf L prod = c := by
    rw [hca]
    exact Rings.ctaOf_lead hpre a
  obtain ⟨kp, pcp, hkp⟩ := exit_of_exited hex hpl hcx
  have hlast := Execution.exit_last hX hpl hkp
  have hkk : k < kp := by
    have : k < (X.tr prod).length := len_of_get hk
    rcases Nat.lt_or_ge k kp with h | h
    · exact h
    · have hkq : k = kp := by omega
      rw [hkq, hkp] at hk
      cases hk
  have hleadkp := leadAt_mono hleadk hkk.le
  have hwait : ∀ (m : Loc) q, q < okPolls m (X.tr prod) →
      ∃ pcw pw acqw scw, X.get (prod, MbarRing.Poll.nth X m prod q) =
        some ⟨pcw, .wait m pw true acqw scw⟩ ∧ MbarRing.Poll.nth X m prod q < kp := by
    intro m q hq
    obtain ⟨pcw, pw, acqw, scw, hwget, -⟩ := MbarRing.Poll.nth_spec hq
    refine ⟨pcw, pw, acqw, scw, hwget, ?_⟩
    have : MbarRing.Poll.nth X m prod q < (X.tr prod).length := len_of_get hwget
    rcases Nat.lt_or_ge (MbarRing.Poll.nth X m prod q) kp with h | h
    · exact h
    · have hkq : MbarRing.Poll.nth X m prod q = kp := by omega
      rw [hkq, hkp] at hwget
      cases hwget
  by_cases hq0 : b = .qEmpty 0
  · have hbfq : bf = .qFull 0 := by rw [hbfdef, hq0]; rfl
    have hcop : S.n = 2 := by
      show bf.copies = 2
      rw [hbfq]
      rfl
    have huse := hr.issue_use hpl hk hmk (Rings.isFull_ring hbf)
    change ((X.tr prod).take k).countP (issuesTo S.full) / S.n + 1 =
      okPolls (bf.partner.loc L (ctaOf L prod)) ((X.tr prod).take k) at huse
    have hel : bf.partner.loc L (ctaOf L prod) = FBar.loc L (ctaOf L prod) (.qEmpty 0) := by
      rw [hbb, hq0]
    rw [hck, hcop, hel] at huse
    have hq0p : n + 1 ≤ okPolls (FBar.loc L (ctaOf L prod) (.qEmpty 0)) (X.tr prod) := by
      have := PairTmaRing.okPolls_take_le (FBar.loc L (ctaOf L prod) (.qEmpty 0)) (X.tr prod) k
      have h2 : (2 * n + (2 - 1)) / 2 = n := by omega
      rw [h2] at huse
      omega
    have hlq := hx.loader_q hpl hw14 hleadkp hkp
    have H1 := Rings.hyp hpre hX hr htm hinit (b := .qFull 1) rfl p
    set S1 := Rings.slot L X p (.qFull 1) with hS1
    have hp1 : S1.prod a = prod := rfl
    have he1a : S1.empty a = FBar.loc L (ctaOf L prod) (.qEmpty 1) := by
      show (FBar.qFull 1).partner.loc L (2 * p + a.val) = _
      rw [hcx, hca]
      rfl
    have hq1 : n + 1 < okPolls (S1.empty a) (X.tr (S1.prod a)) := by
      rw [he1a, hp1, hlq]
      omega
    obtain ⟨-, -, hub1⟩ := PairTmaRing.producer_observes hX H1 (a := a) (n := n) hq1 0
    have hcons1 : S1.cons 0 = g := hcons
    set j' := nthEv X (commitsTo (S1.empty 0)) g n with hj'
    have hnote1 : PairTmaRing.note X S1 0 a n = .async (g, j') (.tcNotify r) := by
      unfold PairTmaRing.note PairTmaRing.cm
      rw [hcons1]
      rfl
    rw [hnote1] at hub1
    have hub1' := hub1
    obtain ⟨i1, -, rec, -, -, hri, hrid, -⟩ := hub1'
    have hrec := List.mem_of_getElem? hri
    have hpres1 := object_record_present hX.tma hrec
    rw [hrid] at hpres1
    have hemp10 : S1.empty 0 = FBar.loc L (ctaOf L g) (.qEmpty 1) := by
      show (FBar.qFull 1).partner.loc L (2 * p + 0) = _
      rw [hcg2]
      rfl
    obtain ⟨pc1, sp1, he1⟩ : ∃ pc1 sp1, X.get (g, j') = some ⟨pc1, .tc (.commit sp1)⟩ := by
      cases record_source hX.tma.2.2.1 hrec with
      | commit hid he1 _ _ =>
        rw [hrid] at hid
        simp only [Ref.async.injEq] at hid
        obtain ⟨rfl, -⟩ := hid
        exact ⟨_, _, he1⟩
      | init hid _ _ | inval hid _ _ | arrive hid _ _ | wait hid _ _ | increment hid _ _ =>
        rw [hrid] at hid
        cases hid
      | tensor hid _ _ _ | arriveOn hid _ _ _ _ | bulk hid _ _ _ _ | clc hid _ _ _ _ =>
        rw [hrid] at hid
        simp only [Ref.async.injEq] at hid
        obtain ⟨-, h⟩ := hid
        cases h
    obtain ⟨hct1, hcn1⟩ := nthEv_spec_of_get he1
    have hmb1 : sp1.mbar = FBar.loc L (ctaOf L g) (.qEmpty 1) := by
      simp only [commitsTo, decide_eq_true_eq] at hct1
      rw [hct1, hemp10]
    have hmb0 : sp.mbar = FBar.loc L (ctaOf L g) (.qEmpty 0) := by rw [hmb, hq0]
    obtain ⟨h995, hnext⟩ := hx.q_next hg he hmb0
    obtain ⟨hlt, hnone⟩ := hnext he1 hmb1 (by rw [hmb1, ← hemp10, hcn1])
    have hnone' : ∀ k, jc < k → k < j' → ¬ ∃ s, X.Commit (g, k) s :=
      fun k h1 h2 ⟨s, pck, hck⟩ => hnone k h1 h2 pck s hck
    have hA : asms.any (·.commitInOrder pc) = true := by rw [h995]; exact commitOrder_995
    have hpres0 := hsel g jc j' pc sp r he hA hlt ⟨sp1, pc1, he1⟩ hnone' hpres1
    have hcn : CommitNext asms X (.async (g, jc) (.tcNotify r)) (.async (g, j') (.tcNotify r)) :=
      ⟨rfl, rfl, hlt, hpres0, hpres1, ⟨pc, sp, he, hA⟩, ⟨sp1, pc1, he1⟩, hnone'⟩
    obtain ⟨pcw, pw, acqw, scw, hwget, hwk⟩ := hwait (S1.empty a) (n + 1) hq1
    have hobs : Witness L X (.async (g, j') (.tcNotify r)) (prod, _) := Witness.of_mbarObserved
      (mbarObserved_of_waitObserves hX.tma.2.2.1 hpres1 ⟨⟨pcw, pw, hwget⟩, hub1⟩)
    obtain ⟨ex, hsp⟩ := hspin _ _ _ _ _ _ hwget
    exact SharedFinished.of_commitNext (finish := (prod, kp)) hpres0 hcn hobs
      (.single (DepStep.of_resumes L (Resumes.of_spin hwget hsp rfl hwk
        (len_of_get hkp))))
      ⟨hpl, hcx, pcp, hkp⟩
  · have hbf0 : bf ≠ .qFull 0 := by
      intro h
      apply hq0
      rw [← hbb, h]
      rfl
    have hdrain := hr.drain hpl hkp hw14 hleadkp hbf hbf0
    have htot : S.n * n + S.n ≤ (X.tr prod).countP (issuesTo S.full) := by
      have h1 := countP_take_succ (p := issuesTo S.full) hk (by simp [issuesTo, hmk])
      have h2 := countP_take_mono (issuesTo S.full) (X.tr prod)
        (show k + 1 ≤ (X.tr prod).length by omega)
      rw [List.take_length] at h2
      omega
    have hpe : okPolls (S.empty a) (X.tr prod) ≥ n + 2 := by
      have hpb : pairBase L prod = 2 * p := by
        unfold pairBase
        rw [hcx, hca]
        omega
      have hfl : bf.loc L (pairBase L prod) = S.full := by rw [hpb]; rfl
      have hel : bf.partner.loc L (ctaOf L prod) = S.empty a := by rw [hcx, hca]; rfl
      rw [hfl, hel] at hdrain
      change bf.copies * n + bf.copies ≤ _ at htot
      have : bf.copies * (n + 2) ≤ bf.copies * okPolls (S.empty a) (X.tr prod) := by
        rw [Nat.mul_add]
        omega
      exact Nat.le_of_mul_le_mul_left this hnpos
    obtain ⟨-, -, hub⟩ := PairTmaRing.producer_observes hX H (a := a) (n := n)
      (show n + 1 < okPolls (S.empty a) (X.tr prod) by omega) 0
    have hnote : PairTmaRing.note X S 0 a n = .async (g, jc) (.tcNotify r) := by
      unfold PairTmaRing.note PairTmaRing.cm
      rw [hcons, hempty0, hn, nthEv_eq he (by simp [commitsTo])]
      rfl
    rw [hnote] at hub
    obtain ⟨pcw, pw, acqw, scw, hwget, hwk⟩ := hwait (S.empty a) (n + 1) (by omega)
    have hpres : X.AsyncPresent (g, jc) (.tcNotify r) := by
      obtain ⟨i, -, rec, -, -, hri, hrid, -⟩ := hub
      have := object_record_present hX.tma (List.mem_of_getElem? hri)
      rw [hrid] at this
      exact this
    exact notify_finished hX hspin hpres ⟨⟨pcw, pw, hwget⟩, hub⟩ hpl hcx hkp hwk

/-! ### The table -/

/-- **CommitFinished**: a commit's arrive-on at each target rank completes before an exit of the
target barrier's CTA, once that CTA exited. -/
theorem commitFinished (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (htm : TmemFacts L X) (ho : OFullFacts L X) (hsf : SFullFacts L X)
    (hx : ExitFacts P L X) (hinit : Rings.RingInit L X) (hO : OAcc.OFullHandoff L X)
    (hS : Score.SFullHandoff L X) (hsel : SelectedPerformed asms X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit) :
    ∀ i (s : TcCommit.Spec) rank (m : Loc), X.Commit i s → TcCommit.target s rank = some m →
      CtaExited L X m.cta → SharedFinished L kernel asms X (.async i (.tcNotify rank)) m.cta := by
  rintro ⟨g, jc⟩ s rank m ⟨pc, he⟩ htg hex
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, c, rfl, hb⟩ := hx.commit_target hg he htg
  rcases hb with hbE | ⟨st, rfl | rfl⟩
  · exact empty_finished hpre hX hr htm hx hinit hsel hspin hg hbE he htg hex
  · exact sfull_finished hpre hX hsf hx hS hspin hg st.isLt he htg hex
  · exact ofull_finished hpre hX ho hx hO hspin hg st.isLt he htg hex

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
