-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Faults
public import Lemmas.Async.AsyncOrder
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Order.OrderNotAccess
public import Lemmas.Order.OrderWaits
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The order of a pair TMA ring slot's copies and its consumers' reads

A proof tool over `Hyp`. A copy issue completing on the full barrier, with `n · u + j` earlier
issues of its producer there, is the item of use `u`; consumer `b`'s successful full poll for use
`u` observes its completion (`copy_observed`, an `AsyncObserved` of the copy), so the copy's
writes precede a later read of `b` (`copy_before_read`). Producer `a`'s successful empty poll for
use `q + 1` observed phase `q`, after at least `q + 1` notifications of each consumer
(`producer_poll`); each notification is of a distinct commit (`notified_commits`), and a read of
consumer `b` before its commit of use `t ≤ q` is acquired by that poll (`read_observed`), so it
precedes the producer's later copies (`read_before_copy`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-! ### Notification records -/

/-- A tensor copy's notification record on an object: its issue names the object and the
copy's bytes, and its observation is notified. -/
theorem tensorNotify_facts {m : Loc} {i : EvId} {n : Nat}
    (h : objectAction X X.async m (.async i (.notify .load)) = some (.completeTx n)) :
    ∃ (pc : Nat) (a : Nat) (s : TensorCopy.Spec) (o : TensorCopy.Observation),
      X.get i = some ⟨pc, .tensorIssue a s⟩ ∧
      X.tensor i = some o ∧ s.mbar = m ∧ o.effects.notified = true ∧
      TensorTransfer.bytes s.descriptor = n := by
  simp only [objectAction] at h
  cases hg : X.get i with
  | none => simp [hg] at h
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    cases k with
    | tensorIssue a s =>
      cases ho : X.tensor i with
      | none => simp [hg, ho] at h
      | some o =>
        by_cases hc : s.mbar = m ∧ o.effects.notified = true
        · simp [hg, ho, hc.1, hc.2] at h
          exact ⟨pc, a, s, o, rfl, rfl, hc.1, hc.2, by omega⟩
        · simp [hg, ho, hc] at h
    | _ => simp [hg] at h

/-- An observed notification of a tensor copy is an `AsyncObserved` of it by the observing wait. -/
theorem tensorObserved_of_notified (hX : Consistent L K A mem0 X) {m : Loc} {i w : EvId}
    {n pcw p : Nat} {ws : MbarScope}
    (hi : objectAction X X.async m (.async i (.notify .load)) = some (.completeTx n))
    (hw : X.get w = some ⟨pcw, .wait m p true true ws⟩)
    (hu : UpdateBeforeWait (X.objects m) (.async i (.notify .load)) (.thread w)) :
    AsyncObserved X i (.notify .load) w true ws := by
  obtain ⟨pc, a, s, o, hget, hobs, hmb, hnot, hb⟩ := tensorNotify_facts hi
  have hspec : o.spec = s := by
    obtain ⟨mA, pc', hget'⟩ := (hX.tensor i o hobs).1
    have h := Option.some.inj (hget.symm.trans hget')
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
    exact h.2.2.symm
  exact ⟨_, m, ⟨rfl, o, a, hobs, ⟨pc, by rw [hspec]; exact hget⟩, by rw [hspec, hmb], hnot⟩,
    ⟨⟨pcw, p, hw⟩, hu⟩⟩

/-- A commit's notification record on an object: the commit is a commit of the thread that names
the object as its target, and the rank is one of its committed targets. -/
theorem tcNotify_facts {m : Loc} {c : EvId} {rank : Fin 16} {act : MBarrier.Action}
    (h : objectAction X X.async m (.async c (.tcNotify rank)) = some act) :
    ∃ pc s, X.get c = some ⟨pc, .tc (.commit s)⟩ ∧ TcCommit.target s rank = some m ∧
      rank ∈ X.tcNotified c := by
  simp only [objectAction] at h
  cases hg : X.get c with
  | none => simp [hg] at h
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    cases k with
    | tc k' =>
      cases k' with
      | commit s =>
        by_cases hc : TcCommit.target s rank = some m ∧ rank ∈ X.tcNotified c
        · exact ⟨pc, s, rfl, hc.1, hc.2⟩
        · simp [hg, hc] at h
      | _ => simp [hg] at h
    | _ => simp [hg] at h

/-- An MMA whose completion a wait observes has read its operand bytes: a byte its issue
addresses is present. -/
theorem mmaRead_present (hX : Consistent L K A mem0 X) {i w : EvId}
    {acq : Bool} {ws : MbarScope} (hom : AsyncObserved X i .mmaDone w acq ws) {d : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) {isB : Bool} {idx : Nat} {l : Loc}
    (hl : sp.byteLoc (if isB then .b else .a) idx = some l)
    (hidx : idx < (if isB then TcMma.Operand.b else .a).bytes sp.descriptor) :
    X.AsyncPresent i (.mmaRead isB idx) := by
  have hdone := (mma_done_waits (L := L) hX.tcCommit hom).1
  rcases hX.tma.2.1.1 i (hX.tma.2.1.2 i hdone) with
    ⟨d', sp', acc', mask', ops, hi', hops, -, ha, hb⟩ | ⟨c, ops, ⟨pc', hc⟩, -⟩ |
      ⟨s, ops, ⟨pc', hc⟩, -⟩
  · obtain ⟨pc, he⟩ := hi
    obtain ⟨pc', he'⟩ := hi'
    rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    obtain ⟨-, -, rfl, -, -⟩ := he'
    have hlt : idx < (if isB then ops.b else ops.a).length := by
      cases isB <;> simp_all
    obtain ⟨b, hb'⟩ : ∃ b, (if isB then ops.b else ops.a)[idx]? = some b :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    exact ⟨l, b, Or.inl ⟨d, sp, acc, mask, ⟨pc, he⟩, hl⟩, ops, hops, hb'⟩
  all_goals
    obtain ⟨pc, he⟩ := hi
    rw [he] at hc
    simp at hc

/-! ### Counts -/

/-- The successful poll of `m` with `n` earlier ones is before a thread's later ones. -/
theorem okPolls_lt_of_get {m : Loc} {g j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩) :
    okPolls m ((X.tr g).take j) < okPolls m (X.tr g) := by
  have h1 := MbarRing.Poll.okPoll_get he
  have h2 := MbarRing.Poll.okPolls_mono m (X.tr g)
    (show j + 1 ≤ (X.tr g).length from len_of_get he)
  rw [List.take_length] at h2
  omega

/-- Two tensor issues on `m` of one thread with as many earlier issues there are one. -/
theorem issue_index_unique {m : Loc} {g k1 pc1 a1 k2 pc2 a2 : Nat} {sp1 sp2 : TensorCopy.Spec}
    (he1 : X.get (g, k1) = some ⟨pc1, .tensorIssue a1 sp1⟩) (hm1 : sp1.mbar = m)
    (he2 : X.get (g, k2) = some ⟨pc2, .tensorIssue a2 sp2⟩) (hm2 : sp2.mbar = m)
    (hcnt : ((X.tr g).take k1).countP (issuesTo m) = ((X.tr g).take k2).countP (issuesTo m)) :
    k1 = k2 := by
  have hiss : ∀ {k pc a} {sp : TensorCopy.Spec}, X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ →
      sp.mbar = m → ∀ k', k < k' →
        ((X.tr g).take k).countP (issuesTo m) + 1 ≤ ((X.tr g).take k').countP (issuesTo m) := by
    intro k pc a sp he hm k' hk'
    have h1 := countP_take_succ he (show issuesTo m ⟨pc, .tensorIssue a sp⟩ = true by
      simp [issuesTo, hm])
    have h2 := countP_take_mono (issuesTo m) (X.tr g) (show k + 1 ≤ k' by omega)
    omega
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := hiss he1 hm1 k2 h; omega
  · exact h
  · have := hiss he2 hm2 k1 h; omega

/-- A cluster-scope wait meets the cluster-scope completion of an operation issued in its
cluster. -/
theorem scopes_meet (hX : Consistent L K A mem0 X) {g h j pc p : Nat} {m : Loc} {acq : Bool}
    {sc : MbarScope} (hg : g < L.threads) (hw : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩)
    (hsc : sc = .cluster) (hc : L.clusterOfCta (g / L.block) = L.clusterOfCta (h / L.block)) :
    ScopesMeet L .cluster g sc h := by
  have hh := Frame.lt_of_get hX hw
  subst hsc
  exact ⟨⟨hg, hh, hc⟩, ⟨hh, hg, hc.symm⟩⟩

variable {nc : Nat} {S : Slot nc}

/-! ### Copies before reads -/

/-- **A copy is observed by its use's poll.** Consumer `b`'s successful full poll with `u`
earlier ones observes the completion of a copy issue on the full barrier with `n · u + j`
earlier issues of its producer there. -/
theorem copy_observed (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc}
    {g k pc al : Nat} {sp : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = S.full) {j pcw p : Nat} {acq : Bool} {sc : MbarScope}
    (hew : X.get (S.cons b, j) = some ⟨pcw, .wait S.full p true acq sc⟩)
    (hj : okPolls S.full ((X.tr (S.cons b)).take j) =
      ((X.tr g).take k).countP (issuesTo S.full) / S.n) :
    AsyncObserved X (g, k) (.notify .load) (S.cons b, j) true sc := by
  obtain ⟨a, rfl, -⟩ := issue_producer H he hm
  have hn := H.n_pos
  set I := ((X.tr (S.prod a)).take k).countP (issuesTo S.full) with hI
  have hp : issuesTo S.full ⟨pc, .tensorIssue al sp⟩ = true := by simp [issuesTo, hm]
  have hk := copyKind_ne a (I % S.n) (Nat.mod_lt _ hn)
  have hit : itF X S (copyKind S.n a (I % S.n) (Nat.mod_lt _ hn)) (I / S.n) =
      .async (S.prod a, k) (.notify .load) := by
    rw [itF_ne hk, kOwner_copyKind, kIdx_copyKind, Nat.div_add_mod, hI, nthEv_eq he hp]
  have hlt : I / S.n < okPolls S.full (X.tr (S.cons b)) := by
    have := okPolls_lt_of_get hew
    omega
  obtain ⟨hx, -, hupd⟩ := consumer_observes hX H hlt (copyKind S.n a (I % S.n) (Nat.mod_lt _ hn))
  obtain ⟨⟨id, r, hid, hrid, -, -, h1⟩, -⟩ := SF_op H hx
  have hra : r.action = .completeTx S.bytes := h1 hk
  have hwF : wF X S b (I / S.n) = (S.cons b, j) := by
    simp only [wF]
    rw [← hj, MbarRing.Poll.nth_eq hew]
  rw [hit, hwF] at hupd
  rw [hit] at hrid
  obtain ⟨rfl, -⟩ := H.full_acq hew
  have hobj : objectAction X X.async S.full (.async (S.prod a, k) (.notify .load)) =
      some (.completeTx S.bytes) := by
    have h := ((hX.tma.2.2.1 S.full).2.1 r (List.mem_of_getElem? hid)).1
    rw [hrid, hra] at h
    exact h
  exact tensorObserved_of_notified hX hobj hew hupd

/-- **A copy before a read.** A copy on the full barrier with `n · u + j` earlier issues of its
producer there is ordered before a read, at a byte both cover, of consumer `b` that has polled the
full barrier successfully more than `u` times before it. -/
theorem copy_before_read (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc}
    {km : Nat} (hkm : km < (X.tr (S.cons b)).length) {gl kl pcl al : Nat}
    {spl : TensorCopy.Spec} (hel : X.get (gl, kl) = some ⟨pcl, .tensorIssue al spl⟩)
    (hml : spl.mbar = S.full)
    (hpolls : ((X.tr gl).take kl).countP (issuesTo S.full) / S.n + 1 ≤
      okPolls S.full ((X.tr (S.cons b)).take km))
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (S.cons b, km) (.mmaRead isB idx) l) :
    AsyncBefore L X l ((gl, kl), .write (.load x y z)) ((S.cons b, km), .mmaRead isB idx) := by
  obtain ⟨j, pc, p, acq, sc, hj, hew, hcw⟩ := MbarRing.Poll.exists_nth hpolls
  have hTO := copy_observed hX H hel hml hew hcw
  have hbo : baseCausality L X (S.cons b, j) (S.cons b, km) :=
    Relation.TransGen.single (Or.inl (po_of_source_not_access rfl hj hkm (by simp [hew,
      Event.acc])))
  have hsm : ScopesMeet L .cluster gl sc (S.cons b) := by
    have hgl := Frame.lt_of_get hX hel
    obtain ⟨a, rfl, -⟩ := issue_producer H hel hml
    exact scopes_meet hX hgl hew (H.full_acq hew).2 (H.cluster a b)
  exact ⟨hca, hcb, Or.inl ⟨_, .inr ⟨sc, hTO, hsm⟩, hbo⟩⟩

/-! ### Reads before copies -/

/-- Consumer `b`'s notification of `empty a`: a unit arrival by a commit of `b`'s thread,
notifying the rank of `a`. -/
def notifies (S : Slot nc) (a : Fin 2) (b : Fin nc) (r : Record Ref) : Bool :=
  match r.id with
  | .async i (.tcNotify rank) =>
    decide (i.1 = S.cons b ∧ rank = rankOf a ∧ r.action = .arrive 1 0)
  | _ => false

/-- A notification of consumer `b` on `empty a` is of a commit of `b`'s thread to the slot. -/
theorem notifies_commit (H : Hyp L K A X S) {a : Fin 2} {b : Fin nc} {x : Record Ref}
    (hx : x ∈ X.objects (S.empty a)) (hn : notifies S a b x = true) :
    ∃ jc pc sp, x.id = .async (S.cons b, jc) (.tcNotify (rankOf a)) ∧
      X.get (S.cons b, jc) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = S.empty 0 := by
  have ha : x.action = .arrive 1 0 := by
    revert hn
    unfold notifies
    split <;> simp_all
  obtain ⟨-, -, b', j, pc, sp, hid, he, hm, -⟩ := notify_consumer H hx ha
  have hb : S.cons b' = S.cons b := by
    simp only [notifies, hid, decide_eq_true_eq] at hn
    exact hn.1
  rw [H.cons_inj hb] at hid he
  exact ⟨j, pc, sp, hid, he, hm⟩

/-- **A producer's empty poll.** Producer `a`'s successful poll of its empty barrier with
`q + 1` earlier ones has a fault-free record that observes the barrier's phase `q`, with at least
`q + 1` notifications of each consumer before it. -/
theorem producer_poll (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    {jl pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hwl : X.get (S.prod a, jl) = some ⟨pc, .wait (S.empty a) p true acq sc⟩) {q : Nat}
    (hq : okPolls (S.empty a) ((X.tr (S.prod a)).take jl) = q + 1) :
    ∃ jr w, (X.objects (S.empty a))[jr]? = some w ∧ w.id = .thread (S.prod a, jl) ∧
      w.fault = none ∧ w.reply.waited = some true ∧
      observedAt (X.objects (S.empty a)) jr = some q ∧
      ∀ b, q + 1 ≤ ((X.objects (S.empty a)).take jr).countP (notifies S a b) := by
  classical
  set log := X.objects (S.empty a) with hlog
  have hch : CheckedLog log := X.objects_checked hX _
  have hni : NoInval log := H.empty_noInval a
  have hlt := okPolls_lt_of_get hwl
  rw [hq] at hlt
  obtain ⟨jr, w, st, hjr, hwid, hww, hst, hph, ho, -⟩ := E_found hX H (n := q + 1) (by omega) hlt
  have hwE : wE X S a (q + 1) = (S.prod a, jl) := by
    simp only [wE]
    rw [← hq, MbarRing.Poll.nth_eq hwl]
  rw [hwE] at hwid
  refine ⟨jr, w, hjr, hwid, fault_free hX H (.inr ⟨a, rfl⟩) (List.mem_of_getElem? hjr), hww,
    by rw [ho]; rfl, fun b => ?_⟩
  rw [MbarRing.Slot.countP_take_card]
  refine le_trans (le_of_eq (Finset.card_range (q + 1)).symm)
    (card_le_of_rel (Finset.range (q + 1)) _
      (fun t k => ∃ r, log[k]? = some r ∧ r.id = note X S b a t ∧ (b, t) ∈ SE X S a)
      (fun t ht' => ?_) (fun t _ t' _ k _ ⟨r, hr, hrid, hy⟩ ⟨r', hr', hrid', hy'⟩ => ?_))
  · have htq := Finset.mem_range.mp ht'
    obtain ⟨hy, hphy, -⟩ := producer_observes hX H (a := a) (n := t) (by omega) b
    obtain ⟨⟨i, r, hi, hid, -, ha⟩, -⟩ := SE_op H hy
    obtain ⟨-, sd, hsd, -⟩ := state_of_init hX (H.empty_init a) (H.empty_noInval a) hi
      (by intro n; rw [ha]; simp)
    have hsd' : stateBefore log i = some sd := hsd
    have hp : phaseAt log i = some sd.phase := by simp [phaseAt, hsd']
    have hpo := MbarRing.Poll.phaseOf_eq hX hi hp
    replace hphy : MbarRing.Poll.phaseOf X (S.empty a) r.id = t := by rw [hid]; exact hphy
    rw [hpo] at hphy
    have hij : i < jr := by
      by_contra hge
      obtain ⟨t', ht'', hle⟩ := hch.phase_mono hni (show jr ≤ i by omega)
        (List.getElem?_eq_some_iff.mp hi).1.le hst
      rw [hsd'] at ht''
      cases ht''
      omega
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hij, ?_⟩, r, hi, hid, hy⟩
    rw [hi]
    simp [notifies, hid, note, cm, ha]
  · rw [hr] at hr'
    cases hr'
    obtain ⟨-, ⟨pc1, sp1, he1, -, -, hc1⟩, -⟩ := SE_op H hy
    obtain ⟨-, ⟨pc2, sp2, he2, -, -, hc2⟩, -⟩ := SE_op H hy'
    have heq : cm X S b t = cm X S b t' := by
      have := hrid.symm.trans hrid'
      simp only [note, Ref.async.injEq, and_true] at this
      exact this
    rw [heq] at hc1
    exact hc1.symm.trans hc2

/-- **Notifications are of commits.** Consumer `b` has made at least as many commits to the slot
as its notifications in a prefix of `empty a`: each is of a distinct commit. -/
theorem notified_commits (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    {b : Fin nc} {jr q : Nat}
    (hq : q ≤ ((X.objects (S.empty a)).take jr).countP (notifies S a b)) :
    q ≤ (X.tr (S.cons b)).countP (commitsTo (S.empty 0)) := by
  classical
  have hnd : (X.objects (S.empty a)).Nodup :=
    List.Nodup.of_map _ (hX.tma.2.2.1 (S.empty a)).1.1
  let f : Record Ref → Nat := fun x => match x.id with
    | .async i _ => i.2
    | _ => 0
  have hle := MbarRing.Slot.length_le_countP_take
    (((X.objects (S.empty a)).take jr).filter (notifies S a b))
    ((hnd.sublist (List.take_sublist _ _)).filter _) (X.tr (S.cons b))
    (commitsTo (S.empty 0)) (X.tr (S.cons b)).length f ?_ ?_
  · rw [List.take_length, ← List.countP_eq_length_filter] at hle
    omega
  · intro x hx
    obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
    obtain ⟨jc, pcc, sp, hid, hcm, hmb⟩ := notifies_commit H (List.mem_of_mem_take hxt) hxn
    have hfx : f x = jc := by simp only [f, hid]
    rw [hfx]
    refine ⟨(List.getElem?_eq_some_iff.mp hcm).1, ?_⟩
    change (X.get (S.cons b, jc)).any _ = true
    rw [hcm]
    simp [commitsTo, hmb]
  · intro x hx y hy hxy
    obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
    obtain ⟨hyt, hyn⟩ := List.mem_filter.mp hy
    obtain ⟨jc, -, -, hid, -⟩ := notifies_commit H (List.mem_of_mem_take hxt) hxn
    obtain ⟨jc', -, -, hid', -⟩ := notifies_commit H (List.mem_of_mem_take hyt) hyn
    have h1 : f x = jc := by simp only [f, hid]
    have h2 : f y = jc' := by simp only [f, hid']
    rw [h1, h2] at hxy
    subst hxy
    exact hX.record_eq (List.mem_of_mem_take hxt) (List.mem_of_mem_take hyt) (hid.trans hid'.symm)

/-- **A producer's poll acquires an earlier read.** A read of consumer `b`, with at most `q`
commits of `b` to the slot up to it, is acquired by a successful empty poll of producer `a` at or
before its successful poll with `q + 1` earlier ones. -/
theorem read_observed (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    {b : Fin nc} {km : Nat} (hR : X.TcAsync (S.cons b, km)) {jl pc p : Nat} {acq : Bool}
    {sc : MbarScope} (hwl : X.get (S.prod a, jl) = some ⟨pc, .wait (S.empty a) p true acq sc⟩)
    {q : Nat} (hq : okPolls (S.empty a) ((X.tr (S.prod a)).take jl) = q + 1)
    (hK : ((X.tr (S.cons b)).take (km + 1)).countP (commitsTo (S.empty 0)) ≤ q) :
    ∃ jw, jw ≤ jl ∧ AsyncObserved X (S.cons b, km) .mmaDone (S.prod a, jw) true .cluster := by
  have hlt := okPolls_lt_of_get hwl
  rw [hq] at hlt
  obtain ⟨t, htdef⟩ : ∃ t, t = ((X.tr (S.cons b)).take (km + 1)).countP
    (commitsTo (S.empty 0)) := ⟨_, rfl⟩
  rw [← htdef] at hK
  obtain ⟨hy, -, hupd⟩ := producer_observes hX H (a := a) (n := t) (by omega) b
  obtain ⟨⟨i, r, hi, hid, -, -⟩, ⟨pcc, sp, hcm, hmb, htg, hcnt⟩, -⟩ := SE_op H hy
  have hkc : km < (cm X S b t).2 := by
    by_contra hge
    have hp : commitsTo (S.empty 0) ⟨pcc, .tc (.commit sp)⟩ = true := by
      simp [commitsTo, hmb]
    have hcm' : X.get (S.cons b, (cm X S b t).2) = some ⟨pcc, .tc (.commit sp)⟩ := hcm
    have hcnt' : ((X.tr (S.cons b)).take (cm X S b t).2).countP (commitsTo (S.empty 0)) = t :=
      hcnt
    have h1 := countP_take_succ hcm' hp
    have h2 := countP_take_mono (commitsTo (S.empty 0)) (X.tr (S.cons b))
      (show (cm X S b t).2 + 1 ≤ km + 1 by omega)
    omega
  have hwpos : (wE X S a (t + 1)).2 ≤ jl := by
    simp only [wE]
    have hnq : MbarRing.Poll.nth X (S.empty a) (S.prod a) (q + 1) = jl := by
      rw [← hq, MbarRing.Poll.nth_eq hwl]
    rcases Nat.lt_or_eq_of_le (show t + 1 ≤ q + 1 by omega) with h | h
    · rw [← hnq]
      exact (MbarRing.Poll.nth_lt_nth h hlt).le
    · rw [h, hnq]
  obtain ⟨pcw, pw, acqw, scw, hew, -⟩ := MbarRing.Poll.nth_spec (X := X)
    (m := S.empty a) (g := S.prod a) (n := t + 1) (by omega)
  obtain ⟨rfl, rfl⟩ := H.empty_acq hew
  have hnp := object_record_present hX.tma (List.mem_of_getElem? hi)
  rw [hid] at hnp
  exact ⟨(wE X S a (t + 1)).2, hwpos, _, S.empty a,
    ⟨cm X S b t, sp, rankOf a, rfl, ⟨rfl, hkc, hR, sp, pcc, hcm⟩, ⟨pcc, hcm⟩, htg, hnp⟩,
    ⟨⟨pcw, pw, hew⟩, hupd⟩⟩

/-- **A read before a copy.** A read of consumer `b` is ordered before a copy of producer `a`,
at a byte both cover, when `b`'s commits to the slot up to the read are two fewer than `a`'s
successful empty polls before the copy; and a wait observes the read's completion. -/
theorem read_before_copy (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    {b : Fin nc} {km : Nat} (hR : X.TcAsync (S.cons b, km)) {kl pcl al : Nat}
    {spl : TensorCopy.Spec} (hel : X.get (S.prod a, kl) = some ⟨pcl, .tensorIssue al spl⟩)
    (hcnt : ((X.tr (S.cons b)).take (km + 1)).countP (commitsTo (S.empty 0)) + 2 ≤
      okPolls (S.empty a) ((X.tr (S.prod a)).take kl))
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (S.cons b, km) (.mmaRead isB idx) l)
    (hcb : AsyncCovers X (S.prod a, kl) (.write (.load x y z)) l) :
    AsyncBefore L X l ((S.cons b, km), .mmaRead isB idx) ((S.prod a, kl), .write (.load x y z)) ∧
      ∃ w ws, AsyncObserved X (S.cons b, km) .mmaDone w true ws := by
  obtain ⟨jl, pc, p, acq, sc, hjl, hwl, hcl⟩ := MbarRing.Poll.exists_nth (X := X)
    (g := S.prod a) (k := kl) (m := S.empty a)
    (n := okPolls (S.empty a) ((X.tr (S.prod a)).take kl) - 1) (by omega)
  obtain ⟨jw, hjw, hom⟩ := read_observed hX H hR hwl
    (q := okPolls (S.empty a) ((X.tr (S.prod a)).take kl) - 2) (by omega) (by omega)
  have hkl : kl < (X.tr (S.prod a)).length := (List.getElem?_eq_some_iff.mp hel).1
  have hbo : baseCausality L X (S.prod a, jw) (S.prod a, kl) :=
    Relation.TransGen.single (Or.inl (po_of_source_not_access rfl (by omega) hkl
    hom.not_access))
  have hsm : ScopesMeet L .cluster (S.cons b) .cluster (S.prod a) := by
    obtain ⟨nw, mw, -, ⟨pcw, pw, hget⟩, -⟩ := hom
    have hct : S.cons b < L.threads := by
      rcases hR with ⟨d, sp, ac, mk, pc', hmi⟩ | ⟨c, pc', hci⟩ | ⟨s, pc', hsi⟩
      · exact Frame.lt_of_get hX hmi
      · exact Frame.lt_of_get hX hci
      · exact Frame.lt_of_get hX hsi
    exact scopes_meet hX hct hget rfl (H.cluster a b).symm
  exact ⟨⟨hca, hcb, Or.inl ⟨_, .inr ⟨.cluster, hom, hsm⟩, hbo⟩⟩, _, _, hom⟩

end
end PTX.PairTmaRing
