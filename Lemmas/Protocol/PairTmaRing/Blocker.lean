-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Final
public import Lemmas.Protocol.PairTmaRing.Order
public import Lemmas.Protocol.MbarRingBlocker
public import Lemmas.Protocol.RecordCountPair

@[expose] public section

/-! # Who blocks a pair TMA ring slot's pollers

A proof tool over `Hyp`, instantiating `MbarRing.Blocker`.

* **Empty barriers.** Consumer `b`'s notifications of `empty a` cover the uses below producer
  `a`'s last successful poll (`notes_ge`), and all consumers' notifications are arrival units
  (`notes_sum_le`). A producer whose barrier ends in the phase its next poll's parity does not
  find has one use outstanding, and some consumer has notified exactly the barrier's phase
  (`producer_blocker`, by `MbarRing.Blocker.exists_eq` with one unit per consumer).
* **The full barrier.** Its last phase awaits the leader producer's arrival or has fewer than
  `2 n` completed copies per phase reached (`full_short`, by `MbarRing.Blocker.tx_short`). A
  thread's arrivals on it are at most its arrival units (`arrivals_le_units`); the copies of two
  threads on it, each notified, are at most its completions (`issues_le_completions`); a copy
  without a notification record is not notified (`unnotified`).
* **A tail arrival.** A final arrival of the leader producer without its use's copies (FA4's
  loader tail) leaves that use's phase unobserved: no consumer completes a poll for a use some
  producer has not issued all its copies of (`tail_unobserved`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

/-- Selections of a list by pairwise disjoint predicates are no more than a selection containing
each. -/
theorem sum_countP_le {κ α : Type} [Fintype κ] (l : List α) (p : κ → α → Bool) (r : α → Bool)
    (hd : ∀ x ∈ l, ∀ k k', p k x = true → p k' x = true → k = k')
    (hr : ∀ x ∈ l, ∀ k, p k x = true → r x = true) :
    ∑ k, l.countP (p k) ≤ l.countP r := by
  classical
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih := ih (fun y hy => hd y (List.mem_cons_of_mem _ hy))
      (fun y hy => hr y (List.mem_cons_of_mem _ hy))
    simp only [List.countP_cons, Finset.sum_add_distrib]
    have h1 : ∑ k, (if p k x = true then 1 else 0) ≤ if r x = true then 1 else 0 := by
      by_cases hx : ∃ k, p k x = true
      · obtain ⟨k, hk⟩ := hx
        rw [Finset.sum_eq_single k (fun k' _ hk' => ite_eq_right_iff.mpr fun h =>
          absurd
          (hd x List.mem_cons_self k' k h hk) hk') (by simp)]
        simp [hk, hr x List.mem_cons_self k hk]
      · push Not at hx
        simp [hx]
    omega

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The action of a tensor copy's notification on an object is a completion. -/
theorem action_completeTx {m : Loc} {i : EvId} {a : MBarrier.Action}
    (h : objectAction X X.async m (.async i (.notify .load)) = some a) :
    ∃ n, a = .completeTx n := by
  simp only [objectAction] at h
  cases hg : X.get i with
  | none => simp [hg] at h
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    cases k with
    | tensorIssue a' s =>
      cases ho : X.tensor i with
      | none => simp [hg, ho] at h
      | some o =>
        by_cases hc : s.mbar = m ∧ o.effects.notified = true
        · simp [hg, ho, hc.1, hc.2] at h
          exact ⟨_, h.symm⟩
        · simp [hg, ho, hc] at h
    | _ => simp [hg] at h

/-- A tensor copy on `m` without a notification record on `m` is not notified. -/
theorem unnotified (hX : Consistent L K A mem0 X) {m : Loc} {i : EvId} {ma : Nat}
    {s : TensorCopy.Spec} (hT : X.TensorIssue i ma s) (hmb : s.mbar = m)
    (hnr : ∀ r ∈ X.objects m, r.id ≠ .async i (.notify .load)) :
    ¬ ∃ obs, X.tensor i = some obs ∧ obs.effects.notified = true := by
  rintro ⟨obs, hobs, hn⟩
  obtain ⟨pc, hget⟩ := hT
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 m).2.2 (Ref.async i (Part.notify .load))
    (.completeTx (TensorTransfer.bytes s.descriptor)) (by simp [objectAction, hget, hobs, hmb, hn])
  exact hnr r hr hid

variable {nc : Nat} {S : Slot nc}

/-! ### Empty barriers -/

/-- Consumer `b`'s notifications of `empty a` cover the uses below producer `a`'s last
successful poll. -/
theorem notes_ge (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} (b : Fin nc)
    {T : Nat} (hT : T + 1 ≤ okPolls (S.empty a) (X.tr (S.prod a))) :
    T ≤ (X.objects (S.empty a)).countP (notifies S a b) := by
  classical
  set log := X.objects (S.empty a) with hlog
  rw [← List.take_length (l := log), MbarRing.Slot.countP_take_card]
  refine le_trans (le_of_eq (Finset.card_range T).symm)
    (card_le_of_rel (Finset.range T) _
      (fun t k => ∃ r, log[k]? = some r ∧ r.id = note X S b a t ∧ (b, t) ∈ SE X S a)
      (fun t ht' => ?_) (fun t _ t' _ k _ ⟨r, hr, hrid, hy⟩ ⟨r', hr', hrid', hy'⟩ => ?_))
  · have htq := Finset.mem_range.mp ht'
    obtain ⟨hy, -, -⟩ := producer_observes hX H (a := a) (n := t) (by omega) b
    obtain ⟨⟨i, r, hi, hid, -, ha⟩, -⟩ := SE_op H hy
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1,
      ?_⟩, r, hi, hid, hy⟩
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

/-- The consumers' notifications of `empty a` are arrival units. -/
theorem notes_sum_le (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} :
    ∑ b, (X.objects (S.empty a)).countP (notifies S a b) ≤
      arrivalUnits (X.objects (S.empty a)) := by
  rw [arrivalUnits_eq_length (fun r hr c' tx hf ha => (notify_consumer H hr ha).1),
    ← List.countP_eq_length_filter]
  refine sum_countP_le _ _ _ (fun x hx k k' h h' => ?_) (fun x hx k h => ?_)
  · obtain ⟨jc, -, -, hid, -⟩ := notifies_commit H hx h
    obtain ⟨jc', -, -, hid', -⟩ := notifies_commit H hx h'
    rw [hid] at hid'
    simp only [Ref.async.injEq, Prod.mk.injEq] at hid'
    exact H.cons_inj hid'.1.1
  · have ha : x.action = .arrive 1 0 := by
      revert h
      unfold notifies
      split <;> simp_all
    exact countedArrive_iff.mpr ⟨fault_free hX H (.inr ⟨a, rfl⟩) hx, 1, 0, ha⟩

/-- **A producer blocked at its empty barrier.** When `empty a` ends in a phase of the parity
producer `a`'s next poll does not find, the producer has one use outstanding, and some consumer
has notified the barrier exactly its phase's number of times. -/
theorem producer_blocker (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    {before : State}
    (hstate : stateBefore (X.objects (S.empty a)) (X.objects (S.empty a)).length = some before)
    (hpar : before.phase % 2 = (okPolls (S.empty a) (X.tr (S.prod a)) + 1) % 2) :
    before.phase + 1 = okPolls (S.empty a) (X.tr (S.prod a)) ∧
      ∃ b : Fin nc, (X.objects (S.empty a)).countP (notifies S a b) = before.phase := by
  obtain ⟨h1, h2⟩ := empty_final_phase hX H hstate
  have hout : before.phase + 1 = okPolls (S.empty a) (X.tr (S.prod a)) := by omega
  refine ⟨hout, ?_⟩
  have hexp := expected_of_init hX (H.empty_init a) (H.empty_noInval a) hstate
  obtain ⟨b, -, hb⟩ := MbarRing.Blocker.exists_eq (X.objects_checked hX _) (H.empty_noInval a)
    hstate (empty_tx_zero hX H (le_refl _) hstate) (fun _ : Fin nc => 1)
    (fun b => (X.objects (S.empty a)).countP (notifies S a b)) (by simp [hexp])
    (by simpa using notes_sum_le hX H) (fun b => notes_ge hX H b (by omega))
    (empty_noIncrement H a)
  exact ⟨b, hb⟩

/-! ### The full barrier -/

/-- **A blocked full barrier awaits its arrival or a copy.** Its last phase either awaits the
leader producer's arrival (the arrival units are the phase number), or has it and fewer than
`2 n` completed copies per phase reached. -/
theorem full_short (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {before : State}
    (hstate : stateBefore (X.objects S.full) (X.objects S.full).length = some before) :
    arrivalUnits (X.objects S.full) = before.phase ∨
      (arrivalUnits (X.objects S.full) = before.phase + 1 ∧
        completedTxCount (X.objects S.full) < 2 * S.n * (before.phase + 1)) := by
  have hcl := completions_le hX H (le_refl _) hstate
  rw [List.take_length] at hcl
  exact MbarRing.Blocker.tx_short (X.objects_checked hX _) H.full_noInval hstate
    (expected_of_init hX H.full_init H.full_noInval hstate) (n := 2 * S.n) (B := S.bytes)
    (by rw [full_expected_bytes H _ (fun _ h => h)]; rfl)
    (fun q hq hf n hn => full_uniform H q hq n hn hf) hcl (full_noIncrement H)

/-- A thread's arrivals on the full barrier are at most its arrival units. -/
theorem arrivals_le_units (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) (h : Nat) :
    arrivals S.full (X.tr h) ≤ arrivalUnits (X.objects S.full) := by
  classical
  rw [arrivalUnits_eq_length (fun r hr c' tx _ ha => (arrival_producer H hr ha).1),
    ← List.countP_eq_length_filter]
  unfold arrivals
  refine countP_le_of_records (fun j => Ref.thread (h, j))
    (fun i j _ _ hf => by simpa using hf) (fun i hi => ?_)
  obtain ⟨⟨pc, kind⟩, he, hp⟩ := (mem_indicesP_iff _ _ i).mp hi
  cases kind with
  | arrive m tx cnt rel sc =>
    have hm : m = S.full := by simpa [arrivesOn, sourceArrive] using hp
    subst hm
    have hget : X.get (h, i) = some ⟨pc, .arrive S.full tx cnt rel sc⟩ := he
    have hact : objectAction X X.async S.full (Ref.thread (h, i)) = some (.arrive cnt tx) := by
      simp [objectAction, hget]
    obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 S.full).2.2 (Ref.thread (h, i)) _ hact
    have hact' := ((hX.tma.2.2.1 S.full).2.1 r hr).1
    rw [hid, hact] at hact'
    exact ⟨r, hr, hid, countedArrive_iff.mpr ⟨fault_free hX H (.inl rfl) hr, cnt, tx,
      (Option.some.inj hact').symm⟩⟩
  | _ => simp [arrivesOn, sourceArrive] at hp

/-- The copies of two distinct threads on the full barrier, when every copy on it has a
notification record, are at most its completions. -/
theorem issues_le_completions (hX : Consistent L K A mem0 X) (H : Hyp L K A X S)
    {h0 h1 : Nat} (hne : h0 ≠ h1)
    (hM : ∀ i ma s, X.TensorIssue i ma s → s.mbar = S.full →
      ∃ r ∈ X.objects S.full, r.id = .async i (.notify .load)) :
    (X.tr h0).countP (issuesTo S.full) + (X.tr h1).countP (issuesTo S.full) ≤
      completedTxCount (X.objects S.full) := by
  classical
  have hrec : ∀ h i, i ∈ indicesP (issuesTo S.full) (X.tr h) → ∃ r ∈ X.objects S.full,
      r.id = Ref.async (h, i) (Part.notify .load) ∧
        (match r.action, r.fault with | .completeTx _, none => true | _, _ => false) = true := by
    intro h i hi
    obtain ⟨⟨pc, kind⟩, he, hp⟩ := (mem_indicesP_iff _ _ i).mp hi
    cases kind with
    | tensorIssue ma s =>
      have hmb : s.mbar = S.full := by simpa [issuesTo] using hp
      obtain ⟨r, hr, hid⟩ := hM (h, i) ma s ⟨pc, he⟩ hmb
      have hact := ((hX.tma.2.2.1 S.full).2.1 r hr).1
      rw [hid] at hact
      obtain ⟨n, hn⟩ := action_completeTx hact
      refine ⟨r, hr, hid, ?_⟩
      rw [hn, fault_free hX H (.inl rfl) hr]
    | _ => simp [issuesTo] at hp
  exact countP_le_of_records_pair (fun k => Ref.async (h0, k) (Part.notify .load))
    (fun k => Ref.async (h1, k) (Part.notify .load)) (fun i j _ _ hf => by simpa using hf)
    (fun i j _ _ hf => by simpa using hf)
    (fun i j _ _ hf => hne (congrArg Prod.fst (Ref.async.inj hf).1)) (hrec h0) (hrec h1)

/-- **A use without all its copies is never observed.** When producer `a` issued fewer than
`n (u + 1)` copies on the full barrier in all (as after a final arrival of use `u` without
copies), no consumer completed a poll for use `u`: every phase from `u` on stays unobserved. -/
theorem tail_unobserved (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {u : Nat}
    (hcopies : (X.tr (S.prod a)).countP (issuesTo S.full) < S.n * (u + 1)) (b : Fin nc) :
    okPolls S.full (X.tr (S.cons b)) ≤ u := by
  by_contra hlt
  have hn := H.n_pos
  have hj : S.n - 1 < S.n := by omega
  have hk0 := copyKind_ne a (S.n - 1) hj
  obtain ⟨hx, -, -⟩ := consumer_observes hX H (b := b) (j := u) (by omega)
    (copyKind S.n a (S.n - 1) hj)
  obtain ⟨-, ⟨e, he, hp, hcnt⟩, -⟩ := SF_op H hx
  simp only [opF_ne hk0, kOwner_copyKind, kPred_ne hk0, kIdx_copyKind] at he hp hcnt
  have h1 := countP_take_succ he hp
  have h2 := countP_take_mono (issuesTo S.full) (X.tr (S.prod a))
    (show _ + 1 ≤ (X.tr (S.prod a)).length from len_of_get he)
  rw [List.take_length] at h2
  dsimp only at h2
  have : S.n * u + (S.n - 1) + 1 = S.n * (u + 1) := by rw [Nat.mul_succ]; omega
  omega

end
end PTX.PairTmaRing
