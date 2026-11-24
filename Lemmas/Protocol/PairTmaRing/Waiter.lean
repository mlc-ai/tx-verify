-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Blocker

@[expose] public section

/-! # Any poller of a pair TMA ring slot's empty barrier, blocked

A proof tool over `Hyp`, for a slot with one consumer. `producer_blocker` names the blocker of
the producer thread itself; here the poller `g` of `empty a` is any thread (in a kernel, any lane
of the producer's warp), and `K` its successful polls of `empty a`. When the barrier's final
phase has the parity of `K + 1` (the parity `g`'s next poll does not find), one of three holds
(`waiter_short`):

* the consumer has made fewer than `K` commits to the slot (`C + 1 ≤ K`);
* some commit has not notified one of its targets (an open commit delivery);
* producer `a` has issued at least the copies of `K + 1` uses on the full barrier.

The barrier counts one arrival per phase, and its arrivals are exactly the consumer's
notifications (`units_eq_notes`), so its phase is their number. With every commit notified, the
consumer's commits to the slot are its notifications of `empty a` (`commits_le_notes`, given that
each such commit targets `empty a` by the rank of `a`), so the phase is at least `K`, hence, by
its parity, at least `K + 1`. The consumer's commit with `K` earlier ones then follows its
successful poll of the full barrier for use `K` (the commit's notification record, `Hyp`), and a
consumer poll for use `K` needs producer `a`'s copies of that use (`tail_unobserved`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
variable {S : Slot 1}

/-- **The arrivals on an empty barrier are the consumer's notifications.** -/
theorem units_eq_notes (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) (a : Fin 2) :
    arrivalUnits (X.objects (S.empty a)) =
      (X.objects (S.empty a)).countP (notifies S a 0) := by
  refine Nat.le_antisymm ?_ ?_
  · rw [arrivalUnits_eq_length (fun r hr c' tx _ ha => (notify_consumer H hr ha).1),
      ← List.countP_eq_length_filter]
    refine List.countP_mono_left fun x hx hc => ?_
    obtain ⟨-, c', tx, ha⟩ := countedArrive_iff.mp hc
    obtain ⟨h1, h0, b, j, pc, sp, hid, -⟩ := notify_consumer H hx ha
    subst h1 h0
    have hb : b = 0 := Subsingleton.elim _ _
    subst hb
    simp [notifies, hid, ha]
  · have h := notes_sum_le hX H (a := a)
    simpa using h

/-- **With every commit notified, the consumer's commits to the slot are at most its
notifications of `empty a`**, when each such commit targets `empty a` by the rank of `a`. -/
theorem commits_le_notes (hX : Consistent L K A mem0 X) {a : Fin 2}
    (htg : ∀ {j pc : Nat} {sp : TcCommit.Spec}, X.get (S.cons 0, j) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = S.empty 0 → TcCommit.target sp (rankOf a) = some (S.empty a))
    (hall : ∀ i sp rank m, X.Commit i sp → TcCommit.target sp rank = some m →
      rank ∈ X.tcNotified i) :
    (X.tr (S.cons 0)).countP (commitsTo (S.empty 0)) ≤
      (X.objects (S.empty a)).countP (notifies S a 0) := by
  refine countP_le_of_records (fun k => Ref.async (S.cons 0, k) (.tcNotify (rankOf a)))
    (fun i j _ _ hij => by simpa using hij) (fun k hk => ?_)
  obtain ⟨⟨pc, kind⟩, he, hp⟩ := (mem_indicesP_iff _ _ k).mp hk
  cases kind with
  | tc op =>
    cases op with
    | commit sp =>
      have hmb : sp.mbar = S.empty 0 := by simpa [commitsTo] using hp
      have hget : X.get (S.cons 0, k) = some ⟨pc, .tc (.commit sp)⟩ := he
      have ht := htg hget hmb
      have hn := hall _ sp _ _ ⟨pc, hget⟩ ht
      have hact : objectAction X X.async (S.empty a)
          (.async (S.cons 0, k) (.tcNotify (rankOf a))) = some (.arrive 1 0) := by
        simp only [objectAction, hget, ht, hn, and_self, ite_true]
      obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 _).2.2 _ _ hact
      have hra := ((hX.tma.2.2.1 _).2.1 r hr).1
      rw [hid, hact, Option.some.injEq] at hra
      refine ⟨r, hr, hid, ?_⟩
      simp [notifies, hid, ← hra]
    | _ => simp [commitsTo] at hp
  | _ => simp [commitsTo] at hp

/-- **A blocked poller of an empty barrier.** When `empty a` ends in a phase of the parity of
`K + 1`, `K` thread `g`'s successful polls of it, the consumer has made fewer than `K` commits to
the slot, or a commit has an undelivered target, or producer `a` has issued the copies of `K + 1`
uses. -/
theorem waiter_short (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {g : Nat}
    {before : State}
    (hstate : stateBefore (X.objects (S.empty a)) (X.objects (S.empty a)).length = some before)
    (hpar : before.phase % 2 = (okPolls (S.empty a) (X.tr g) + 1) % 2)
    (htg : ∀ {j pc : Nat} {sp : TcCommit.Spec}, X.get (S.cons 0, j) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = S.empty 0 → TcCommit.target sp (rankOf a) = some (S.empty a)) :
    (X.tr (S.cons 0)).countP (commitsTo (S.empty 0)) + 1 ≤ okPolls (S.empty a) (X.tr g) ∨
      (¬ ∀ i sp rank m, X.Commit i sp → TcCommit.target sp rank = some m →
        rank ∈ X.tcNotified i) ∨
      S.n * (okPolls (S.empty a) (X.tr g) + 1) ≤ (X.tr (S.prod a)).countP (issuesTo S.full) := by
  set Kp := okPolls (S.empty a) (X.tr g) with hKp
  set C := (X.tr (S.cons 0)).countP (commitsTo (S.empty 0)) with hC
  set N := (X.objects (S.empty a)).countP (notifies S a 0) with hN
  have hphase : before.phase = N := by
    rw [hN, ← units_eq_notes hX H a]
    exact (MbarRing.Blocker.units_eq_phase (X.objects_checked hX _) (H.empty_noInval a) hstate
      (empty_tx_zero hX H le_rfl hstate)
      (expected_of_init hX (H.empty_init a) (H.empty_noInval a) hstate)
      (empty_noIncrement H a)).symm
  have hNC : N ≤ C := notified_commits hX H (jr := (X.objects (S.empty a)).length)
    (by rw [List.take_length])
  by_cases h1 : C + 1 ≤ Kp
  · exact .inl h1
  refine .inr ?_
  by_cases hall : ∀ i sp rank m, X.Commit i sp → TcCommit.target sp rank = some m →
      rank ∈ X.tcNotified i
  swap
  · exact .inl hall
  refine .inr ?_
  have hCN : C ≤ N := commits_le_notes hX htg hall
  have hK : Kp < C := by omega
  -- the consumer's commit with `Kp` earlier ones, and its notification of `empty a`
  obtain ⟨e, he, hp, hcnt⟩ := nthEv_spec (p := commitsTo (S.empty 0)) (g := S.cons 0) hK
  set jK := nthEv X (commitsTo (S.empty 0)) (S.cons 0) Kp
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | tc op =>
    cases op with
    | commit sp =>
      have hmb : sp.mbar = S.empty 0 := by simpa [commitsTo] using hp
      have ht := htg he hmb
      have hn := hall _ sp _ _ ⟨pc, he⟩ ht
      have hact : objectAction X X.async (S.empty a)
          (.async (S.cons 0, jK) (.tcNotify (rankOf a))) = some (.arrive 1 0) := by
        simp only [objectAction, he, ht, hn, and_self, ite_true]
      obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 _).2.2 _ _ hact
      have hra := ((hX.tma.2.2.1 _).2.1 r hr).1
      rw [hid, hact, Option.some.injEq] at hra
      obtain ⟨-, -, b, j, -, -, hid', -, -, -, hbud⟩ := notify_consumer H hr hra.symm
      rw [hid] at hid'
      simp only [Ref.async.injEq, Prod.mk.injEq, and_true] at hid'
      obtain ⟨hb, rfl⟩ := hid'
      have hb0 : b = 0 := Subsingleton.elim _ _
      subst hb0
      rw [hcnt] at hbud
      have hpm := okPolls_take_le S.full (X.tr (S.cons 0)) jK
      by_contra hc
      have := tail_unobserved hX H (a := a) (u := Kp) (by omega) 0
      omega
    | _ => simp [commitsTo] at hp
  | _ => simp [commitsTo] at hp

end
end PTX.PairTmaRing
