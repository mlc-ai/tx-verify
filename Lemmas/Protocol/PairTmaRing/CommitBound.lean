-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Blocker
public import Lemmas.Kernel.Obligation

@[expose] public section

/-! # A pair TMA ring slot's full barrier is bounded by a consumer's commits

A proof tool over `Hyp`. The phase of the full barrier is at most one more than consumer `b`'s
commits to the slot (`full_phase_le_commits`): its arrival units are the leader producer's
arrivals (`units_le_arrivals`), each made after more successful polls of the leader's empty
barrier than its earlier arrivals (`arrivals_le_okPolls`), and the producer's poll for a use
`N ≥ 1` found `N` notifications of each consumer, each of a distinct commit
(`okPolls_le_commits`).

So a thread whose next poll of the full barrier has the parity of a number `n` at least `b`'s
commits, when the barrier's phase has that parity, waits on a short use
(`full_blocked_of_commits`): the phase is at most `n`, and either the leader producer has made at
most `n` arrivals, or some producer has issued fewer than `n + 1` uses' copies, or a copy issued
on the barrier has not completed (an open tensor obligation). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
variable {nc : Nat} {S : Slot nc}

/-- A counted arrival record of the full barrier is the record of an arrival of the leader
producer. -/
theorem full_arrive_record (H : Hyp L K A X S) {x : Record Ref} (hx : x ∈ X.objects S.full)
    (hc : countedArrive x = true) :
    ∃ j pc rel sc, x.id = .thread (S.prod 0, j) ∧
      X.get (S.prod 0, j) = some ⟨pc, .arrive S.full S.tx 1 rel sc⟩ := by
  obtain ⟨-, c', tx, ha⟩ := countedArrive_iff.mp hc
  cases H.full_src x hx with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ ha' => rw [ha] at ha'; cases ha'
  | @arrive j pc rel sc hid he _ _ => exact ⟨j, pc, rel, sc, hid, he⟩

/-- The arrival units of the full barrier are at most the leader producer's arrivals. -/
theorem units_le_arrivals (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) :
    arrivalUnits (X.objects S.full) ≤ arrivals S.full (X.tr (S.prod 0)) := by
  classical
  rw [arrivalUnits_eq_length (fun r hr c' tx _ ha => (arrival_producer H hr ha).1)]
  have hnd : (X.objects S.full).Nodup := List.Nodup.of_map _ (hX.tma.2.2.1 S.full).1.1
  let f : Record Ref → Nat := fun x => match x.id with
    | .thread i => i.2
    | _ => 0
  have hle := MbarRing.Slot.length_le_countP_take ((X.objects S.full).filter countedArrive)
    (hnd.filter _) (X.tr (S.prod 0)) (arrivesOn S.full) (X.tr (S.prod 0)).length f ?_ ?_
  · rw [List.take_length] at hle
    exact hle
  · intro x hx
    obtain ⟨hxm, hxc⟩ := List.mem_filter.mp hx
    obtain ⟨j, pc, rel, sc, hid, he⟩ := full_arrive_record H hxm hxc
    have hfx : f x = j := by simp only [f, hid]
    rw [hfx]
    refine ⟨len_of_get he, ?_⟩
    change (X.get (S.prod 0, j)).any _ = true
    rw [he]
    simp [arrivesOn, sourceArrive]
  · intro x hx y hy hxy
    obtain ⟨hxm, hxc⟩ := List.mem_filter.mp hx
    obtain ⟨hym, hyc⟩ := List.mem_filter.mp hy
    obtain ⟨j, -, -, -, hid, -⟩ := full_arrive_record H hxm hxc
    obtain ⟨j', -, -, -, hid', -⟩ := full_arrive_record H hym hyc
    have h1 : f x = j := by simp only [f, hid]
    have h2 : f y = j' := by simp only [f, hid']
    rw [h1, h2] at hxy
    subst hxy
    exact hX.record_eq hxm hym (hid.trans hid'.symm)

/-- The leader producer's arrivals on the full barrier are at most its successful polls of its
empty barrier. -/
theorem arrivals_le_okPolls (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) :
    arrivals S.full (X.tr (S.prod 0)) ≤ okPolls (S.empty 0) (X.tr (S.prod 0)) := by
  by_contra hlt
  obtain ⟨j, x, hx, hp, hc⟩ := MbarRing.Slot.exists_nth_countP (arrivesOn S.full)
    (xs := X.tr (S.prod 0)) (c := arrivals S.full (X.tr (S.prod 0)) - 1)
    (by unfold arrivals at hlt ⊢; omega)
  obtain ⟨pc, k⟩ := x
  cases k with
  | arrive m tx cnt rel sc =>
    have hm : m = S.full := by simpa [arrivesOn, sourceArrive] using hp
    subst hm
    have hget : X.get (S.prod 0, j) = some ⟨pc, .arrive S.full tx cnt rel sc⟩ := hx
    have hact : objectAction X X.async S.full (Ref.thread (S.prod 0, j)) =
        some (.arrive cnt tx) := by
      simp [objectAction, hget]
    obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 S.full).2.2 (Ref.thread (S.prod 0, j)) _ hact
    have hact' := ((hX.tma.2.2.1 S.full).2.1 r hr).1
    rw [hid, hact] at hact'
    have ha : r.action = .arrive cnt tx := (Option.some.inj hact').symm
    cases H.full_src r hr with
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | copy _ _ _ ha' => rw [ha] at ha'; cases ha'
    | @arrive j' pc' rel' sc' hid' _ _ hb =>
      rw [hid] at hid'
      simp only [Ref.thread.injEq, Prod.mk.injEq, true_and] at hid'
      subst hid'
      have hpm := okPolls_take_le (S.empty 0) (X.tr (S.prod 0)) j
      simp only [arrivals] at hb hlt hc
      omega
  | _ => simp [arrivesOn, sourceArrive] at hp

/-- **A producer's successful empty polls are at most one more than a consumer's commits.** -/
theorem okPolls_le_commits (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) (a : Fin 2)
    (b : Fin nc) :
    okPolls (S.empty a) (X.tr (S.prod a)) ≤
      (X.tr (S.cons b)).countP (commitsTo (S.empty 0)) + 1 := by
  by_contra hlt
  set N := okPolls (S.empty a) (X.tr (S.prod a)) with hN
  obtain ⟨pc, p, acq, sc, hwl, hcnt⟩ := MbarRing.Poll.nth_spec (X := X) (m := S.empty a)
    (g := S.prod a) (n := N - 1) (by omega)
  obtain ⟨jr, w, -, -, -, -, -, hge⟩ := producer_poll hX H hwl (q := N - 2)
    (by rw [hcnt]; omega)
  have := notified_commits hX H (hge b)
  omega

/-- **The full barrier's phase is at most one more than a consumer's commits.** -/
theorem full_phase_le_commits (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) (b : Fin nc)
    {before : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some before) :
    before.phase ≤ (X.tr (S.cons b)).countP (commitsTo (S.empty 0)) + 1 := by
  have h1 := full_short hX H hst
  have h2 := units_le_arrivals hX H
  have h3 := arrivals_le_okPolls hX H
  have h4 := okPolls_le_commits hX H 0 b
  omega

/-- **A blocked full barrier below a consumer's commits.** When the full barrier's phase has
the parity of a number `n` at least consumer `b`'s commits, the leader producer has made at most
`n` arrivals, or some producer has issued fewer than `n + 1` uses' copies on the barrier, or a
tensor copy has not completed. -/
theorem full_blocked_of_commits (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) (b : Fin nc)
    {before : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some before) {n : Nat}
    (hC : (X.tr (S.cons b)).countP (commitsTo (S.empty 0)) ≤ n)
    (hpar : before.phase % 2 = n % 2) :
    arrivals S.full (X.tr (S.prod 0)) ≤ n ∨
      (∃ a, (X.tr (S.prod a)).countP (issuesTo S.full) < S.n * (n + 1)) ∨
      Descent.Obl L X .tensor := by
  have hle : before.phase ≤ n := by
    have := full_phase_le_commits hX H b hst
    omega
  rcases full_short hX H hst with hu | ⟨hu, hcomp⟩
  · left
    have := arrivals_le_units hX H (S.prod 0)
    omega
  · right
    by_cases hobl : Descent.Obl L X .tensor
    · exact .inr hobl
    · left
      have hall : ∀ i ma s, X.TensorIssue i ma s →
          ∃ obs, X.tensor i = some obs ∧ obs.effects.notified = true := by
        simpa [Descent.Obl] using hobl
      have hM : ∀ i ma s, X.TensorIssue i ma s → s.mbar = S.full →
          ∃ r ∈ X.objects S.full, r.id = .async i (.notify .load) := by
        intro i ma s hT hmb
        by_contra hno
        push Not at hno
        exact unnotified hX hT hmb hno (hall i ma s hT)
      have hsum := issues_le_completions hX H (h0 := S.prod 0) (h1 := S.prod 1)
        (fun h => absurd (H.prod_inj h) (by decide)) hM
      have hmul : 2 * S.n * (before.phase + 1) ≤ 2 * (S.n * (n + 1)) := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega))
      by_contra hno
      push Not at hno
      have a0 := hno 0
      have a1 := hno 1
      omega

end
end PTX.PairTmaRing
