-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

/-! # A producer's last empty poll observes every notification

A proof tool over `Hyp`. Consumer `b`'s notifications of `empty a` are at most its successful
full polls (`notes_le_okPolls`): each is of a distinct commit of `b` to the slot, made within
its budget (fewer earlier commits than successful full polls). When every consumer's successful
full polls are fewer than producer `a`'s successful empty polls `N` (as after a drain whose use
no consumer observed), the producer's last successful empty poll, the one with `N - 1` earlier
ones, has every notification of the barrier before its record (`last_poll_observes`): it found
at least `N - 1` of them (`producer_poll`), and there are at most `N - 1`. -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
variable {nc : Nat} {S : Slot nc}

/-- A notification of consumer `b` on `empty a` is of a commit of `b` within its budget. -/
theorem notifies_budget (H : Hyp L K A X S) {a : Fin 2} {b : Fin nc} {x : Record Ref}
    (hx : x ∈ X.objects (S.empty a)) (hn : notifies S a b x = true) :
    ∃ jc pc sp, x.id = .async (S.cons b, jc) (.tcNotify (rankOf a)) ∧
      X.get (S.cons b, jc) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = S.empty 0 ∧
      ((X.tr (S.cons b)).take jc).countP (commitsTo (S.empty 0)) + 1 ≤
        okPolls S.full ((X.tr (S.cons b)).take jc) := by
  obtain ⟨jc, pc, sp, hid, he, hm⟩ := notifies_commit H hx hn
  refine ⟨jc, pc, sp, hid, he, hm, ?_⟩
  cases H.empty_src a x hx with
  | init ha | poll _ _ ha =>
    simp only [notifies, hid] at hn
    simp_all
  | @notify b' j pc' sp' hid' he' hm' htg ha hb =>
    rw [hid] at hid'
    simp only [Ref.async.injEq, Prod.mk.injEq] at hid'
    obtain ⟨⟨hbb, rfl⟩, -⟩ := hid'
    rw [hbb]
    exact hb

/-- **Consumer `b`'s notifications of `empty a` are at most its successful full polls.** -/
theorem notes_le_okPolls (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    (b : Fin nc) :
    (X.objects (S.empty a)).countP (notifies S a b) ≤ okPolls S.full (X.tr (S.cons b)) := by
  classical
  set M := okPolls S.full (X.tr (S.cons b)) with hM
  by_cases hle : (X.tr (S.cons b)).countP (commitsTo (S.empty 0)) ≤ M
  · refine le_trans (notified_commits hX H (a := a) (jr := (X.objects (S.empty a)).length) ?_) hle
    rw [List.take_length]
  · obtain ⟨K, e, -, -, hK⟩ := MbarRing.Slot.exists_nth_countP (commitsTo (S.empty 0))
      (xs := X.tr (S.cons b)) (c := M) (by omega)
    have hnd : (X.objects (S.empty a)).Nodup :=
      List.Nodup.of_map _ (hX.tma.2.2.1 (S.empty a)).1.1
    let f : Record Ref → Nat := fun x => match x.id with
      | .async i _ => i.2
      | _ => 0
    have hlen := MbarRing.Slot.length_le_countP_take
      ((X.objects (S.empty a)).filter (notifies S a b)) (hnd.filter _) (X.tr (S.cons b))
      (commitsTo (S.empty 0)) K f ?_ ?_
    · rw [← List.countP_eq_length_filter] at hlen
      omega
    · intro x hx
      obtain ⟨hxm, hxn⟩ := List.mem_filter.mp hx
      obtain ⟨jc, pcc, sp, hid, hcm, hmb, hbud⟩ := notifies_budget H hxm hxn
      have hfx : f x = jc := by simp only [f, hid]
      rw [hfx]
      have hpm := okPolls_take_le S.full (X.tr (S.cons b)) jc
      refine ⟨?_, ?_⟩
      · by_contra hge
        have := countP_take_mono (commitsTo (S.empty 0)) (X.tr (S.cons b))
          (show K ≤ jc by omega)
        omega
      · change (X.get (S.cons b, jc)).any _ = true
        rw [hcm]
        simp [commitsTo, hmb]
    · intro x hx y hy hxy
      obtain ⟨hxm, hxn⟩ := List.mem_filter.mp hx
      obtain ⟨hym, hyn⟩ := List.mem_filter.mp hy
      obtain ⟨jc, -, -, hid, -⟩ := notifies_commit H hxm hxn
      obtain ⟨jc', -, -, hid', -⟩ := notifies_commit H hym hyn
      have h1 : f x = jc := by simp only [f, hid]
      have h2 : f y = jc' := by simp only [f, hid']
      rw [h1, h2] at hxy
      subst hxy
      exact hX.record_eq hxm hym (hid.trans hid'.symm)

/-- **The last empty poll observes every notification.** When every consumer's successful full
polls are fewer than producer `a`'s successful empty polls `N`, the producer's poll with `N - 1`
earlier ones exists, and every notification of `empty a` precedes its record. -/
theorem last_poll_observes (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    (hN : ∀ b, okPolls S.full (X.tr (S.cons b)) + 1 ≤ okPolls (S.empty a) (X.tr (S.prod a))) :
    (∃ pc p acq sc, X.get (S.prod a, MbarRing.Poll.nth X (S.empty a) (S.prod a)
      (okPolls (S.empty a) (X.tr (S.prod a)) - 1)) = some ⟨pc, .wait (S.empty a) p true acq sc⟩) ∧
    ∀ jr w, (X.objects (S.empty a))[jr]? = some w →
      w.id = .thread (S.prod a, MbarRing.Poll.nth X (S.empty a) (S.prod a)
        (okPolls (S.empty a) (X.tr (S.prod a)) - 1)) →
      ∀ b, ((X.objects (S.empty a)).take jr).countP (notifies S a b) =
        (X.objects (S.empty a)).countP (notifies S a b) := by
  set N := okPolls (S.empty a) (X.tr (S.prod a)) with hNdef
  have hb0 := hN ⟨0, H.nc_pos⟩
  obtain ⟨pc, p, acq, sc, hwl, hcnt⟩ := MbarRing.Poll.nth_spec (X := X) (m := S.empty a)
    (g := S.prod a) (n := N - 1) (by omega)
  refine ⟨⟨pc, p, acq, sc, hwl⟩, fun jr w hjr hwid b => ?_⟩
  have hT := notes_le_okPolls hX H (a := a) b
  have hb := hN b
  have htk : ((X.objects (S.empty a)).take jr).countP (notifies S a b) ≤
      (X.objects (S.empty a)).countP (notifies S a b) :=
    (List.take_sublist _ _).countP_le
  by_cases h2 : 2 ≤ N
  · obtain ⟨jr', w', hjr', hwid', -, -, -, hge⟩ := producer_poll hX H hwl (q := N - 2)
      (by rw [hcnt]; omega)
    have hjj : jr = jr' := object_record_index_unique hX.tma.2.2.1 hjr hjr'
      (hwid.trans hwid'.symm)
    subst hjj
    have := hge b
    omega
  · omega

end
end PTX.PairTmaRing
