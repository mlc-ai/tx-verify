-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Lemmas.Flow.CountTake
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # The correction warps' named-barrier events agree across lanes (`BarAgree`)

A correction thread's named-barrier events are its start barrier, the syncs of its two statistics
barriers (both generations of the first and the last part of each item, one per stage per loop
trip) and its end barrier (`corr_bar`); each is fixed by its site (`barEv`). Its count of earlier
named-barrier events is the sum of the four counts of `Correction.Counts` (`corr_barCount`), a
function of the site, the item and the trip (`barPos`) that is one-to-one on the barrier sites
given the item count and the trips. Two lanes of a warp have one cluster, so one item count, and
one warp index, so their `n`-th named-barrier events are one event (`Cross.barAgree_corr`).

A correction poll's site is fixed by its position (the five poll sites are at distinct positions),
so its object is (`corr_wait`). Its parity is its item's: at an O-full or stage-0 free poll the
item is the round (the object is polled at that position only, `Counts.oFull`, `Counts.oFree`);
at a stage-1 free poll the round as well, since the tail's polls of the object come after the last
item (`Counts.oFree` is monotone); at the tail it is the item count. Hence two lanes polling at
one position in one round poll one object with one parity (`Cross.pollAgree_corr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The named-barrier event of a correction barrier site. -/
def barEv (L : Launch) (g : Nat) : Correction.Site → Event
  | .bar0 => ⟨(Correction.Site.bar0).pc, .bar 2 (some 416) .sync⟩
  | .sync st gen => ⟨(Correction.Site.sync st gen).pc,
      .bar (Correction.kOf L g + 3 + 4 * st.val) (some 64) .sync⟩
  | .barEnd => ⟨(Correction.Site.barEnd).pc, .bar 2 (some 416) .arrive⟩
  | s => ⟨s.pc, .exit⟩

/-- The named-barrier events before a barrier site: `1 + (2 n + 2) i` before an item's syncs. -/
def barPos (L : Launch) (d : Correction.D) : Nat :=
  let n := Correction.trips L
  match d.site with
  | .sync 0 .first => 1 + (2 * n + 2) * d.i
  | .sync 1 .first => 1 + (2 * n + 2) * d.i + 1
  | .sync st .loop => 1 + (2 * n + 2) * d.i + (2 + 2 * d.t + st.val)
  | .sync st .last => 1 + (2 * n + 2) * d.i + (2 * n + st.val)
  | .barEnd => 1 + (2 * n + 2) * d.i
  | _ => 0

theorem barIs_both {id id' c c' : Nat} {m m' : BarMode} {x : Event} (h1 : barIs id c m x = true)
    (h2 : barIs id' c' m' x = true) : id = id' ∧ m = m' := by
  obtain ⟨pc, k⟩ := x
  cases k <;> simp only [barIs, Bool.false_eq_true] at h1 h2
  rename_i i0 cnt m0
  cases cnt <;> simp_all

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A correction thread's named-barrier event is its barrier site's.** -/
theorem corr_bar_ev {g i : Nat} {x : Event} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (hx : X.get (g, i) = some x) (hb : Execution.isBar x = true) :
    ∃ d : Correction.D, Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧
      (d.site = .bar0 ∨ (∃ st gen, d.site = .sync st gen) ∨ d.site = .barEnd) ∧
      x = barEv L g d.site := by
  obtain ⟨pc, k⟩ := x
  cases k <;> simp only [Execution.isBar, Bool.false_eq_true] at hb
  rename_i id cnt m
  rcases corr_origin hpre hX ht hx hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, -, hc, hi, -, -, -, hev⟩
  · cases hk
  obtain ⟨hpc, hk⟩ := hev (by simp)
  obtain ⟨site, i', tt, aw, a, o'⟩ := d
  simp only at hpc
  subst hpc
  cases site
  case bar0 => exact ⟨_, hc, hi, .inl rfl, by simp only at hk; rw [hk]; rfl⟩
  case sync st gen =>
    exact ⟨_, hc, hi, .inr (.inl ⟨st, gen, rfl⟩), by simp only at hk; rw [hk]; rfl⟩
  case barEnd => exact ⟨_, hc, hi, .inr (.inr rfl), by simp only at hk; rw [hk]; rfl⟩
  all_goals exfalso
  all_goals simp at hk

/-- **A correction thread's count of named-barrier events** is the sum of its counts of the start
and end barriers and of the syncs of its two statistics barriers. -/
theorem corr_barCount {g : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (i : Nat) :
    ((X.tr g).take i).countP Execution.isBar =
      barEvents 2 416 .sync ((X.tr g).take i) + barEvents 2 416 .arrive ((X.tr g).take i) +
        barEvents (Correction.kOf L g + 3 + 4 * 0) 64 .sync ((X.tr g).take i) +
        barEvents (Correction.kOf L g + 3 + 4 * 1) 64 .sync ((X.tr g).take i) := by
  have hkw := corr_kOf hw hw'
  have hk4 := corr_kOf hw hw'
  unfold barEvents
  rw [← countP_or_disj, ← countP_or_disj, ← countP_or_disj]
  · apply List.countP_congr
    intro x hx
    obtain ⟨j, -, hj⟩ := get_of_mem_take hx
    obtain ⟨pc, k⟩ := x
    constructor
    · intro h
      cases k <;> simp only [Execution.isBar, Bool.false_eq_true] at h
      rename_i id cnt m
      rcases corr_bar hpre hX ht hw hw' hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl, st, hst, rfl⟩
      · cases m <;> simp [barIs]
      · rcases (show st = 0 ∨ st = 1 by omega) with rfl | rfl <;> simp [barIs] <;> omega
    · intro h
      cases k <;> simp_all [barIs, Execution.isBar]
  · intro x _ ⟨h1, h2⟩
    simp only [Bool.or_eq_true] at h1
    rcases h1 with (h1 | h1) | h1 <;> obtain ⟨he, hm⟩ := barIs_both h1 h2 <;> omega
  · intro x _ ⟨h1, h2⟩
    simp only [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1 <;> obtain ⟨he, hm⟩ := barIs_both h1 h2 <;> omega
  · intro x _ ⟨h1, h2⟩
    obtain ⟨he, hm⟩ := barIs_both h1 h2
    cases hm

/-- **The count of named-barrier events at a correction barrier site** is its `barPos`. -/
theorem corr_barPos {g i : Nat} {d : Correction.D} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (hc : Correction.Counts L g d ((X.tr g).take i)) (hi : Correction.Inv L g d)
    (hs : d.site = .bar0 ∨ (∃ st gen, d.site = .sync st gen) ∨ d.site = .barEnd) :
    ((X.tr g).take i).countP Execution.isBar = barPos L d := by
  rw [corr_barCount hpre hX ht hw hw' i, hc.bar2.1, hc.bar2.2, hc.sync 0 (by decide),
    hc.sync 1 (by decide)]
  have hst0 := hi.start
  obtain ⟨site, i', tt, aw, a, o⟩ := d
  simp only at hs hst0 ⊢
  rcases hs with rfl | ⟨st, gen, rfl⟩ | rfl
  · obtain rfl := hst0 (.inr (.inl rfl))
    simp [Correction.bar2Sync, Correction.bar2Arrive, Correction.syncPos, barPos]
  · fin_cases st <;> cases gen <;>
      simp [Correction.bar2Sync, Correction.bar2Arrive, Correction.syncPos, barPos] <;> ring
  · simp [Correction.bar2Sync, Correction.bar2Arrive, Correction.syncPos, barPos]; ring

/-- **`BarAgree`, correction part**: two lanes of a correction warp make one named-barrier event
as their `n`-th. -/
theorem Cross.barAgree_corr {g h i j : Nat} {x y : Event} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hsw : SameWarp L g h) (hx : X.get (g, i) = some x)
    (hy : X.get (h, j) = some y) (hbx : Execution.isBar x = true)
    (hby : Execution.isBar y = true)
    (hcnt : ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar) :
    x = y := by
  obtain ⟨⟨-, -, hcta⟩, hwarp⟩ := hsw
  have hwh : warpOf L h = warpOf L g := by simp only [warpOf]; omega
  have hkk : Correction.kOf L h = Correction.kOf L g := by
    simp only [Correction.kOf, Correction.tidOf]; omega
  have hitems : Correction.items L h = Correction.items L g := by
    simp only [Correction.items, clusterOf, ctaOf] at *; rw [hcta]
  obtain ⟨d, hc, hi, hs, rfl⟩ := corr_bar_ev hpre hX ht hw hw' hx hbx
  obtain ⟨d', hc', hi', hs', rfl⟩ := corr_bar_ev hpre hX ht (by omega) (by omega) hy hby
  rw [corr_barPos hpre hX ht hw hw' hc hi hs,
    corr_barPos hpre hX ht (by omega) (by omega) hc' hi' hs'] at hcnt
  have hT := corr_trips_pos hpre
  have hbE : d.site = .barEnd → d.i = Correction.items L g := fun h =>
    hi.tail (by rw [h]; rfl) (by rw [h]; simp) (by rw [h]; simp) (fun _ => by rw [h]; simp)
  have hbE' : d'.site = .barEnd → d'.i = Correction.items L h := fun h' =>
    hi'.tail (by rw [h']; rfl) (by rw [h']; simp) (by rw [h']; simp) (fun _ => by rw [h']; simp)
  have ha := hi.item
  have ha' := hi'.item
  have hb := hi.tail
  have hb' := hi'.tail
  have hc0 := hi.trip
  have hc0' := hi'.trip
  obtain ⟨site, I, t, aw, a, o⟩ := d
  obtain ⟨site', I', t', aw', a', o'⟩ := d'
  simp only at hs hs' ha ha' hb hb' hc0 hc0' hcnt hbE hbE' ⊢
  rw [hitems] at ha' hb' hbE'
  have hsep : (I = I' ∧ (2 * Correction.trips L + 2) * I = (2 * Correction.trips L + 2) * I') ∨
      (I < I' ∧ (2 * Correction.trips L + 2) * I + (2 * Correction.trips L + 2) ≤
        (2 * Correction.trips L + 2) * I') ∨
      (I' < I ∧ (2 * Correction.trips L + 2) * I' + (2 * Correction.trips L + 2) ≤
        (2 * Correction.trips L + 2) * I) := by
    rcases Nat.lt_trichotomy I I' with hlt | rfl | hlt
    · have := Nat.mul_le_mul_left (2 * Correction.trips L + 2) (show I + 1 ≤ I' by omega)
      rw [Nat.mul_add] at this; omega
    · exact .inl ⟨rfl, rfl⟩
    · have := Nat.mul_le_mul_left (2 * Correction.trips L + 2) (show I' + 1 ≤ I by omega)
      rw [Nat.mul_add] at this; omega
  have hst0 := hi.start
  have hst0' := hi'.start
  simp only at hst0 hst0'
  rcases hs with rfl | ⟨st, gen, rfl⟩ | rfl <;> rcases hs' with rfl | ⟨st', gen', rfl⟩ | rfl
  all_goals (try fin_cases st)
  all_goals (try fin_cases st')
  all_goals (try cases gen)
  all_goals (try cases gen')
  all_goals (try dsimp only at hcnt ha ha' hb hb' hc0 hc0' hbE hbE' ⊢)
  all_goals simp only [Fin.zero_eta, Fin.mk_one, barPos, barEv, Correction.Site.inItem,
    Correction.Site.inTrip,
    Fin.isValue, Fin.val_zero, Fin.val_one, Bool.false_eq_true, IsEmpty.forall_iff,
    forall_const] at hcnt ha ha' hb hb' hc0 hc0' hbE hbE' ⊢
  all_goals (try rw [hkk])
  all_goals (exfalso; omega)


omit hpre hX ht in
/-- The poll sites of the correction are at distinct positions. -/
theorem corr_wait_pc_inj {s s' : Correction.Site}
    (hs : s = .oWait 0 ∨ s = .oWait 1 ∨ s = .fWait 0 ∨ s = .fWait 1 ∨ s = .tailWait)
    (hs' : s' = .oWait 0 ∨ s' = .oWait 1 ∨ s' = .fWait 0 ∨ s' = .fWait 1 ∨ s' = .tailWait)
    (h : s.pc = s'.pc) : s = s' := by
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (revert h; decide)

/-- A correction poll in normal form: its site, object and parity. -/
theorem corr_wait' {g i pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, i) = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ d : Correction.D, Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧
      d.site.pc = pc ∧
      (d.site = .oWait 0 ∨ d.site = .oWait 1 ∨ d.site = .fWait 0 ∨ d.site = .fWait 1 ∨
        d.site = .tailWait) ∧
      m = Correction.ownLoc L g (match d.site with
        | .oWait st => 192 + 8 * st.val | .fWait st => 272 + 8 * st.val | _ => 280) ∧
      p = (match d.site with | .oWait _ => d.i % 2 | _ => (d.i + 1) % 2) := by
  obtain ⟨d, -, hc, hi, hpc, hs⟩ := corr_wait hpre hX ht hw hw' he
  refine ⟨d, hc, hi, hpc, ?_⟩
  rcases hs with ⟨st, hsd, rfl, rfl⟩ | ⟨st, hsd, rfl, rfl⟩ | ⟨hsd, rfl, rfl⟩ <;> rw [hsd] <;>
    (try fin_cases st) <;> simp

/-- At a correction poll position, the round counts the successful polls of the position's
object (for the O-full and stage-0 free objects, polled at one position only). -/
theorem corr_round_eq {g k off : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    {s : Correction.Site} (hso : (s = .oWait 0 ∧ off = 192) ∨ (s = .oWait 1 ∧ off = 200) ∨
      (s = .fWait 0 ∧ off = 272)) :
    pollRound s.pc ((X.tr g).take k) = okPolls (Correction.ownLoc L g off) ((X.tr g).take k) := by
  unfold pollRound okPolls
  apply List.countP_congr
  intro x hx
  obtain ⟨j, -, hj⟩ := get_of_mem_take hx
  obtain ⟨xpc, xk⟩ := x
  cases xk
  case wait m' p' ok' acq' sc' =>
    cases ok'
    · simp [okPollAt, okPoll, sourceWaitSuccess]
    · obtain ⟨d, -, -, hpc, hs', hm, -⟩ := corr_wait' hpre hX ht hw hw' hj
      subst hpc
      simp only [okPollAt, okPoll, sourceWaitSuccess, beq_iff_eq, decide_eq_true_eq, hm]
      rcases hso with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hs' with h' | h' | h' | h' | h' <;> rw [h'] <;>
        simp [Correction.ownLoc, Correction.sb, Correction.Site.pc]
  all_goals simp [okPollAt, okPoll, sourceWaitSuccess]

/-- At a stage-1 free poll the round is the item: the tail's polls of the object come after the
last item. -/
theorem corr_round_f1 {g k : Nat} {d : Correction.D} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hc : Correction.Counts L g d ((X.tr g).take k))
    (hi : Correction.Inv L g d) (hs : d.site = .fWait 1) :
    pollRound (Correction.Site.fWait 1).pc ((X.tr g).take k) = d.i := by
  have hof : okPolls (Correction.ownLoc L g (272 + 8 * 1)) ((X.tr g).take k) = d.i := by
    have := hc.oFree 1 (by decide)
    simp only [Correction.fPos, hs] at this
    simpa using this
  rw [← hof]
  unfold pollRound okPolls
  apply List.countP_congr
  intro x hx
  obtain ⟨j, hjk, hj⟩ := get_of_mem_take hx
  obtain ⟨xpc, xk⟩ := x
  cases xk
  case wait m' p' ok' acq' sc' =>
    cases ok'
    · simp [okPollAt, okPoll, sourceWaitSuccess]
    · obtain ⟨d', hc', hi', hpc, hs', hm, -⟩ := corr_wait' hpre hX ht hw hw' hj
      simp only [okPollAt, okPoll, sourceWaitSuccess, beq_iff_eq, decide_eq_true_eq]
      rw [← hpc, hm]
      constructor
      · intro h
        rw [corr_wait_pc_inj hs' (by simp) h]
        simp
      · intro h
        simp only [Correction.ownLoc, Loc.mk.injEq, true_and, Correction.sb] at h
        rcases hs' with h' | h' | h' | h' | h'
        all_goals rw [h'] at h ⊢
        all_goals simp at h ⊢
        -- a tail poll before a stage-1 free poll: the free polls would decrease
        exfalso
        have htl := hi'.tail (by rw [h']; rfl) (by rw [h']; simp) (by rw [h']; simp)
          (fun _ => by rw [h']; simp)
        have hit := hi.item (by rw [hs]; rfl)
        have h1 := hc'.oFree 1 (by decide)
        simp only [Correction.fPos, h'] at h1
        have hmono := countP_take_mono (okPoll (Correction.ownLoc L g (272 + 8 * 1))) (X.tr g)
          hjk.le
        unfold okPolls at h1 hof
        omega
  all_goals simp [okPollAt, okPoll, sourceWaitSuccess]

/-- **`PollAgree`, correction part**: two lanes of a correction warp polling at one position in
one round poll one object with one parity. -/
theorem Cross.pollAgree_corr {g h k k' pc p p' : Nat} {m m' : Loc} {ok ok' acq acq' : Bool}
    {sc sc' : MbarScope} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hsw : SameWarp L g h)
    (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩)
    (hr : pollRound pc ((X.tr g).take k) = pollRound pc ((X.tr h).take k')) :
    m = m' ∧ p % 2 = p' % 2 := by
  obtain ⟨⟨-, -, hcta⟩, hwarp⟩ := hsw
  have hwh : warpOf L h = warpOf L g := by simp only [warpOf]; omega
  have hitems : Correction.items L h = Correction.items L g := by
    simp only [Correction.items, clusterOf, ctaOf] at *; rw [hcta]
  have hctah : ctaOf L h = ctaOf L g := by simp only [ctaOf]; omega
  obtain ⟨d, hc, hi, hpc, hs, rfl, rfl⟩ := corr_wait' hpre hX ht hw hw' he
  obtain ⟨d', hc', hi', hpc', hs', rfl, rfl⟩ := corr_wait' hpre hX ht (by omega) (by omega) he'
  have hss := corr_wait_pc_inj hs hs' (hpc.trans hpc'.symm)
  have hown : ∀ off, Correction.ownLoc L h off = Correction.ownLoc L g off := fun off => by
    simp only [Correction.ownLoc, hctah]
  refine ⟨by rw [hss, hown], ?_⟩
  rw [← hss] at hs' ⊢
  rcases hs with hsd | hsd | hsd | hsd | hsd
  · have r1 := corr_round_eq hpre hX ht (k := k) hw hw' (.inl ⟨hsd, rfl⟩)
    have r2 := corr_round_eq hpre hX ht (k := k') (g := h) (by omega) (by omega)
      (.inl ⟨hss ▸ hsd, rfl⟩)
    have o1 : okPolls (Correction.ownLoc L g 192) ((X.tr g).take k) = d.i + Correction.oPos 0 d :=
      hc.oFull 0 (by decide)
    have o2 : okPolls (Correction.ownLoc L h 192) ((X.tr h).take k') =
      d'.i + Correction.oPos 0 d' := hc'.oFull 0 (by decide)
    rw [← hpc] at hr
    rw [hsd] at hr r1
    rw [← hss, hsd] at r2
    rw [r1, r2, o1, o2, Correction.oPos, Correction.oPos, hsd, ← hss, hsd] at hr
    rw [hsd]; simp only at hr ⊢; omega
  · have r1 := corr_round_eq hpre hX ht (k := k) hw hw' (.inr (.inl ⟨hsd, rfl⟩))
    have r2 := corr_round_eq hpre hX ht (k := k') (g := h) (by omega) (by omega)
      (.inr (.inl ⟨hss ▸ hsd, rfl⟩))
    have o1 : okPolls (Correction.ownLoc L g 200) ((X.tr g).take k) = d.i + Correction.oPos 1 d :=
      hc.oFull 1 (by decide)
    have o2 : okPolls (Correction.ownLoc L h 200) ((X.tr h).take k') =
      d'.i + Correction.oPos 1 d' := hc'.oFull 1 (by decide)
    rw [← hpc] at hr
    rw [hsd] at hr r1
    rw [← hss, hsd] at r2
    rw [r1, r2, o1, o2, Correction.oPos, Correction.oPos, hsd, ← hss, hsd] at hr
    rw [hsd]; simp only at hr ⊢; omega
  · have r1 := corr_round_eq hpre hX ht (k := k) hw hw' (.inr (.inr ⟨hsd, rfl⟩))
    have r2 := corr_round_eq hpre hX ht (k := k') (g := h) (by omega) (by omega)
      (.inr (.inr ⟨hss ▸ hsd, rfl⟩))
    have o1 : okPolls (Correction.ownLoc L g 272) ((X.tr g).take k) = d.i + Correction.fPos 0 d :=
      hc.oFree 0 (by decide)
    have o2 : okPolls (Correction.ownLoc L h 272) ((X.tr h).take k') =
      d'.i + Correction.fPos 0 d' := hc'.oFree 0 (by decide)
    rw [← hpc] at hr
    rw [hsd] at hr r1
    rw [← hss, hsd] at r2
    rw [r1, r2, o1, o2, Correction.fPos, Correction.fPos, hsd, ← hss, hsd] at hr
    rw [hsd]; simp only at hr ⊢; omega
  · have r1 := corr_round_f1 hpre hX ht hw hw' hc hi hsd
    have r2 := corr_round_f1 hpre hX ht (by omega) (by omega) hc' hi' (hss ▸ hsd)
    rw [← hpc, hsd, r1, r2] at hr
    rw [hsd]; simp only; omega
  · have t1 := hi.tail (by rw [hsd]; rfl) (by rw [hsd]; simp) (by rw [hsd]; simp)
      (fun _ => by rw [hsd]; simp)
    have t2 := hi'.tail (by rw [← hss, hsd]; rfl) (by rw [← hss, hsd]; simp)
      (by rw [← hss, hsd]; simp) (fun _ => by rw [← hss, hsd]; simp)
    rw [hsd]; simp only
    rw [t1, t2, hitems]

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
