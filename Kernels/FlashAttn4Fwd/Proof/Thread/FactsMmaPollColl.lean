-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaPollAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.TrackedCount
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaExit

@[expose] public section

/-! # The MMA warp's collectives at its rendezvous polls

At each poll position of the MMA warp in `rdvSites` (EXT-DEPENDENCY-ORDER), the round of
a poll gives the item and the trip (`Counts.pollsAt`, `Mma.round_at`), and the lane's next
shuffle after the poll's success is the first broadcast after the poll site (`Mma.rdvShfl`), of
ordinal `4 + cnt shA (site, i, t)` (the prologue's four shuffles and the role's,
`TrackedCount.shflJ`). So the collective of a round is a function of the position and the round
(`Mma.collOf`):

* before a poll of a later round the lane has made that shuffle (`before`), its shuffles at the
  poll being more;
* when another lane of the warp polls the position in a later round, that lane made the shuffle,
  so this lane made it too (`ShflOk`), after its poll, since it has not yet made it there
  (`after`); the lane did not exit before it, as at its exit it has done every item of its
  cluster.

The MMA warp's other polls are the inner P-ready polls (`p2Wait`), followed by a plain `@p bra`
that is not a poll branch, and the hand-off wait (`waitDealloc`), made once per thread, so in
round 0 (`Cross.PollRest_mma`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The first broadcast after each rendezvous poll site of the MMA warp. -/
def Mma.rdvShfl : Mma.Site → Option Mma.Site
  | .qWait 0 => some (.shfl 0)
  | .kvWait 0 => some (.shfl 0)
  | .qWait 1 => some (.shfl 2)
  | .kvWait 1 => some (.shfl 3)
  | .pWait 0 => some (.shfl 3)
  | .kvWait 2 => some (.shfl 6)
  | .pWait 1 => some (.shfl 7)
  | .kvWait 3 => some (.shfl 9)
  | .pWait 2 => some (.shfl 9)
  | .pWait 3 => some (.shfl 12)
  | _ => none

/-- The rendezvous poll sites. -/
def Mma.rdvSites : List Mma.Site :=
  [.qWait 0, .kvWait 0, .qWait 1, .kvWait 1, .pWait 0, .kvWait 2, .pWait 1, .kvWait 3, .pWait 2,
    .pWait 3]

/-- The item and the trip of round `r` of a poll site. -/
def Mma.roundIT (L : Launch) (s : Mma.Site) (r : Nat) : Nat × Nat :=
  if Mma.region s = 2 then (r / (Mma.trips L - 1), r % (Mma.trips L - 1))
  else (r, if Mma.region s = 1 then 0 else Mma.trips L - 1)

/-- The shuffle ordinal of round `r` at a rendezvous poll site. -/
def Mma.collSite (L : Launch) (s : Mma.Site) (r : Nat) : Nat :=
  match Mma.rdvShfl s with
  | some s' => 4 + Mma.cnt L Mma.shA 6 2
      ⟨s', (Mma.roundIT L s r).1, (Mma.roundIT L s r).2, b32 0, fun _ => b32 0⟩
  | none => 0

/-- The collective of round `r` at position `pc` of the MMA warp. -/
def Mma.collOf (L : Launch) (pc r : Nat) : Bool × Nat :=
  match Mma.rdvSites.find? (fun s => decide (s.pc = pc)) with
  | some s => (false, Mma.collSite L s r)
  | none => (false, 0)

/-- The static facts of the rendezvous poll sites: `rdvSites` names exactly them among the
MMA poll sites; their positions are distinct; their first broadcast is after them in the trip,
fewer than six shuffles later, fewer than eight shuffles into an item part after the loop. -/
theorem Mma.rdv_facts :
    Mma.allSites.all (fun s => !(s.isPoll &&
      rdvPos (s.pc + 1)) || decide (s ∈ Mma.rdvSites)) = true ∧
    Mma.rdvSites.all (fun s => Mma.rdvSites.all fun s' => !decide (s.pc = s'.pc) ||
      decide (s = s')) = true ∧
    Mma.rdvSites.all (fun s => match Mma.rdvShfl s with
      | some s' => decide (Mma.shA s' = Mma.shA s) && (s.loop == s'.loop) && s.isPoll &&
          decide (Mma.region s = 2 ∨ Mma.shA s ≤ 7) && decide (Mma.shA s < 14) &&
          decide (Mma.rdvSites.find? (fun x => decide (x.pc = s.pc)) = some s)
      | none => false) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The facts of one rendezvous poll site. -/
theorem Mma.rdv_site {s : Mma.Site} (hs : s ∈ Mma.rdvSites) :
    ∃ s', Mma.rdvShfl s = some s' ∧ Mma.shA s' = Mma.shA s ∧ s.loop = s'.loop ∧
      s.isPoll = true ∧ (Mma.region s = 2 ∨ Mma.shA s ≤ 7) ∧ Mma.shA s < 14 ∧
      Mma.rdvSites.find? (fun x => decide (x.pc = s.pc)) = some s := by
  have h := List.all_eq_true.mp Mma.rdv_facts.2.2 s hs
  revert h
  cases hr : Mma.rdvShfl s with
  | none => simp
  | some s' =>
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨s', rfl, h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The collective of a rendezvous poll site's round is the shuffle count at the site with the
round's item and trip. -/
theorem Mma.collOf_eq {s : Mma.Site} (hs : s ∈ Mma.rdvSites) (r : Nat) :
    Mma.collOf L s.pc r = (false, 4 + Mma.cnt L Mma.shA 6 2
      ⟨s, (Mma.roundIT L s r).1, (Mma.roundIT L s r).2, b32 0, fun _ => b32 0⟩) := by
  obtain ⟨s', h1, h2, h3, -, -, -, h7⟩ := Mma.rdv_site hs
  simp only [Mma.collOf, h7, Mma.collSite, h1, Mma.cnt, h2, h3]

/-- The round of a poll at a rendezvous site decodes to the state's item and trip. -/
theorem Mma.roundIT_at {g : Nat} {d : Mma.D} (hi : Mma.Inv L g d) (hs : d.site ∈ Mma.rdvSites) :
    Mma.roundIT L d.site (Mma.pollCnt L d.site d) = (d.i, d.t) := by
  obtain ⟨-, -, -, -, hp, -, -, -⟩ := Mma.rdv_site hs
  rcases Mma.round_at hi hp with ⟨hd, -⟩ | ⟨h2, hc, ht⟩ | ⟨h1, hc, ht⟩ | ⟨h3, hc, ht⟩
  · rw [hd] at hs
    simp [Mma.rdvSites] at hs
  · rw [hc]
    simp only [Mma.roundIT, h2, ite_true]
    have hpos : 0 < Mma.trips L - 1 := by omega
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega),
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    simp
  · rw [hc, ht]
    simp [Mma.roundIT, h1]
  · rw [hc]
    simp only [Mma.roundIT, h3]
    simp
    omega

/-- The shuffle counts of a rendezvous site's rounds grow with the round. -/
theorem Mma.cnt_round_lt {g : Nat} {d : Mma.D} (hi : Mma.Inv L g d) (hs : d.site ∈ Mma.rdvSites)
    {r : Nat} (hr : r < Mma.pollCnt L d.site d) :
    Mma.cnt L Mma.shA 6 2
      ⟨d.site, (Mma.roundIT L d.site r).1, (Mma.roundIT L d.site r).2, b32 0, fun _ => b32 0⟩ <
      Mma.cnt L Mma.shA 6 2 d := by
  obtain ⟨-, -, -, -, hp, -, -, -⟩ := Mma.rdv_site hs
  have hIT := Mma.roundIT_at hi hs
  rcases Mma.round_at hi hp with ⟨hd, -⟩ | ⟨h2, hc, ht⟩ | ⟨h1, hc, ht⟩ | ⟨h3, hc, ht⟩
  · rw [hd] at hs
    simp [Mma.rdvSites] at hs
  · have hrt : r < (Mma.trips L - 1) * d.i + d.t := by rw [← hc]; exact hr
    simp only [Mma.roundIT, h2, ite_true, Mma.cnt]
    generalize hn1 : Mma.trips L - 1 = n1 at hrt ⊢
    have hn1p : 0 < n1 := by omega
    have hq := Nat.div_add_mod r n1
    have hρ := Nat.mod_lt r hn1p
    generalize r / n1 = q at hq ⊢
    generalize r % n1 = ρ at hq hρ ⊢
    have hlp : d.site.loop = 1 := by
      unfold Mma.Site.loop
      split_ifs with h
      · rfl
      · exfalso
        obtain ⟨site, _⟩ := d
        simp only at h2 h hs
        simp [Mma.rdvSites] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Mma.Site.ord, Mma.region, Mma.kvOrd, Mma.pOrd]
    rw [hlp, Nat.mul_one, Nat.mul_one]
    rcases Nat.lt_trichotomy q d.i with hlt | heq | hgt
    · have := Nat.mul_le_mul_left (6 * Mma.trips L + 2) (show q + 1 ≤ d.i by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · subst heq
      omega
    · have := Nat.mul_le_mul_left n1 (show d.i + 1 ≤ q by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
  · have hrt : r < d.i := by rw [← hc]; exact hr
    simp [Mma.roundIT, h1, Mma.cnt, ht]
    have := Nat.mul_lt_mul_of_pos_left hrt (show 0 < 6 * Mma.trips L + 2 by omega)
    omega
  · have hrt : r < d.i := by rw [← hc]; exact hr
    simp only [Mma.roundIT, h3, Mma.cnt]
    simp only [show (3 : Nat) ≠ 2 from by decide, show (3 : Nat) ≠ 1 from by decide, ite_false]
    have := Nat.mul_lt_mul_of_pos_left hrt (show 0 < 6 * Mma.trips L + 2 by omega)
    rw [show Mma.trips L - 1 = d.t by omega]
    omega


/-- The part of an item and the loop flag of a rendezvous poll site. -/
theorem Mma.rdv_loop : Mma.rdvSites.all (fun s => (decide (Mma.region s = 1) && s.loop == 0) ||
    (decide (Mma.region s = 2 ∨ Mma.region s = 3) && s.loop == 1)) = true := by
  decide +kernel

/-- **A poll of warp 12 at a rendezvous position**: a rendezvous poll site's, with the thread's
shuffles and its round at the position. -/
theorem rdv_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hw : warpOf L g = 12) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (hu : rdvPos (pc + 1) = true) :
    ∃ d : Mma.D, Frame.stateAt (code L) X g k = some (some (.inr (.mma d))) ∧
      Mma.Counts L g d ((X.tr g).take k) ∧ Mma.Inv L g d ∧ d.site ∈ Mma.rdvSites ∧
      pc = d.site.pc ∧
      ((X.tr g).take k).countP Execution.isShfl = 4 + Mma.cnt L Mma.shA 6 2 d ∧
      pollRound pc ((X.tr g).take k) = Mma.pollCnt L d.site d := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, u, hσ, hJ, hi, -, -, h, hc, hf⟩ :=
    mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
      (by rintro (⟨f, h⟩ | h) <;> cases h)
  have hpc : pc = d.site.pc := fires_pc hf
  obtain ⟨B, hB, -, -⟩ := wait_ev (Mma.site_event hpre hg h hc hf) rfl
  have hpoll : d.site.isPoll = true := by
    obtain ⟨site, _⟩ := d
    cases site <;> simp_all [Mma.pollBar, Mma.Site.isPoll]
  have hrdv : d.site ∈ Mma.rdvSites := by
    have := List.all_eq_true.mp Mma.rdv_facts.1 d.site (Mma.mem_allSites _)
    rw [← hpc] at this
    simpa [hpoll, hu] using this
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hS := (RunInv.holds hpre hX hg (shflJ_run hpre hg) hk hσ).2.1
  refine ⟨d, hσ, hJ, hi, hrdv, hpc, hS, ?_⟩
  unfold pollRound
  rw [hpc]
  exact hJ.pollsAt d.site hpoll

/-- A shuffle event of a thread with `n` earlier shuffles. -/
theorem shflK_of {g j : Nat} {e : Event} (he : X.get (g, j) = some e)
    (hp : Execution.isShfl e = true) (hc : ((X.tr g).take j).countP Execution.isShfl = n) :
    X.ShflK (g, j) n := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp [Execution.isShfl] at hp
  exact ⟨⟨_, _, _, _, _, _, _, he⟩, hc⟩

/-- **The `before` clause of `Cross.PollColl`, for warp 12.** -/
theorem Cross.PollColl_mma_before (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc m p ok acq sc r}, g < L.threads → warpOf L g = 12 →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      rdvPos (pc + 1) = true →
      r < pollRound pc ((X.tr g).take k) → ∃ b, b < k ∧ CollAt X g b (Mma.collOf L pc r) := by
  intro g k pc m p ok acq sc r _ hw he hu hr
  obtain ⟨d, -, hJ, hi, hrdv, hpc, hS, hR⟩ := rdv_poll hpre hX ht hw he hu
  rw [hR] at hr
  have hlt := Mma.cnt_round_lt hi hrdv hr
  rw [hpc, Mma.collOf_eq hrdv r]
  obtain ⟨j, e, hj, hej, hp, hcnt⟩ := exists_nthEv (X := X) (p := Execution.isShfl) (g := g)
    (k := k) (n := 4 + Mma.cnt L Mma.shA 6 2
      ⟨d.site, (Mma.roundIT L d.site r).1, (Mma.roundIT L d.site r).2, b32 0, fun _ => b32 0⟩)
    (by omega)
  exact ⟨j, hj, shflK_of hej hp hcnt⟩

/-- **The `after` clause of `Cross.PollColl`, for warp 12.** -/
theorem Cross.PollColl_mma_after (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g h k k' pc m m' p p' ok ok' acq acq' sc sc'}, g < L.threads → h < L.threads →
      g ≠ h → SameWarp L g h → warpOf L g = 12 →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ →
      rdvPos (pc + 1) = true →
      pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') →
      ∃ a, k < a ∧ CollAt X g a (Mma.collOf L pc (pollRound pc ((X.tr g).take k))) := by
  intro g h k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh _ hs hw he he' hu hlt
  have hw' : warpOf L h = 12 := by rw [← hw]; exact hs.2.symm
  obtain ⟨d, -, hJ, hi, hrdv, hpc, hS, hR⟩ := rdv_poll hpre hX ht hw he hu
  obtain ⟨b, -, hK⟩ := Cross.PollColl_mma_before hpre hX ht hh hw' he' hu hlt
  rw [hR, hpc, Mma.collOf_eq hrdv, Mma.roundIT_at hi hrdv] at hK ⊢
  have hn : Mma.cnt L Mma.shA 6 2 ⟨d.site, d.i, d.t, b32 0, fun _ => b32 0⟩ =
      Mma.cnt L Mma.shA 6 2 d := rfl
  rw [hn] at hK ⊢
  obtain ⟨⟨pcb, mb, ab, bb, cb, rb, ob, hgb⟩, hcb⟩ := hK
  rcases Step.shfl_lane_of_ready hX hgb ⟨⟨_, _, _, _, _, _, _, hgb⟩, hcb⟩
      (sameWarp_symm hs) with
      ⟨j, hKj⟩ | ⟨x, pcx, hex, hcx⟩
  · obtain ⟨⟨pcj, mj, aj, bj, cj, rj, oj, hgj⟩, -⟩ := id hKj
    refine ⟨j, ?_, hKj⟩
    by_contra hjk
    have hjk' : j < k := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hjk) with h1 | h1
      · exact h1
      · subst h1
        rw [he] at hgj
        cases hgj
    have h1 := PTX.Flow.countP_take_succ (p := Execution.isShfl) hgj rfl
    have h2 := PTX.Flow.countP_take_mono Execution.isShfl (X.tr g) (show j + 1 ≤ k by omega)
    have h3 := hKj.2
    simp only at h3
    omega
  · exfalso
    obtain ⟨dx, t, ins, o, hσx, hJx, -, -, -, -, hcx', hfx⟩ :=
      mma_state hpre hX ht hex hw (by simp [Prologue.ProKind]) (fun f h => by cases h)
    have hsx := Mma.exit_site hcx' hfx rfl
    have hkx : x < (X.tr g).length := (List.getElem?_eq_some_iff.mp hex).1
    have hSx := (RunInv.holds hpre hX hg (shflJ_run hpre hg) hkx hσx).2.1
    have hitem := hi.i (by
      obtain ⟨site, _⟩ := d
      simp [Mma.rdvSites] at hrdv
      rcases hrdv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial)
    have hdone := hJx.done (by rw [hsx]; rfl) hitem.2
    have hii := item_lt hitem.1 hdone
    obtain ⟨-, -, -, -, -, hreg, h14, -⟩ := Mma.rdv_site hrdv
    have hl := List.all_eq_true.mp Mma.rdv_loop d.site hrdv
    have htr := hi.trip
    unfold Mma.TripOk at htr
    have hpos := Nat.mul_le_mul_left (6 * Mma.trips L + 2) (show d.i + 1 ≤ dx.i by omega)
    rw [Nat.mul_add, Nat.mul_one] at hpos
    have hn1 := mma_trips_pos hpre
    simp only [shflCnt, Mma.shfls, Mma.cnt] at hSx
    simp only [Mma.cnt] at hcx
    rw [hsx] at hSx
    simp only [Mma.shA, Mma.Site.phase, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
      Mma.Site.ord] at hSx
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
    rcases hl with ⟨h1, hl⟩ | ⟨h23, hl⟩
    · rw [h1] at htr hreg
      simp only at htr
      rw [hl, htr] at hcx
      simp at hcx hreg
      omega
    · rw [hl] at hcx
      rcases h23 with h2 | h3
      · rw [h2] at htr
        simp only at htr
        have : d.t * 1 * 6 ≤ 6 * Mma.trips L := by omega
        omega
      · rw [h3] at htr hreg
        simp at htr hreg
        omega

/-! ### The other polls -/

/-- Among the MMA poll sites, those after which the branch is a poll branch (a guarded `bra.uni`
on the poll's predicate) outside `rdvSites` are the hand-off wait's: the inner
P-ready polls (`p2Wait`) are followed by a plain `@p bra`. -/
theorem Mma.rest_facts : Mma.allSites.all (fun s => !(s.isPoll &&
    !rdvPos (s.pc + 1) && kernel.pollBranch (s.pc + 1)) ||
    decide (s = .waitDealloc)) = true := by
  decide +kernel

/-- **`Cross.PollRest`, MMA part**: a lane of the MMA warp polling at a position followed by a
poll branch that is not a rendezvous position polls at the hand-off wait, once per thread, so it
is in round 0 and the premise that asks for an order fails. -/
theorem Cross.PollRest_mma (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g h k k' pc p' : Nat} {m' : Loc} {ok' acq' : Bool}
    {sc' : MbarScope} (hw : warpOf L g = 12) (hs : SameWarp L g h)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩)
    (hb : kernel.pollBranch (pc + 1) = true)
    (hu : rdvPos (pc + 1) = false) :
    ¬ pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') := by
  have hw' : warpOf L h = 12 := by rw [← hw]; exact hs.2.symm
  obtain ⟨d, hJ, -, hpc, hpoll, -⟩ := mma_poll hpre hX ht hw' he'
  have hd : d.site = .waitDealloc := by
    have := List.all_eq_true.mp Mma.rest_facts d.site (Mma.mem_allSites _)
    rw [← hpc] at this
    simpa [hpoll, hu, hb] using this
  have h0 : pollRound pc ((X.tr h).take k') = 0 := by
    unfold pollRound
    rw [hpc, hJ.pollsAt d.site hpoll]
    simp [Mma.pollCnt, Mma.deallocA, hd]
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
