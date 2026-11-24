-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemLife
public import Kernels.FlashAttn4Fwd.Proof.Interface

@[expose] public section

/-! # The lanes of the MMA warp agree on their polls of one round

A poll of warp 12 at a position is a poll site's (two sites share a position only as the inner
P-ready poll of the elected lane and of the others, which poll one barrier with one parity:
`pollKey`). Its round, the thread's successful polls at that position before it, is the item `i`
for a site before or after the trip loop and `(n - 1) i + t` for a site in it (`Counts.pollsAt`,
`round_at`), which with the trip facts of `Inv` gives the item and the trip. The barrier and the
parity of the poll are functions of the site, the item and the trip, so two lanes polling at one
position in one round poll one barrier with one parity (`Cross.PollAgree_mma`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A poll site up to the lane's election at the inner P-ready poll. -/
def Mma.Site.pollKey : Mma.Site → Mma.Site
  | .p2Wait k _ => .p2Wait k false
  | s => s

/-- Poll sites at one position have one key. -/
theorem Mma.pollKey_pc : Mma.allSites.all (fun s => Mma.allSites.all fun s' =>
    !(s.isPoll && s'.isPoll && decide (s.pc = s'.pc)) || decide (s.pollKey = s'.pollKey)) =
    true := by
  decide +kernel

theorem Mma.pollKey_eq {s s' : Mma.Site} (hs : s.isPoll = true) (hs' : s'.isPoll = true)
    (hpc : s.pc = s'.pc) : s.pollKey = s'.pollKey := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp Mma.pollKey_pc s (Mma.mem_allSites s)) s'
    (Mma.mem_allSites s')
  simpa [hs, hs', hpc] using h

/-- The round of a poll at its own site. -/
theorem Mma.round_at {g : Nat} {d : Mma.D} (hi : Mma.Inv L g d) (hs : d.site.isPoll = true) :
    (d.site = .waitDealloc ∧ Mma.pollCnt L d.site d = 0) ∨
    (Mma.region d.site = 2 ∧ Mma.pollCnt L d.site d = (Mma.trips L - 1) * d.i + d.t ∧
      d.t + 1 < Mma.trips L) ∨
    (Mma.region d.site = 1 ∧ Mma.pollCnt L d.site d = d.i ∧ d.t = 0) ∨
    (Mma.region d.site = 3 ∧ Mma.pollCnt L d.site d = d.i ∧ d.t + 1 = Mma.trips L) := by
  have htr := hi.trip
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp [Mma.Site.isPoll] at hs
  case waitDealloc => simp [Mma.pollCnt, Mma.deallocA]
  case p2Wait k ld =>
    fin_cases k <;> simp [Mma.TripOk, Mma.region] at htr <;>
      simp [Mma.pollCnt, Mma.region, Mma.cntL, Mma.cnt, Mma.Site.after, Mma.Site.inTrip,
        Mma.Site.loop, Mma.Site.ord, Mma.p2Ord, htr]
  all_goals
    rename_i k
    fin_cases k <;> simp [Mma.TripOk, Mma.region] at htr <;>
      simp [Mma.pollCnt, Mma.region, Mma.cntL, Mma.cnt, Mma.Site.after, Mma.Site.inTrip,
        Mma.Site.loop, Mma.Site.ord, Mma.qOrd, Mma.kvOrd, Mma.pOrd, htr]

/-- The barrier and the parity of a poll site, its part of the item and whether it is the
hand-off wait, are those of its key. -/
theorem Mma.poll_key1 (s : Mma.Site) (i t : Nat) (b b' : Value) (pr pr' : Nat → Value) :
    Mma.pollBar L ⟨s, i, t, b, pr⟩ = Mma.pollBar L ⟨s.pollKey, i, t, b', pr'⟩ ∧
      Mma.pollPar L ⟨s, i, t, b, pr⟩ = Mma.pollPar L ⟨s.pollKey, i, t, b', pr'⟩ ∧
      Mma.region s = Mma.region s.pollKey ∧ (s = .waitDealloc ↔ s.pollKey = .waitDealloc) := by
  cases s
  case p2Wait k ld => fin_cases k <;> exact ⟨rfl, rfl, rfl, by simp [Mma.Site.pollKey]⟩
  all_goals exact ⟨rfl, rfl, rfl, Iff.rfl⟩

theorem Mma.poll_key (s s' : Mma.Site) (i t : Nat) (b b' : Value) (pr pr' : Nat → Value)
    (hk : s.pollKey = s'.pollKey) :
    Mma.pollBar L ⟨s, i, t, b, pr⟩ = Mma.pollBar L ⟨s', i, t, b', pr'⟩ ∧
      Mma.pollPar L ⟨s, i, t, b, pr⟩ = Mma.pollPar L ⟨s', i, t, b', pr'⟩ ∧
      Mma.region s = Mma.region s' ∧ (s = .waitDealloc ↔ s' = .waitDealloc) := by
  obtain ⟨a1, a2, a3, a4⟩ := Mma.poll_key1 (L := L) s i t b b' pr pr'
  obtain ⟨c1, c2, c3, c4⟩ := Mma.poll_key1 (L := L) s' i t b' b' pr' pr'
  rw [hk] at a1 a2 a3 a4
  exact ⟨a1.trans c1.symm, a2.trans c2.symm, a3.trans c3.symm, a4.trans c4.symm⟩

/-- **A poll of warp 12** is a poll site's, at its position, of its barrier and parity. -/
theorem mma_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hw : warpOf L g = 12) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ d : Mma.D, Mma.Counts L g d ((X.tr g).take k) ∧ Mma.Inv L g d ∧ pc = d.site.pc ∧
      d.site.isPoll = true ∧ ∃ B, Mma.pollBar L d = some B ∧ m = Mma.bar L g B ∧
        p = Mma.pollPar L d := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, u, -, hJ, hi, -, -, h, hc, hf⟩ :=
    mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
      (by rintro (⟨f, h⟩ | h) <;> cases h)
  obtain ⟨B, hB, hm, hp⟩ := wait_ev (Mma.site_event hpre hg h hc hf) rfl
  refine ⟨d, hJ, hi, fires_pc hf, ?_, B, hB, hm, hp⟩
  obtain ⟨site, _⟩ := d
  cases site <;> simp_all [Mma.pollBar, Mma.Site.isPoll]

/-- Division with remainder below the divisor is unique. -/
theorem divmod_unique {a q q' r r' : Nat} (h : a * q + r = a * q' + r') (hr : r < a)
    (hr' : r' < a) : q = q' ∧ r = r' := by
  have h1 : (r + a * q) / a = q := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  have h2 : (r' + a * q') / a = q' := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr', Nat.zero_add]
  have hq : q = q' := by rw [← h1, ← h2, Nat.add_comm r, Nat.add_comm r', h]
  subst hq
  exact ⟨rfl, by omega⟩

/-- **`Cross.PollAgree`, for warp 12.** -/
theorem Cross.PollAgree_mma (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g h k k' pc p p' : Nat} {m m' : Loc} {ok ok' acq acq' : Bool} {sc sc' : MbarScope}
      {d d' : ThreadD}, SameWarp L g h → warpOf L g = 12 → St L X g k = some (some d) →
      St L X h k' = some (some d') → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ →
      pollRound pc ((X.tr g).take k) = pollRound pc ((X.tr h).take k') →
      m = m' ∧ p % 2 = p' % 2 := by
  intro g h k k' pc p p' m m' ok ok' acq acq' sc sc' _ _ hs hw _ _ he he' hr
  have hw' : warpOf L h = 12 := by rw [← hw]; exact hs.2.symm
  obtain ⟨e, hJ, hi, hpc, hpoll, B, hB, hm, hp⟩ := mma_poll hpre hX ht hw he
  obtain ⟨e', hJ', hi', hpc', hpoll', B', hB', hm', hp'⟩ := mma_poll hpre hX ht hw' he'
  have hkey := Mma.pollKey_eq hpoll hpoll' (hpc.symm.trans hpc')
  have h1 := hJ.pollsAt e.site hpoll
  have h2 := hJ'.pollsAt e'.site hpoll'
  have h2' : ((X.tr h).take k').countP (okPollAt e.site.pc) = Mma.pollCnt L e'.site e' := by
    rw [← hpc, hpc']
    exact h2
  unfold pollRound at hr
  rw [hpc, h1, h2'] at hr
  have hcta : g / L.block = h / L.block := hs.1.2.2
  have key : e.i = e'.i ∧ e.t = e'.t ∨ e.site = .waitDealloc := by
    obtain ⟨site, i, t, base, pro⟩ := e
    obtain ⟨site', i', t', base', pro'⟩ := e'
    simp only at hkey hr ⊢
    obtain ⟨-, -, hreg, hwd⟩ := Mma.poll_key (L := L) site site' i t base base' pro pro' hkey
    have R := Mma.round_at hi hpoll
    have R' := Mma.round_at hi' hpoll'
    simp only at R R'
    rcases R with ⟨hd, -⟩ | ⟨h2r, hc, htt⟩ | ⟨h1r, hc, htt⟩ | ⟨h3r, hc, htt⟩
    · exact .inr hd
    all_goals rcases R' with ⟨hd', -⟩ | ⟨h2r', hc', htt'⟩ | ⟨h1r', hc', htt'⟩ |
      ⟨h3r', hc', htt'⟩
    all_goals first
      | omega
      | (exfalso
         have := hwd.mpr hd'
         subst this
         simp [Mma.region] at *)
      | (left
         rw [hc, hc'] at hr
         exact divmod_unique hr (by omega) (by omega))
  have hcta : g / L.block = h / L.block := hs.1.2.2
  obtain ⟨site, i, t, base, pro⟩ := e
  obtain ⟨site', i', t', base', pro'⟩ := e'
  simp only at hkey key hB hB' hp hp' hm hm' ⊢
  rcases key with ⟨rfl, rfl⟩ | hd
  · obtain ⟨h1, h2, -⟩ := Mma.poll_key (L := L) site site' i t base base' pro pro' hkey
    rw [h1, hB'] at hB
    obtain rfl := Option.some.inj hB
    refine ⟨by rw [hm, hm']; simp [Mma.bar, hcta], by rw [hp, hp', h2]⟩
  · obtain ⟨-, -, -, hwd⟩ := Mma.poll_key (L := L) site site' i t base base' pro pro' hkey
    have hd' := hwd.mp hd
    subst hd hd'
    simp only [Mma.pollBar, Option.some.injEq] at hB hB'
    subst hB hB'
    exact ⟨by rw [hm, hm']; simp [Mma.bar, hcta], by rw [hp, hp']; rfl⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
