-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderPoll
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaElect
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaPollColl

@[expose] public section

/-! # The loader's collectives at its rendezvous polls

The rendezvous positions of the loader warp are its six item polls (`Loader.rdv_wait`). The round
of a poll of use `u` gives the item and the trip (`Counts.rounds`, `roundOf_wait`), and the
lane's next collective after the poll's success is the election of the use (`elA` on the leader
CTA, `elC` otherwise), with as many elections before it as at the poll: `i E + preElects u t`
(`Counts.elects`), a function of the CTA, the position and the round (`Loader.collAt`).

* Before a poll of a later round the lane has made that election (`before`), its elections at the
  poll being more.
* When another lane of the warp polls the position in a later round, that lane made the election,
  so this lane took part in its instance (`ElectOk`), with the same ordinal (`ElectOrdinal`),
  after its poll, since it had not yet made it there (`after`).

Only the MMA warp and the loader poll at the rendezvous positions (`rdv_warp`), so their
collective functions together give `Cross.PollColl`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Loader
open Work

/-- One on the leader CTA `c` of a pair. -/
def r0c (c : Nat) : Nat := if c % 2 = 0 then 1 else 0

/-- The elections of round `r` of use `u`'s poll in CTA `c`: the item's and trip's of the round. -/
def roundElects (L : Launch) (c : Nat) (u : UseK) (r : Nat) : Nat :=
  let E := 4 * r0c c + 7 + (n L - 1) * (2 * r0c c + 3)
  if u.trip then
    r / (n L - 1) * E + preElectsC c u (r % (n L - 1))
  else r * E + preElectsC c u 0
where
  preElectsC (c : Nat) (u : UseK) (t : Nat) : Nat :=
    match u with
    | .k0 => 0
    | .q0 => r0c c + 2
    | .q1 => 2 * r0c c + 4
    | .v0 => 3 * r0c c + 6
    | .k => 4 * r0c c + 7 + t * (2 * r0c c + 3)
    | .v => 4 * r0c c + 7 + t * (2 * r0c c + 3) + (r0c c + 2)

/-- The loader's item poll sites. -/
def waitSites : List UseK := [.k0, .q0, .q1, .v0, .k, .v]

/-- The collective of round `r` at position `pc` of the loader in CTA `c`. -/
def collAt (L : Launch) (c pc r : Nat) : Bool × Nat :=
  match waitSites.find? (fun u => decide ((Site.wait u).pc = pc)) with
  | some u => (true, roundElects L c u r)
  | none => (true, 0)

/-- The rendezvous positions are the item polls'; each names its use. -/
theorem rdv_facts :
    waitSites.all (fun u => waitSites.find? (fun u' => decide ((Site.wait u').pc =
      (Site.wait u).pc)) = some u) = true ∧
    (List.finRange 6).all (fun k =>
      !rdvPos ((Site.drain k).pc + 1)) = true ∧
    !rdvPos (Site.drainQ.pc + 1) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem mem_waitSites (u : UseK) : u ∈ waitSites := by cases u <;> simp [waitSites]

/-- The elections of a poll's own round are the elections at its state. -/
theorem roundElects_at {g : Nat} {d : D} {u : UseK} (hi : Inv L g d) (hs : d.site = .wait u) :
    roundElects L (ctaOf L g) u (roundOf L g d u) = electOf L g d := by
  rw [roundOf_wait hs]
  have hr : r0c (ctaOf L g) = r0 L g := rfl
  cases htr : u.trip
  · simp only [roundElects, htr, Bool.false_eq_true, ↓reduceIte, electOf, hs, hr, itemElects]
    cases u <;> simp_all [UseK.trip, roundElects.preElectsC, preElects]
  · have ht := hi.trip (by rw [hs]; cases u <;> simp_all [UseK.trip, Site.inTrip])
    simp only [roundElects, htr, ↓reduceIte, electOf, hs, hr, itemElects]
    have hpos : 0 < n L - 1 := by omega
    rw [Nat.mul_comm d.i, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega), Nat.add_zero,
      Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega), Nat.mul_comm (n L - 1)]
    cases u <;> simp_all [UseK.trip, roundElects.preElectsC, preElects]

/-- The elections of an earlier round are fewer than at the poll. -/
theorem roundElects_lt {g : Nat} {d : D} {u : UseK} (hi : Inv L g d) (hs : d.site = .wait u)
    {r : Nat} (hr : r < roundOf L g d u) :
    roundElects L (ctaOf L g) u r < electOf L g d := by
  rw [roundOf_wait hs] at hr
  have hr0 : r0c (ctaOf L g) = r0 L g := rfl
  have hr01 : r0 L g ≤ 1 := by unfold r0; split_ifs <;> omega
  cases htr : u.trip
  · simp only [htr, Bool.false_eq_true, ↓reduceIte] at hr
    simp only [roundElects, htr, Bool.false_eq_true, ↓reduceIte, electOf, hs, hr0, itemElects]
    have hle := Nat.mul_le_mul_right (4 * r0 L g + 7 + (n L - 1) * (2 * r0 L g + 3))
      (show r + 1 ≤ d.i by omega)
    rw [Nat.add_mul, Nat.one_mul] at hle
    cases u <;> simp_all [UseK.trip, roundElects.preElectsC, preElects]
  · simp only [htr, ↓reduceIte] at hr
    have ht := hi.trip (by rw [hs]; cases u <;> simp_all [UseK.trip, Site.inTrip])
    simp only [roundElects, htr, ↓reduceIte, electOf, hs, hr0, itemElects]
    have hpos : 0 < n L - 1 := by omega
    have hq := Nat.div_add_mod r (n L - 1)
    have hρ := Nat.mod_lt r hpos
    generalize r / (n L - 1) = q at hq ⊢
    generalize r % (n L - 1) = ρ at hq hρ ⊢
    generalize hE : 4 * r0 L g + 7 + (n L - 1) * (2 * r0 L g + 3) = E
    rcases Nat.lt_trichotomy q d.i with hlt | heq | hgt
    · have hle := Nat.mul_le_mul_right E (show q + 1 ≤ d.i by omega)
      rw [Nat.add_mul, Nat.one_mul] at hle
      have hm := Nat.mul_le_mul_right (2 * r0 L g + 3) (show ρ + 1 ≤ n L - 1 by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      cases u <;> simp_all [UseK.trip, roundElects.preElectsC, preElects] <;> omega
    · subst heq
      have hlt : ρ < d.t := by
        have := Nat.mul_comm d.i (n L - 1)
        omega
      have hm := Nat.mul_le_mul_right (2 * r0 L g + 3) (show ρ + 1 ≤ d.t by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      cases u <;> simp_all [UseK.trip, roundElects.preElectsC, preElects]
    · exfalso
      have := Nat.mul_le_mul_right (n L - 1) (show d.i + 1 ≤ q by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      have := Nat.mul_comm (n L - 1) q
      omega

end Loader

theorem isElectE_eq_ev (x : Event) : Loader.isElectE x = isElectEv x := by
  obtain ⟨_, k⟩ := x
  cases k <;> rfl

/-- **A poll of the loader at a rendezvous position** is an item poll's, with the thread's
elections and its round at the position. -/
theorem loader_rdv_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hw : warpOf L g = 14) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (hu : rdvPos (pc + 1) = true) :
    ∃ (d : Loader.D) (u : Loader.UseK), Loader.Inv L g d ∧ d.site = .wait u ∧
      pc = (Loader.Site.wait u).pc ∧
      elections X g k = Loader.electOf L g d ∧
      pollRound pc ((X.tr g).take k) = Loader.roundOf L g d u := by
  obtain ⟨d, t, ins, o, -, hJ, -, hi, hc, hf⟩ :=
    Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
  have hpc : pc = d.site.pc := Loader.fires_pc hf
  have hwp := OpPcsFast.mem Loader.kernel_wait_pcs hc (Loader.waitOp_of hf rfl)
  rcases Loader.site_wait d.site hwp with ⟨u, hs⟩ | ⟨kk, hs⟩ | hs
  · refine ⟨d, u, hi, hs, hs ▸ hpc, ?_, ?_⟩
    · unfold elections
      rw [← hJ.elects]
      exact (List.countP_congr fun x _ => by rw [isElectE_eq_ev]).symm
    · rw [hpc, hs]
      exact hJ.rounds u
  · exfalso
    have := List.all_eq_true.mp Loader.rdv_facts.2.1 kk (List.mem_finRange kk)
    rw [hpc, hs] at hu
    simp [hu] at this
  · exfalso
    have := Loader.rdv_facts.2.2
    rw [hpc, hs] at hu
    simp [hu] at this

/-- The collective of a loader poll's round, at its position. -/
theorem Loader.collAt_wait (u : Loader.UseK) (c r : Nat) :
    Loader.collAt L c (Loader.Site.wait u).pc r = (true, Loader.roundElects L c u r) := by
  have h := List.all_eq_true.mp Loader.rdv_facts.1 u (Loader.mem_waitSites u)
  simp only [decide_eq_true_eq] at h
  simp only [Loader.collAt, h]

/-- **The `before` clause of `Cross.PollColl`, for warp 14.** -/
theorem Cross.PollColl_loader_before (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc m p ok acq sc r}, g < L.threads → warpOf L g = 14 →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      rdvPos (pc + 1) = true →
      r < pollRound pc ((X.tr g).take k) →
      ∃ b, b < k ∧ CollAt X g b (Loader.collAt L (ctaOf L g) pc r) := by
  intro g k pc m p ok acq sc r _ hw he hu hr
  obtain ⟨d, u, hi, hs, hpc, hE, hR⟩ := loader_rdv_poll hpre hX ht hw he hu
  rw [hR] at hr
  have hlt := Loader.roundElects_lt hi hs hr
  rw [hpc, Loader.collAt_wait]
  obtain ⟨j, e, hj, hej, hp, hcnt⟩ := exists_nthEv (X := X) (p := isElectEv) (g := g)
    (k := k) (n := Loader.roundElects L (ctaOf L g) u r)
    (by unfold elections at hE; omega)
  obtain ⟨epc, ek⟩ := e
  cases ek <;> simp [isElectEv] at hp
  rename_i mask inst l
  obtain rfl := elect_full hX (e := (g, j)) hej
  exact ⟨j, hj, ⟨epc, inst, l, hej⟩, hcnt⟩

/-- **The `after` clause of `Cross.PollColl`, for warp 14.** -/
theorem Cross.PollColl_loader_after (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g h k k' pc m m' p p' ok ok' acq acq' sc sc'}, g < L.threads → h < L.threads →
      g ≠ h → SameWarp L g h → warpOf L g = 14 →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ →
      rdvPos (pc + 1) = true →
      pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') →
      ∃ a, k < a ∧ CollAt X g a
        (Loader.collAt L (ctaOf L g) pc (pollRound pc ((X.tr g).take k))) := by
  intro g h k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh _ hs hw he he' hu hlt
  have hw' : warpOf L h = 14 := by rw [← hw]; exact hs.2.symm
  have hcta : ctaOf L h = ctaOf L g := hs.1.2.2.symm
  obtain ⟨d, u, hi, hsd, hpc, hE, hR⟩ := loader_rdv_poll hpre hX ht hw he hu
  obtain ⟨b, -, hK⟩ := Cross.PollColl_loader_before hpre hX ht hh hw' he' hu hlt
  rw [hcta, hR, hpc, Loader.collAt_wait, Loader.roundElects_at hi hsd] at hK
  obtain ⟨⟨pcb, inst, l, hb⟩, hbn⟩ := hK
  rw [hR, hpc, Loader.collAt_wait, Loader.roundElects_at hi hsd]
  obtain ⟨j, hj⟩ := elect_participant hX (sameWarp_symm hs) hb (electMember_lane (L := L) g)
  have ho := electOrdinal hX (ElectMutual.of_full fun he => elect_full hX he)
    (sameWarp_symm hs) hb hj
  simp only at ho hbn
  unfold elections at hbn hE
  refine ⟨j, ?_, ⟨pcb, inst, l, hj⟩, by unfold elections; omega⟩
  by_contra hjk
  have hjk' : j < k := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hjk) with h1 | h1
    · exact h1
    · subst h1
      have h1 : X.get (g, j) = some ⟨pcb, .elect 4294967295 inst l⟩ := hj
      rw [he] at h1
      cases h1
  have h1 := PTX.Flow.countP_take_succ (p := isElectEv) (X := X) hj rfl
  have h2 := PTX.Flow.countP_take_mono isElectEv (X.tr g) (show j + 1 ≤ k by omega)
  omega

theorem Idle.site_not_rdv (s : Idle.Site) :
    rdvPos (s.pc + 1) = false := by
  cases s <;> site_decide

theorem Store.site_not_rdv (s : Store.Site) :
    rdvPos (s.pc + 1) = false := by
  cases s <;> site_decide

theorem Softmax.site_not_rdv (s : Softmax.Site) :
    rdvPos (s.pc + 1) = false := by
  cases s <;> site_decide

theorem Correction.site_not_rdv (s : Correction.Site) :
    rdvPos (s.pc + 1) = false := by
  cases s <;> site_decide

/-- **Only the MMA warp and the loader poll at the rendezvous positions.** -/
theorem rdv_warp (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (hu : rdvPos (pc + 1) = true) :
    warpOf L g = 12 ∨ warpOf L g = 14 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, -, -, -, -, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  have hpc := fires_pc hf
  simp only at hpc
  rcases d with q | r
  · exact absurd (pro_event hpre hX he hσ (fun f h => by cases h)).proKind
      (by simp [Prologue.ProKind])
  have hw := role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg)
    k r hσ
  cases r with
  | mma _ => exact .inl hw
  | loader _ => exact .inr hw
  | idle s' => rw [hpc] at hu; rw [Idle.site_not_rdv] at hu; cases hu
  | store s' => rw [hpc] at hu; rw [Store.site_not_rdv] at hu; cases hu
  | softmax s' => rw [hpc] at hu; rw [Softmax.site_not_rdv] at hu; cases hu
  | corr s' => rw [hpc] at hu; rw [Correction.site_not_rdv] at hu; cases hu

/-- The collective function of the MMA warp and the loader. -/
def rdvColl (L : Launch) (key : Nat × Nat) (pc r : Nat) : Bool × Nat :=
  if key.2 = 12 then Mma.collOf L pc r else Loader.collAt L key.1 pc r

/-- **`Cross.PollColl`** (the restated premise of `Thread/FactsWarp.lean`). -/
theorem Cross.pollColl (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) : Cross.PollColl L X := by
  refine ⟨rdvColl L, fun {g h k k' pc m m' p p' ok ok' acq acq' sc sc'} hg hh hgh hs he he'
    hu hlt => ?_, fun {g k pc m p ok acq sc r} hg he hu hr => ?_⟩
  · rcases rdv_warp hpre hX ht he hu with hw | hw
    · simp only [rdvColl, warpKey, hw, ↓reduceIte]
      exact Cross.PollColl_mma_after hpre hX ht hg hh hgh hs hw he he' hu hlt
    · simp only [rdvColl, warpKey, hw, show (14 : Nat) ≠ 12 from by decide, ↓reduceIte]
      exact Cross.PollColl_loader_after hpre hX ht hg hh hgh hs hw he he' hu hlt
  · rcases rdv_warp hpre hX ht he hu with hw | hw
    · simp only [rdvColl, warpKey, hw, ↓reduceIte]
      exact Cross.PollColl_mma_before hpre hX ht hg hw he hu hr
    · simp only [rdvColl, warpKey, hw, show (14 : Nat) ≠ 12 from by decide, ↓reduceIte]
      exact Cross.PollColl_loader_before hpre hX ht hg hw he hu hr

end
end PTX.Kernels.FlashAttn4Fwd.Proof
