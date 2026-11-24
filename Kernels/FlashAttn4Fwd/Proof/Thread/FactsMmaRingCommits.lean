-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsMma
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCommitCount
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaElect

@[expose] public section

/-! # The MMA lanes' commits to a ring empty barrier, against a lane's polls of its full barrier

The field `MmaRingPollFacts.commits`: a lane `y` of the waiter's warp with no more elections than
the waiter has committed to the partner empty barrier of the polled full barrier no more often
than the waiter's successful polls of it.

Suppose `y` made one more such commit. That commit (`exists_nthEv`) is at an MMA commit state
(`commit_state`) of the elected lane (`lead_of_site`), whose count of earlier commits to the
barrier is the waiter's count of successful polls. By the role's counts (`Mma.Counts`: `qEmpty`,
`kvEmpty` against `qFull`, `kvFull`), the commit releases the Q stage or the ring use the waiter
polls for (`Mma.rel_cnt`, `Mma.kv_cnt`; the ring use numbers of one slot are told apart by
their count, `slots`). The commit of a use comes after the use's poll and two more elections in
program order (`q_gap`, `kv_gap`), so `y` made more elections before the commit than the waiter
made in all (`Mma.Counts.elects`), against the premise. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

namespace Mma

/-- The item of an affine count with a remainder below the step. -/
theorem affine_inj {m a b i j : Nat} (ha : a < m) (hb : b < m) (h : m * i + a = m * j + b) :
    i = j := by
  have hm : 0 < m := by omega
  have h1 : (m * i + a) / m = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : (m * j + b) / m = j := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hb, Nat.zero_add]
  rw [← h1, ← h2, h]

/-- The commit of Q stage `k` of an item comes after the item's poll of the stage and more
elections. -/
theorem q_gap {L : Launch} {d dx : D} {k : Fin 2} {c : Fin 12} (hs : d.site = .qWait k)
    (hx : dx.site = .commit c) (hc : cBar L dx c = .qEmpty k) (htr : TripOk L dx)
    (heq : cnt L (qeA k) 0 1 dx = cnt L (qA k) 0 1 d) :
    cnt L elA 8 4 d < cnt L elA 8 4 dx := by
  obtain ⟨site, i, t, b, p⟩ := d
  obtain ⟨sx, ix, tx, bx, px⟩ := dx
  simp only at hs hx heq htr hc ⊢
  subst hs hx
  fin_cases k <;> fin_cases c <;> simp [cBar] at hc <;> simp [TripOk, region] at htr <;>
    simp [cnt, qeA, qA, elA, Site.after, Site.inTrip, Site.loop, Site.ord, elCOrd,
      qOrd] at heq ⊢ <;>
    subst heq <;> omega

/-- The commit of a ring use comes after its poll and more elections. -/
theorem kv_gap {L : Launch} {d dx : D} {k : Fin 4} {c : Fin 12} (hs : d.site = .kvWait k)
    (hx : dx.site = .commit c) (hk : cKind c = 2) (hn : 0 < trips L) (htr : TripOk L d)
    (htrx : TripOk L dx) (heq : kvUse L dx.i (relU c dx.t) = kvUse L d.i (kvU k d.t)) :
    cnt L elA 8 4 d < cnt L elA 8 4 dx := by
  obtain ⟨site, i, t, b, p⟩ := d
  obtain ⟨sx, ix, tx, bx, px⟩ := dx
  simp only at hs hx heq htr htrx ⊢
  subst hs hx
  unfold kvUse kvBase at heq
  have hb1 : relU c tx < 2 * trips L := by
    fin_cases c <;> simp [cKind] at hk <;> simp [TripOk, region] at htrx <;> simp [relU] <;>
      omega
  have hb2 : kvU k t < 2 * trips L := by
    fin_cases k <;> simp [TripOk, region] at htr <;> simp [kvU] <;> omega
  obtain rfl := affine_inj hb1 hb2 heq
  have heq' : relU c tx = kvU k t := by omega
  fin_cases k <;> fin_cases c <;> simp [cKind] at hk <;> simp [TripOk, region] at htr htrx <;>
    simp [relU, kvU] at heq' <;>
    simp [cnt, elA, Site.after, Site.inTrip, Site.loop, Site.ord, elCOrd, kvOrd] <;> omega

/-- A KV-empty commit names the slot of the use it releases. -/
theorem cBar_rel {L : Launch} {d : D} {c : Fin 12} (hk : cKind c = 2) :
    cBar L d c = .kvEmpty (slotOf L d.i (relU c d.t)) := by
  fin_cases c <;> simp [cKind] at hk <;> simp [cBar, relU]

/-- A commit to a ring empty barrier is a KV-empty commit. -/
theorem cKind_of_kvEmpty {L : Launch} {d : D} {c : Fin 12} {s : Fin 6}
    (h : cBar L d c = .kvEmpty s) : cKind c = 2 := by
  fin_cases c <;> simp [cBar] at h <;> rfl

end Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The field `MmaRingPollFacts.commits`.** -/
theorem MmaRingPollFacts_commits (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) (hok : Cross.SitesTmplOk L) :
    ∀ {g y : Nat} {d : Mma.D} {b : FBar}, g < L.threads → SameWarp L g y →
      St L X g (X.tr g).length = some (some (.inr (.mma d))) →
      ((∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) → Mma.pollBar L d = some b →
      SelfElected L X y → (X.tr y).countP isElectEv ≤ (X.tr g).countP isElectEv →
      (X.tr y).countP (commitsTo (b.partner.loc L (ctaOf L g))) ≤
        okPolls (b.loc L (ctaOf L g)) (X.tr g) := by
  intro g y d b hg hw hσ hs hB _ hel
  obtain ⟨hJ, hi⟩ := end_good hpre hX ht hok hg hσ
  change Mma.Counts L g d (X.tr g) at hJ
  replace hi : Mma.Inv L g d := hi.1
  have hcta : y / L.block = g / L.block := hw.1.2.2.symm
  by_contra hlt
  obtain ⟨j, e, -, he, hp, hcnt⟩ := exists_nthEv (X := X) (g := y) (k := (X.tr y).length)
    (p := commitsTo (b.partner.loc L (ctaOf L g)))
    (n := okPolls (b.loc L (ctaOf L g)) (X.tr g)) (by rw [List.take_length]; omega)
  unfold commitsTo at hp
  split at hp
  case h_2 => cases hp
  rename_i sp hk
  have he' : X.get (y, j) = some ⟨e.pc, .tc (.commit sp)⟩ := by rw [he, ← hk]
  obtain ⟨-, dx, c, hJx, hix, hsx, hsp, -, -⟩ := commit_state hpre hX ht he'
  have hL := (lead_of_site hX hJx (by rw [hsx]; rfl)).take j
  have hm : sp.mbar = b.partner.loc L (ctaOf L y) := by
    rw [show ctaOf L y = ctaOf L g from hcta]
    simpa using hp
  have hb := commit_bar hsp hm
  -- the elections before the commit are at most the waiter's
  have hfe : Mma.isElectE = isElectEv := funext isElectE_eq
  have hele : Mma.cnt L Mma.elA 8 4 dx ≤ Mma.cnt L Mma.elA 8 4 d := by
    have h1 := hJx.elects
    have h2 := hJ.elects
    rw [hfe] at h1 h2
    have h3 := (List.take_sublist j (X.tr y)).countP_le (p := isElectEv)
    omega
  rcases hs with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hbq : b = .qFull k := by
      obtain ⟨site, i, tt, base, pro⟩ := d
      simp only at hk
      subst hk
      simpa [Mma.pollBar] using hB.symm
    subst hbq
    have h1 := hJx.qEmpty hL k
    have h2 := hJ.qFull k
    change ((X.tr y).take j).countP (commitsTo ((FBar.qEmpty k).loc L (ctaOf L y))) = _ at h1
    rw [show ctaOf L y = ctaOf L g from hcta] at h1
    change okPolls ((FBar.qFull k).loc L (ctaOf L g)) (X.tr g) = _ at h2
    simp only [FBar.partner] at hcnt hb
    have := Mma.q_gap hk hsx hb hix.trip (by omega)
    omega
  · set s := Mma.slotOf L d.i (Mma.kvU k d.t) with hsd
    have hbk : b = .kvFull s := by
      obtain ⟨site, i, tt, base, pro⟩ := d
      simp only at hk
      subst hk
      simpa [Mma.pollBar] using hB.symm
    subst hbk
    simp only [FBar.partner] at hcnt hb
    have hk2 := Mma.cKind_of_kvEmpty hb
    have h1 := hJx.kvEmpty hL s
    have h2 := hJ.kvFull s
    change ((X.tr y).take j).countP (commitsTo ((FBar.kvEmpty s).loc L (ctaOf L y))) = _ at h1
    rw [show ctaOf L y = ctaOf L g from hcta] at h1
    change okPolls ((FBar.kvFull s).loc L (ctaOf L g)) (X.tr g) = _ at h2
    have hrel : Mma.cnt L Mma.relA 2 0 dx = Mma.kvUse L dx.i (Mma.relU c dx.t) := by
      obtain ⟨site, i, tt, base, pro⟩ := dx
      simp only at hsx ⊢
      subst hsx
      exact Mma.rel_cnt c hk2 i tt base pro
    have hpoll : Mma.cnt L Mma.kvA 2 0 d = Mma.kvUse L d.i (Mma.kvU k d.t) := by
      obtain ⟨site, i, tt, base, pro⟩ := d
      simp only at hk ⊢
      subst hk
      exact Mma.kv_cnt k i tt base pro
    have hsx' : s = Mma.slotOf L dx.i (Mma.relU c dx.t) := by
      have := Mma.cBar_rel (L := L) (d := dx) hk2
      rw [hb] at this
      exact FBar.kvEmpty.inj this
    have hs1 : s.val = Mma.kvUse L dx.i (Mma.relU c dx.t) % 6 := by
      rw [hsx']; rfl
    have hs2 : s.val = Mma.kvUse L d.i (Mma.kvU k d.t) % 6 := by
      rw [hsd]; rfl
    rw [hrel] at h1
    rw [hpoll] at h2
    have hs6 := s.isLt
    have heq : Mma.kvUse L dx.i (Mma.relU c dx.t) = Mma.kvUse L d.i (Mma.kvU k d.t) := by
      simp only [Mma.slots] at h1 h2
      omega
    have := Mma.kv_gap hk hsx hk2 (mma_trips_pos hpre) hi.trip hix.trip heq
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
