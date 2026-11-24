-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedCorrSite
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTcAgree

@[expose] public section

/-! # The correction warps' warp-collective `tcgen05` schedule (`Sched.CorrTcSched`)

The schedule of a correction warp is `sch` (`Thread/FactsSchedCorrBlk.lean`) with the nonzero
ballots `vS` of one lane of the warp (`rep`, any launched lane with the warp's key). A lane's
count of nonzero ballots agrees with the representative's up to the ballots the lane has made
(`corr_vS_eq`: the lanes' `k`-th ballots are equal), so at a state of a lane the count of
warp-collective `tcgen05` events, `25 vS m + 32 i + finTc` less the rescale's events still to
come (`Counts.tcColl`, `Counts.voteN`), is the first ordinal of the state's block in the
representative's blocks plus its offset; in a rescale the vote's ballot is nonzero
(`Counts.rsNz`), so the block has its twenty-five events (`corr_count`). The site table then
places each state against the schedule (`site_ok`, `sch_at_rs`, `sch_at_fin`, `lt_sch`,
`lt_sch_next`). The prologue makes no such event and is before every slot. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time CorrTc

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A collective schedule from the site tables against the counts of the trace.** -/
theorem collSched_of_take {κ : Type} {p : Event → Bool} {key : Nat → κ} {Grp : Nat → Prop}
    {S : κ → Nat → Nat} (isP : Nat → ThreadD → Bool)
    (hev : ∀ {g k : Nat} {d : ThreadD} {e : Event}, g < L.threads → Grp g →
      St L X g k = some (some d) → X.get (g, k) = some e → p e = isP g d)
    (htime : ∀ {g k : Nat} {d : ThreadD}, g < L.threads → Grp g → k ≤ (X.tr g).length →
      St L X g k = some (some d) →
        (isP g d = true → stateTime L g d = S (key g) (((X.tr g).take k).countP p)) ∧
        (isP g d = false → stateTime L g d < S (key g) (((X.tr g).take k).countP p)))
    (hmono : ∀ c n, S c n < S c (n + 1)) : Sched.CollSched (timed L) X p key Grp S where
  atEv := by
    intro g k d e hg hG hσ he hp
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    exact (htime hg hG hk.le hσ).1 (by rw [← hev hg hG hσ he]; exact hp)
  nonEv := by
    intro g k d e hg hG hσ he hp
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    exact (htime hg hG hk.le hσ).2 (by rw [← hev hg hG hσ he]; exact hp)
  endLe := by
    intro g d hg hG hσ
    have h := htime hg hG le_rfl hσ
    rw [List.take_length] at h
    cases hP : isP g d
    · exact (h.2 hP).le
    · exact (h.1 hP).le
  mono := hmono

/-- A launched lane of the warp with key `c`, when there is one. -/
def rep (L : Launch) (c : Nat × Nat) : Nat :=
  if h : ∃ g, g < L.threads ∧ warpKey L g = c then Classical.choose h else 0

theorem rep_same {g : Nat} (hg : g < L.threads) : SameWarp L g (rep L (warpKey L g)) := by
  have h : ∃ h, h < L.threads ∧ warpKey L h = warpKey L g := ⟨g, hg, rfl⟩
  have hs := Classical.choose_spec h
  unfold rep
  rw [dite_eq_left h]
  exact sameWarp_of_key hg hs.1 hs.2.symm

/-- A lane's count of nonzero ballots is a count of the blocks (`VOk`). -/
theorem vS_ok (h : Nat) : VOk (vS X h) where
  zero := by simp [vS]
  step m := by
    simp only [vS, List.range_succ, List.countP_append]
    cases hz : voteNz X h m <;> simp [hz]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)

section
include hpre hX ht

/-- **The count at a correction state in the representative's blocks**, and the nonzero ballot
of a rescale's vote. -/
theorem corr_count {g k : Nat} {c : Correction.D} (hg : g < L.threads) (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hk : k ≤ (X.tr g).length)
    (hc : Correction.Counts L g c ((X.tr g).take k)) :
    ((X.tr g).take k).countP isTcColl =
        bS (Work.n L) (vS X (rep L (warpKey L g))) c.i (rOf L c) + oOf c ∧
      (isRs c = 1 → vS X (rep L (warpKey L g)) (nV (Work.n L) * c.i + rOf L c + 1) =
        vS X (rep L (warpKey L g)) (nV (Work.n L) * c.i + rOf L c) + 1) := by
  have hvN := hc.voteN
  have htc := hc.tcColl
  rw [countP_nz_take, ← Correction.isVote_eq_isBallot] at htc
  obtain ⟨e1, e2, e3, e4, e5⟩ := tcLack_eq c
  have hR : isRs c = 1 → 1 ≤ Correction.votePos L 0 c + Correction.votePos L 1 c := rs_votes
  have hE : ∀ M, M ≤ ((X.tr g).take k).countP Correction.isVote →
      vS X g M = vS X (rep L (warpKey L g)) M :=
    fun M hM => corr_vS_eq hpre hX ht hw hw' (rep_same hg) hM
  set M := ((X.tr g).take k).countP Correction.isVote with hMdef
  set v := vS X (rep L (warpKey L g)) with hvdef
  set A := nV (Work.n L) * c.i + rOf L c with hAdef
  have htc' : ((X.tr g).take k).countP isTcColl + Correction.tcLack c =
      25 * vS X g M + 32 * c.i + Correction.finTc c := htc
  rw [hE M le_rfl] at htc'
  have hA : A + isRs c = M := by
    rw [Corr.trips_eq] at hvN
    simp only [hAdef, rOf, nV]
    rcases (show isRs c = 0 ∨ isRs c = 1 by omega) with h | h
    · rw [h]; omega
    · have := hR h; rw [h]; omega
  have hz : isRs c = 1 → v (A + 1) = v A + 1 := by
    intro h1
    have htl : 0 < Correction.tcLack c := by omega
    obtain ⟨u, hu, vpc, vm, va, vb, hget, hb, hcnt⟩ := hc.rsNz htl
    have huk : u < k := by rw [List.length_take] at hu; omega
    rw [take_get huk] at hget
    rw [take_take_le huk.le] at hcnt
    have hn := nthEv_eq (p := Correction.isVote) hget rfl
    have hnz : voteNz X g A = true := by
      rw [show ((X.tr g).take u).countP Correction.isVote = A by omega] at hn
      unfold voteNz
      rw [← Correction.isVote_eq_isBallot, hn, hget]
      simpa [isNzVote] using hb
    rw [← hE A (by omega), ← hE (A + 1) (by omega)]
    exact vS_succ hnz
  refine ⟨?_, hz⟩
  simp only [bS, oOf, ← hAdef]
  rw [← hA] at htc'
  rcases (show isRs c = 0 ∨ isRs c = 1 by omega) with h | h
  · rw [h, Nat.add_zero] at htc'
    have := e2 h
    omega
  · rw [h, hz h] at htc'
    have := e3 h
    omega

end

include hpre hX ht hok

/-- **The correction warps' warp-collective `tcgen05` schedule.** -/
theorem corrTcSched : CorrTcSched L X := by
  refine ⟨fun c N => sch (Work.n L) (vS X (rep L c)) N,
    collSched_of_take (fun _ d => tcKind (nextKind d)) ?_ ?_ fun c N => sch_mono (vS_ok _) N⟩
  · intro g k d e hg _ hσ he
    exact (fired_kind hpre hX hok hg hσ he).2.1
  · intro g k d hg hG hk hσ
    obtain ⟨hJ, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    have hv := vS_ok (X := X) (rep L (warpKey L g))
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
        ⟨hw', -⟩ | ⟨-, -, c, rfl⟩
    · rw [prologue_tcKind p, prologue_not_tc hJ.1]
      refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
      refine lt_sch hv (i := 0) (r := 0) (o := 0) (Nat.zero_le _) (by decide)
        (by simp [bS, hv.zero]) ?_
      have h1 := Progress.Time.prologue_lt_reg p.site
      simp only [stateTime]
      exact h1.trans (by unfold tmB; split <;> exact Progress.Time.fixed_lt (by decide))
    all_goals (try omega)
    have hn : 0 < Work.n L := Mma.trips_pos hpre
    obtain ⟨hr, htc, hntc⟩ := site_ok hn (g := g) hinv
    obtain ⟨hcnt, hz⟩ := corr_count hpre hX ht hg hG.1 hG.2 hk hJ
    simp only [stateTime, nextKind]
    rw [hcnt]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨hcase, heq⟩ := htc h
      rw [heq]
      rcases hcase with ⟨hr', ho, h1⟩ | ⟨hr', ho⟩
      · exact (sch_at_rs hv hr' (hz h1) ho rfl).symm
      · rw [hr']
        exact (sch_at_fin hv ho rfl).symm
    · rcases hntc h with ⟨ho, hlt⟩ | ⟨ho, hr', hlt⟩
      · exact lt_sch hv hr ho le_rfl hlt
      · exact lt_sch_next hv (by rw [hr', ho]) hlt

/-- **`Cross.TcSched`** of every warp. -/
theorem tcSched_all : TcSched L X := tcSched hpre hX ht hok (corrTcSched hpre hX ht hok)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
