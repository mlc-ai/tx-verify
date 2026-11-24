-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RdMmaRun

@[expose] public section

/-!
# The MMA lane's states at one site of one iteration are one state

`rank d = 64 · d.i + (the site's place in the iteration)` never decreases along a step of the MMA
machine (`next_rank`) and rises at a step out of `pv 7`. The thread's states from the entry of the
role to a later state are one run (`mma_back'`, with the one-step relation), so two states of the
lane at PV step 7 of the same iteration are at the same event (`pv7_unique`). The entry is
unique by the role byte protocol (`mma_entry_unique`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rd
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The place of a site in the iteration. -/
def siteRank : Mma.Site → Nat
  | .setMaxReg => 0 | .ldNum => 1 | .bar0 => 2
  | .qkBar => 3 | .kvWait => 4 | .qkShfl => 5 | .qkBar2 => 6 | .qkElect => 7
  | .qk j => 8 + j.val | .qkCommit => 16 | .qkSkip => 6
  | .pvBar => 17 | .pWait => 18 | .pvShfl => 19 | .pvBar2 => 20 | .pvElect => 21
  | .pv j => 22 + j.val | .pvCommit1 => 30 | .pvCommit2 => 31 | .pvSkip => 20
  | .finBar => 32 | .finElect => 33 | .finCommit => 34 | .bar1 => 35 | .setMaxRegInc => 36

theorem siteRank_lt (s : Mma.Site) : siteRank s < 64 := by
  cases s <;> simp only [siteRank] <;> omega

/-- The rank of a state. -/
def mrank (d : Mma.D) : Nat := 64 * d.i + siteRank d.site

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **The rank does not fall along a step, and rises at a step out of PV step 7.** -/
theorem next_rank {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d)) :
    mrank d0 ≤ mrank d ∧ (d0.site = .pv 7 → mrank d0 < mrank d) := by
  have hl0 := siteRank_lt d0.site
  have hl := siteRank_lt d.site
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       simp_all [mrank, siteRank]
       try omega
       done)
    | skip

/-- **A backward run to the entry with the one-step relation.** -/
theorem mma_back' (hX : Consistent L kernel asms mem0 X) :
    ∀ (k : Nat) {d : Mma.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.mma d P))) →
      ∃ (k0 : Nat) (d0 : Mma.D), k0 ≤ k ∧ St Q L X g k0 = some (some (.w (.mma d0 P))) ∧
        d0.site = .setMaxReg ∧
        ∀ j, k0 ≤ j → j < k → ∃ (e : Event) (dj dj' : Mma.D), (X.tr g)[j]? = some e ∧
          St Q L X g j = some (some (.w (.mma dj P))) ∧
          St Q L X g (j + 1) = some (some (.w (.mma dj' P))) ∧
          Mma.next L g dj e = some (some dj') := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ
    by_cases hs : d.site = .setMaxReg
    · exact ⟨k, d, le_refl _, hσ, hs, fun j h1 h2 => by omega⟩
    · obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ := mma_state_pred_adj hX hk hσ hs
      obtain ⟨k1, d1, hk1, hσ1, hs1, hch⟩ := ih k0 (by omega) (by omega) hs0
      refine ⟨k1, d1, by omega, hσ1, hs1, fun j hj1 hj2 => ?_⟩
      by_cases hjk : j = k0
      · subst hjk
        exact ⟨e, d0, d, he, hs0, by rw [hadj]; exact hσ, hn⟩
      · exact hch j hj1 (by omega)

/-- **Two states of the lane at PV step 7 of one iteration are at one event.** -/
theorem pv7_unique (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k1 k2 : Nat} {d1 d2 : Mma.D}
    {P1 P2 : Loader.Pro} (hk1 : k1 < (X.tr g).length) (hk2 : k2 < (X.tr g).length)
    (h1 : St Q L X g k1 = some (some (.w (.mma d1 P1)))) (s1 : d1.site = .pv 7)
    (h2 : St Q L X g k2 = some (some (.w (.mma d2 P2)))) (s2 : d2.site = .pv 7)
    (hi : d1.i = d2.i) : k1 = k2 := by
  have key : ∀ {k1 k2 : Nat} {d1 d2 : Mma.D} {P1 P2 : Loader.Pro},
      k1 < (X.tr g).length → k2 < (X.tr g).length → k1 < k2 →
      St Q L X g k1 = some (some (.w (.mma d1 P1))) → d1.site = .pv 7 →
      St Q L X g k2 = some (some (.w (.mma d2 P2))) → d2.site = .pv 7 → d1.i = d2.i → False := by
    intro k1 k2 d1 d2 P1 P2 hk1 hk2 hlt h1 s1 h2 s2 hi
    obtain ⟨k0, d0, hk0, h0, hs0, hch⟩ := mma_back' hX k2 hk2 h2
    obtain ⟨k0', d0', hk0', h0', hs0', -⟩ := mma_back hX hf k1 hk1 h1
    have heq := mma_entry_unique hpre hX hf hR (by omega) (by omega) h0 hs0 h0' hs0'
    have hle : k0 ≤ k1 := by omega
    -- the rank along the run from k1
    have claim : ∀ n, k1 + n ≤ k2 → ∃ dj : Mma.D, St Q L X g (k1 + n) =
        some (some (.w (.mma dj P2))) ∧ mrank d1 ≤ mrank dj ∧ (0 < n → mrank d1 < mrank dj) := by
      intro n
      induction n with
      | zero =>
        intro _
        obtain ⟨e, dj, dj', he, hs, hs', hn⟩ := hch k1 hle hlt
        have hh := Option.some.inj (Option.some.inj (hs.symm.trans h1))
        simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at hh
        obtain ⟨hd, hp⟩ := hh
        subst hd hp
        exact ⟨dj, by rw [Nat.add_zero]; exact hs, le_refl _, fun h => absurd h (by omega)⟩
      | succ n ih =>
        intro hn
        obtain ⟨dj, hdj, hr, hrs⟩ := ih (by omega)
        obtain ⟨e, dj1, dj', he, hs, hs', hnx⟩ := hch (k1 + n) (by omega) (by omega)
        have hd : dj1 = dj := by
          have := Option.some.inj (Option.some.inj (hs.symm.trans hdj))
          simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
          exact this.1
        subst hd
        obtain ⟨hmono, hstrict⟩ := next_rank hnx
        refine ⟨dj', by rw [← Nat.add_assoc]; exact hs', by omega, fun _ => ?_⟩
        rcases Nat.eq_zero_or_pos n with hz | hz
        · subst hz
          have hh := Option.some.inj (Option.some.inj
            ((by simpa using hdj : St Q L X g k1 = some (some (.w (.mma dj1 P2)))).symm.trans h1))
          simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at hh
          obtain ⟨hd, -⟩ := hh
          subst hd
          have := hstrict s1
          omega
        · have := hrs hz
          omega
    obtain ⟨dj, hdj, -, hlt2⟩ := claim (k2 - k1) (by omega)
    have hk21 : k1 + (k2 - k1) = k2 := by omega
    rw [hk21] at hdj
    have hh := Option.some.inj (Option.some.inj (hdj.symm.trans h2))
    simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at hh
    obtain ⟨hd, -⟩ := hh
    rw [hd] at hlt2
    have := hlt2 (by omega)
    have hm : mrank d1 = mrank d2 := by
      unfold mrank
      rw [hi, s1, s2]
    omega
  rcases lt_trichotomy k1 k2 with h | h | h
  · exact (key hk1 hk2 h h1 s1 h2 s2 hi).elim
  · exact h
  · exact (key hk2 hk1 h h2 s2 h1 s1 hi.symm).elim

end
end PTX.Kernels.InklingRelDecode.Proof.Rd
