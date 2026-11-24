-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QGroup
public import Lemmas.Flow.Polls
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepTma
import Lemmas.Protocol.RecordCountPair
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A lane of warp 14 past the first TMA groups made a Q group's events

`q_done`: a lane of warp 14 that loses no election and is past the first four TMA groups has
arrived on each Q stage's full barrier and issued two copies that complete on it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem q_done (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14) (hub : ¬ HasUb X) {k : Nat} {b : Bool}
    {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (h0 : n .ub = 0) (hpast : 1000 ≤ ppos (decide (n (.load .commit) = 0)) d.site)
    (hwin : ∀ j pc inst ld, X.get (g, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩ →
      ld = laneOf L g) {t : Fin 7} (ht : t.val < 4) :
    1 ≤ arrivals (bl L g (taOff t)) ((X.tr g).take k) ∧
      2 ≤ ((X.tr g).take k).countP (issuesTo (bl L g (taOff t))) := by
  have hH := group_hist hp hX hg hw hub hσ h0
  have hi : ∀ i : Fin 3, ∃ j < k, ∃ e d, X.get (g, j) = some e ∧ d.site = wonSite t i ∧
      Ev p L g 14 d e ∧
        ∃ b n, Frame.stateAt (thread p L) X g j = some (some (LdWarp.linj p L g b d n)) := by
    intro i
    have hpos : wonPos t i < ppos (decide (n (.load .commit) = 0)) d.site := by
      unfold wonPos; omega
    rcases hH t i ht hpos with h | ⟨j, -, pc, inst, ld, he, hld⟩
    · exact h
    · exact absurd (hwin j pc inst ld he) hld
  have hget : ∀ {j e}, j < k → X.get (g, j) = some e → ((X.tr g).take k)[j]? = some e :=
    fun hj he => by rw [List.getElem?_take_of_lt hj]; exact he
  have hissue : ∀ i : Fin 3, i.val ≠ 0 → ∃ j < k, (∃ e, X.get (g, j) = some e ∧
      issuesTo (bl L g (taOff t)) e = true) ∧ ∃ b d n, d.site = wonSite t i ∧
        Frame.stateAt (thread p L) X g j = some (some (LdWarp.linj p L g b d n)) := by
    intro i hi0
    obtain ⟨j, hj, ⟨pc, kind⟩, ⟨s, v, kk⟩, he, hs, hev, b', n', hst⟩ := hi i
    simp only at hs
    refine ⟨j, hj, ⟨_, he, ?_⟩, b', _, n', hs, hst⟩
    obtain ⟨c, hc⟩ : ∃ c, s = .tc t c := by
      rw [hs]; unfold wonSite
      rw [ite_eq_right hi0]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    subst hc
    simp only [Ev] at hev
    rcases hev with ⟨a, sp, hk, hb⟩ | ⟨f, hk⟩
    · subst hk
      simp [issuesTo, hb, tc_bar hp]
    · subst hk
      exact (hub ⟨(g, j), pc, f, he⟩).elim
  constructor
  · obtain ⟨j, hj, ⟨pc, kind⟩, ⟨s, v, kk⟩, he, hs, hev, -⟩ := hi 0
    simp only [wonSite, Fin.val_zero, ↓reduceIte] at hs
    subst hs
    simp only [Ev] at hev
    subst hev
    refine List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? (hget hj he), ?_⟩
    simp [arrivesOn, sourceArrive, ta_loc hp t]
  · obtain ⟨j1, hj1, ⟨e1, he1, hp1⟩, b1, d1, n1, hs1, hst1⟩ := hissue 1 (by simp)
    obtain ⟨j2, hj2, ⟨e2, he2, hp2⟩, b2, d2, n2, hs2, hst2⟩ := hissue 2 (by simp)
    have hne : j1 ≠ j2 := by
      rintro rfl
      rw [hst1] at hst2
      simp only [Option.some.injEq, LdWarp.linj, Prod.mk.injEq, Sum.inr.injEq] at hst2
      obtain ⟨h1, -⟩ := hst2
      cases h1
      rw [hs1] at hs2
      simp [wonSite] at hs2
    rw [MBarrier.countP_eq_card]
    have hsub : ({j1, j2} : Finset Nat) ⊆
        MBarrier.indicesP (issuesTo (bl L g (taOff t))) ((X.tr g).take k) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [MBarrier.mem_indicesP_iff]
      rcases hx with rfl | rfl
      · exact ⟨e1, hget hj1 he1, hp1⟩
      · exact ⟨e2, hget hj2 he2, hp2⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
