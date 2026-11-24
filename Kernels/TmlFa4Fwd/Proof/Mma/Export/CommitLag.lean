-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.At
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Kernels.TmlFa4Fwd.Proof.Mma.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # An MMA lane short of a commit is early

`mma_commit_early`: the committing lane of warp 12 with at most `v` commits to a barrier, fewer than
the tile's, is before the time `B`, when every place at which the closed form is at most `v` is
before `B`. `s_commit_early` is that for S-full, `o_commit_early` for O. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (commitAt)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem mma_exit_site {d : Mma.D} {pc : Nat} (hev : Mma.Ev p L g d ⟨pc, .exit⟩) :
    ∃ l, d.site = .exit l := by
  obtain ⟨s, v⟩ := d
  cases s <;> simp only [Mma.Ev] at hev
  case exit l => exact ⟨l, rfl⟩
  all_goals exfalso
  all_goals (try simp only [Epilogue.Ev, Mma.Site.toE] at hev)
  all_goals shape_destruct hev
  all_goals cases ‹Kind.exit = _›

theorem pipeT_succ_lt {q r v : Nat} (h : q < 86) (hs : (if q < 20 then 0 else r + 1) ≤ v) :
    Progress.Mm.pipeT p q r + 1 < Progress.clk p v 512 := by
  have := Nat.mul_le_mul_left Progress.span hs
  unfold Progress.Mm.pipeT
  simp only [Progress.clk]
  omega

private theorem commit_s (st : Fin 2) (q r : Nat) : commitAt q r (80 + 8 * st.val) =
    if st = 0 then Mma.pq 8 q r + Mma.pq 34 q r else Mma.pq 14 q r + Mma.pq 47 q r := by
  fin_cases st <;> simp [commitAt]

/-- The tile's commits to an S-full barrier. -/
theorem commitAt_s (st : Fin 2) (R : Nat) : commitAt 100 R (80 + 8 * st.val) = R + 1 := by
  rw [commit_s]
  fin_cases st <;> simp [Mma.pq] <;> omega

/-- The tile's commit to an O barrier. -/
theorem commitAt_o (st : Fin 2) (R : Nat) : commitAt 100 R (144 + 8 * st.val) = 1 := by
  fin_cases st <;> simp [commitAt, Mma.pq]

/-- The releases of a K/V slot. -/
theorem commitAt_kv (q r : Nat) {s : Nat} (hs : s < 3) :
    commitAt q r (56 + 8 * s) = Mma.ringCount (Mma.ringRel q r) s := by
  interval_cases s <;> simp [commitAt]

/-- A release of a K/V slot the tile makes. -/
theorem commitAt_kv_total {R i : Nat} (h3 : 3 ≤ i) (hi : i < 2 * R + 5) :
    i / 3 ≤ commitAt 100 R (56 + 8 * (i % 3)) := by
  rw [commitAt_kv _ _ (Nat.mod_lt i (by decide))]
  have : Mma.ringRel 100 R = 2 * R + 2 := by simp [Mma.ringRel, Mma.pq]; omega
  rw [this]
  unfold Mma.ringCount
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12)
  (hwin : ∀ j pc mk inst ld, X.get (g, j) = some ⟨pc, .elect mk inst ld⟩ → ld = laneOf L g)
  {R : Nat} (hR : MmaRounds p L g R)
include hp hX hFw hub hg hw hwin hR

/-- A lane short of its commits is early. -/
theorem mma_commit_early {o v B : Nat} (hB : Progress.primeBase p + 1024 ≤ B)
    (hend : v < commitAt 100 R o)
    (hq : ∀ q r, q < 86 → (q < 20 → r = 0) → (20 ≤ q ∧ q < 60 → r < R) → (60 ≤ q → r = R) →
      commitAt q r o ≤ v → Progress.Mm.pipeT p q r + 1 < B)
    (ha : (X.tr g).countP (commitsTo (obj L g o)) ≤ v) :
    Sched.threadTime (Progress.timed p L) X g < B := by
  have key : ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ + 1 < B := by
    intro k σ hσ
    obtain ⟨q, r, hc, ht⟩ := mma_at hp hX hFw hub hg hw hwin hR hσ
    have hle : commitAt q r o ≤ v := by
      rw [← hc]; exact le_trans (List.take_sublist _ _).countP_le ha
    rcases ht with ⟨-, -, h⟩ | ⟨h1, h2, h3, h4, h⟩ | ⟨rfl, rfl⟩
    · omega
    · rw [h]; exact hq q r h1 h2 h3 h4 hle
    · omega
  have h0 : 0 < B := by omega
  unfold Sched.threadTime
  split
  · rename_i d hd; exact Nat.lt_of_succ_lt (key _ d hd)
  · exact h0
  · split
    · rename_i d hd; exact key _ d hd
    · exact h0

/-- A lane that exited made all its commits. -/
theorem mma_exit_commits {k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) (o : Nat) :
    commitAt 100 R o ≤ (X.tr g).countP (commitsTo (obj L g o)) := by
  have hbm := mma_rounds_bmax hp hg hR
  rcases mma_counts hp hX hFw hw he (fun f h => by cases h) with ⟨s, n, -, hev, hx⟩ | hev |
    ⟨d, n, r, w, hσ, hQ, hcm, hF, hev⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  obtain ⟨l, hs⟩ := mma_exit_site hev
  obtain ⟨q, r', hc, ht⟩ := mma_at hp hX hFw hub hg hw hwin hR hσ
  have htime : Progress.time p L g (Mma.minj p L g d n) = Progress.endT p l 8 := by
    simp only [Progress.time, Progress.roleTime, Progress.Mm.time, hs, Mma.Site.pipe,
      Bool.false_eq_true, ite_false, Progress.Mm.endOff]
  cases l with
  | false =>
    obtain ⟨R', bal, hP, -⟩ := hR
    have hearly : d.site.early = false := by rw [hs]; rfl
    exact (noPicked_of_exit (Mma.mfits_main hearly hF).2.1
      (by show d.site.epi = _; rw [hs]; rfl) ⟨R', bal, hP⟩).elim
  | true =>
    have hle := (List.take_sublist k (X.tr g)).countP_le (p := commitsTo (obj L g o))
    rw [htime] at ht
    have hd := Progress.drain_order p (s := Progress.bmax p + 1) (o := 0) le_rfl (by decide)
    have hpr := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    simp only [Progress.endT, ite_true] at ht
    rcases ht with ⟨-, -, h⟩ | ⟨h1, h2, h3, h4, h⟩ | ⟨rfl, rfl⟩
    · omega
    · exfalso
      have hs' : (if q < 20 then 0 else r' + 1) ≤ Progress.bmax p + 1 := by
        split
        · omega
        · have : r' ≤ R := by
            rcases Nat.lt_or_ge q 60 with h6 | h6
            · exact (h3 ⟨by omega, h6⟩).le
            · exact (h4 h6).le
          omega
      have := Progress.drain_order p hs' (o := 2 * q) (by unfold Progress.span; omega)
      unfold Progress.Mm.pipeT at h
      omega
    · rw [← hc]; exact hle

/-- **S full**: a lane with at most `v ≤ R` commits to the barrier of stage `st` is before the polls
of softmax round `v`. -/
theorem s_commit_early (st : Fin 2) {v : Nat} (hv : v ≤ R)
    (ha : (X.tr g).countP (commitsTo (obj L g (80 + 8 * st.val))) ≤ v) :
    Sched.threadTime (Progress.timed p L) X g < Progress.clk p v 512 := by
  have hend := commitAt_s st R
  refine mma_commit_early hp hX hFw hub hg hw hwin hR ?_ (by omega) ?_ ha
  · exact Progress.primeBase_le_clk p _ _
  · intro q r h1 h2 h3 h4 hc
    have hs : (if q < 20 then 0 else r + 1) ≤ v := by
      split
      · omega
      · revert hc
        rw [commit_s]
        fin_cases st <;> simp only [Mma.pq] <;> norm_num <;> split_ifs <;> omega
    exact pipeT_succ_lt h1 hs

/-- **O**: a lane with no commit to the O barrier of stage `st` is before the polls of the final
stage. -/
theorem o_commit_early (st : Fin 2)
    (ha : (X.tr g).countP (commitsTo (obj L g (144 + 8 * st.val))) ≤ 0) :
    Sched.threadTime (Progress.timed p L) X g < Progress.clk p (R + 1) 512 := by
  have hend : commitAt 100 R (144 + 8 * st.val) = 1 := commitAt_o st R
  refine mma_commit_early hp hX hFw hub hg hw hwin hR ?_ (by omega) ?_ ha
  · exact Progress.primeBase_le_clk p _ _
  · intro q r h1 h2 h3 h4 hc
    refine pipeT_succ_lt h1 ?_
    split
    · omega
    · have : r ≤ R := by
        rcases Nat.lt_or_ge q 60 with h6 | h6
        · exact (h3 ⟨by omega, h6⟩).le
        · exact (h4 h6).le
      omega

/-- **K/V empty**: a lane with fewer releases of slot `i % 3` than the packets up to `i - 3` in it
is before band M's end of slot `(i - 2) / 2`. -/
theorem kv_commit_early {i : Nat} (h3 : 3 ≤ i) (hi : i < 2 * R + 5)
    (ha : (X.tr g).countP (commitsTo (obj L g (56 + 8 * (i % 3)))) + 1 ≤ i / 3) :
    Sched.threadTime (Progress.timed p L) X g < Progress.clk p (min ((i - 2) / 2) (R + 1)) 512 := by
  refine mma_commit_early hp hX hFw hub hg hw hwin hR (o := 56 + 8 * (i % 3))
    (v := i / 3 - 1) ?_ ?_ ?_ (by omega)
  · exact Progress.primeBase_le_clk p _ _
  · rw [commitAt_kv _ _ (Nat.mod_lt i (by decide))]
    have : Mma.ringRel 100 R = 2 * R + 2 := by simp [Mma.ringRel, Mma.pq]; omega
    rw [this]
    unfold Mma.ringCount
    omega
  · intro q r h1 h2 h4 h5 hc
    rw [commitAt_kv _ _ (Nat.mod_lt i (by decide))] at hc
    refine pipeT_succ_lt h1 ?_
    split
    · omega
    · rename_i h20
      have hrel : 2 * r + 1 ≤ Mma.ringRel q r := by
        simp only [Mma.ringRel, Mma.pq]
        split_ifs <;> omega
      have hrR : r ≤ R := by
        rcases Nat.lt_or_ge q 60 with h6 | h6
        · exact (h4 ⟨by omega, h6⟩).le
        · exact (h5 h6).le
      unfold Mma.ringCount at hc
      omega

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
