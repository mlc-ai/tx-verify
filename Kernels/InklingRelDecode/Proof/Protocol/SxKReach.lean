-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpCount

@[expose] public section

/-!
# The MMA lane reaches every QK and PV step before a later state

The analogue of `Lp.reach_rank` for the MMA warp:

* `rank`: a number of each MMA state, `29 i + pos site`, with the QK half at positions 0 to 13
  (`qk j` at `5 + j`), the PV half at 14 to 28 (`pv j` at `19 + j`), the loop's end and the
  sites before the loop at 0 to 4;
* `rank_step`: a step of a thread that led its elections raises the rank by at most one, except
  at the two steps that skip a half: after the QK half of iteration 0 (no PV half) and into the
  PV half of the last iteration `num_iters` (no QK half), `Jump`;
* `reach_rank`: backward from a state of rank at least `R`, a state of rank exactly `R`, for a
  target `R` that no jump skips: a PV position of an iteration `≥ 1`, or a QK position of an
  iteration below `num_iters`;
* `reach_qk`, `reach_pv`: the states at QK step `j` of iteration `b` and PV step `j` of
  iteration `b + 1` before a state after them.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Cover
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The place of a site in an iteration of the loop. -/
def pos : Mma.Site → Nat
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar => 0 | .kvWait => 1 | .qkShfl => 2 | .qkBar2 => 3 | .qkElect => 4
  | .qk j => 5 + j | .qkCommit => 13 | .qkSkip => 13
  | .pvBar => 14 | .pWait => 15 | .pvShfl => 16 | .pvBar2 => 17 | .pvElect => 18
  | .pv j => 19 + j | .pvCommit1 => 27 | .pvCommit2 => 28 | .pvSkip => 28
  | .finBar => 0 | .finElect => 1 | .finCommit => 2 | .bar1 => 3 | .setMaxRegInc => 4

/-- The rank of an MMA state. -/
def rank (d : Mma.D) : Nat := 29 * d.i + pos d.site

theorem pos_le (s : Mma.Site) : pos s ≤ 28 := by
  cases s <;> simp only [pos] <;> omega

theorem site_qk {s : Mma.Site} {j : Fin 8} (h : pos s = 5 + j) : s = .qk j := by
  cases s <;> simp only [pos] at h <;> first | omega | (congr 1; exact Fin.ext (by omega))

theorem site_pv {s : Mma.Site} {j : Fin 8} (h : pos s = 19 + j) : s = .pv j := by
  cases s <;> simp only [pos] at h <;> first | omega | (congr 1; exact Fin.ext (by omega))

/-- The steps that raise the rank by more than one: out of the QK half of iteration 0 or out of
the PV half, into the next iteration's start, its end, or its PV half when it has no QK half. -/
def Jump (d0 d : Mma.D) : Prop :=
  d.i = d0.i + 1 ∧ (pos d0.site = 28 ∨ (pos d0.site = 13 ∧ d0.i = 0)) ∧
    (pos d.site = 0 ∨ (pos d.site = 14 ∧ ¬ d.i < d.n))

/-- **One step of a thread that leads its elections raises the rank by at most one**, except at a
`Jump`; `num_iters` is kept except at its load. -/
theorem rank_step {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g)
    (hk : d.site.isSkip = false) :
    rank d0 ≤ rank d ∧ (rank d ≤ rank d0 + 1 ∨ Jump d0 d) ∧ (d.n = d0.n ∨ d.site = .bar0) := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       simp_all [rank, pos, Jump, Mma.Site.isSkip]; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       simp_all [rank, pos, Jump, Mma.Site.isSkip]; omega)

/-- **Backward to a state of a given rank.** For a thread that leads its elections and a target
`R` that is a PV position of an iteration `≥ 1` or a QK position of an iteration below
`num_iters`: an MMA state of rank at least `R` has, at an earlier or the same event, an MMA state
of rank exactly `R`. -/
theorem reach_rank (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hlead : ElectLead L g (X.tr g)) (hbc : Mma.BcastRun (X.tr g)) {R N : Nat}
    (hR : (29 ≤ R ∧ 19 ≤ R % 29) ∨ (5 ≤ R % 29 ∧ R % 29 ≤ 12 ∧ R / 29 < N)) :
    ∀ k {d : Mma.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.mma d P))) → R ≤ rank d → d.n = N →
      ∃ k' d', k' ≤ k ∧ St Q L X g k' = some (some (.w (.mma d' P))) ∧ rank d' = R := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ hr hN
    by_cases heq : rank d = R
    · exact ⟨k, d, le_refl _, hσ, heq⟩
    have hI := mma_inv_at hX hf hk hσ
    have hnp : ¬ Mma.PreSite d.site := by
      intro h
      have h0 := hI.pre h
      have hp : pos d.site = 0 := by
        revert h
        cases d.site <;> simp [Mma.PreSite, pos]
      unfold rank at hr
      omega
    have hs0 : d.site ≠ .setMaxReg := fun h => hnp (by rw [h]; trivial)
    obtain ⟨k0, e, d0, hadj, -, he, hσ0, hn⟩ := mma_state_pred_adj hX hk hσ hs0
    have hmem : e ∈ X.tr g := List.mem_of_getElem? (show (X.tr g)[k0]? = some e from he)
    have hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g :=
      fun mask inst ld h => hlead e hmem mask inst ld h
    obtain ⟨h1, h2, h3⟩ := rank_step hn hl (not_skip hX hbc hσ)
    have hN0 : d0.n = N := by
      rcases h3 with h3 | h3
      · omega
      · exact absurd (by rw [h3]; trivial) hnp
    by_cases hr0 : R ≤ rank d0
    · obtain ⟨k', d', hk', hσ', h4⟩ := ih k0 (by omega) (by omega) hσ0 hr0 hN0
      exact ⟨k', d', by omega, hσ', h4⟩
    · exfalso
      rcases h2 with h2 | ⟨hi, hp0, hp⟩
      · omega
      · have hl0 := pos_le d0.site
        have hl1 := pos_le d.site
        unfold rank at hr hr0 heq
        rcases hp with hp | ⟨hp, hlt⟩ <;> rcases hp0 with hp0 | ⟨hp0, hi0⟩ <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Cover
