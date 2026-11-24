-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.WarpWaits

@[expose] public section

/-! # The warp collective class: the step

When every lane of `g`'s warp is at `g`'s collective site, the warp performs one instance of it
(`warp_batch`); otherwise a lane stopped before the site or is at an earlier site, a pending
obligation of smaller rank. So a released pending thread at a collective site steps
(`warp_next_steps`), and so does every released pending thread whose next event is a
warp-synchronous collective (`warp_steps`, the class `NextSteps L mem0 .warp` of the assembly). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow Classical

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A state whose next event is a warp-synchronous collective is at a collective site. -/
theorem coll_of_warp {d : ThreadD} (h : nextKind d = .warp) : ∃ s, d.coll = some s := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind, ThreadD.coll]

section
variable (hpre : Pre P L mem0) (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X)
  (hub : ¬ HasUb X)
include hpre ht hX hub

omit ht hub in
/-- An election site's batch: every lane performs the full-mask election at the site. -/
theorem elect_batch {g : Nat} (hg : g < L.threads) {s : CollSite}
    (hfe : ∀ h inst leader, s.Fires L h ⟨s.pc, .elect fullMask inst leader⟩)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Step.Launched L X h)
    (hrels : ∀ h, SameWarp L g h → Step.Released L X h)
    (hready : ∀ h, SameWarp L g h → ∃ t t1, Run kernel Prod L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau kernel Prod L h) t t1 ∧
      ∀ e, s.Fires L h e → ∃ u, EStep kernel Prod L h t1 e (some u)) :
    ∃ Y, Consistent L kernel Prod mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨leader, hlm, hdet⟩ := Step.exists_leader (g := g) hX (member_full (laneOf_lt L g))
  refine Step.elect_counted_extension hX (pc := s.pc) hg (fun lane hl => Step.warp_full hb hg hl.1)
    (fun h _ => member_full (laneOf_lt L h)) hlm hdet hst hrels ?_ (fun _ => prod_wf _)
  intro h hw inst
  obtain ⟨t, t1, hr, hl, hf⟩ := hready h hw
  obtain ⟨u, hu⟩ := hf _ (hfe h inst leader)
  exact ⟨t, t1, _, hr, hl, hu⟩

/-- **Every lane at the site: the warp performs the collective**, a counted extension. -/
theorem warp_batch {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    {s : CollSite} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hs : d.coll = some s)
    (hrel : Step.Released L X g)
    (hall : ∀ h, SameWarp L g h → ∃ dh, Frame.stateAt (code L) X h (X.tr h).length =
      some (some dh) ∧
      dh.coll = some s) :
    ∃ Y, Consistent L kernel Prod mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hg := hp.1
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hready : ∀ h, SameWarp L g h → ∃ t t1, Run kernel Prod L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau kernel Prod L h) t t1 ∧
      ∀ e, s.Fires L h e → ∃ u, EStep kernel Prod L h t1 e (some u) := fun h hw => by
    obtain ⟨dh, hσh, hsh⟩ := hall h hw
    exact lane_ready ht hX hub hg hp hσ hs hw hσh hsh
  have hrels : ∀ h, SameWarp L g h → Step.Released L X h := fun h hw =>
    lane_released hpre ht hX hub hg hσ hs hrel hall hw
  by_cases hsh : s = .shfl
  · subst hsh
    have g0 : X.tr g = [] := ht.coll_before hg (noUb_of hub g) hσ hs
    have hlanes0 : ∀ h, SameWarp L g h → X.tr h = [] := fun h hw => by
      obtain ⟨dh, hσh, hsh⟩ := hall h hw
      exact ht.coll_before hw.1.2.1 (noUb_of hub h) hσh hsh
    -- the warp's shuffle from any execution with the same traces whose cluster is launched
    have hbatch : ∀ X', Consistent L kernel Prod mem0 X' → X'.tr = X.tr →
        (∀ h, SameWarp L g h → Step.Launched L X' h) →
        ∃ Y, Consistent L kernel Prod mem0 Y ∧ X'.le Y ∧ X'.size L < Y.size L := by
      intro X' hX' htr hl
      refine Step.shfl_counted_extension hX' hb (pc := CollSite.shfl.pc) (m := .idx)
        (fun h => Proof.b32 (h % L.block / 32)) (fun _ => 0) (fun _ => 31) hg
          (fun h hw => .inr (hl h hw))
        (fun h hw => released_nil (by rw [htr]; exact hlanes0 h hw)) ?_ (fun _ _ => prod_wf _)
      intro h hw recv ok
      obtain ⟨t, t1, hr, hl', hf⟩ := hready h hw
      obtain ⟨u, hu⟩ := hf _ ⟨recv, ok, rfl⟩
      exact ⟨t, t1, _, by rw [htr]; exact hr, hl', hu⟩
    have hcl : ∀ h, SameWarp L g h →
        L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) := fun h hw => by
      rw [hw.1.2.2]
    cases hown : X.clcState.owner (L.clusterOfCta (g / L.block)) with
    | none =>
      have hv : Clc.ValidTask L (L.clusterOfCta (g / L.block)) := by
        rw [clc_valid_task_iff hpre.oneDimLaunch hpre.grid hpre.cluster]
        have h1 : g / L.block < 1024 := by
          have := hp.1
          unfold Launch.threads at this
          rw [hpre.grid, hpre.block] at this
          rw [hpre.block]
          omega
        simp only [clusterOfCta_eq hpre]
        omega
      obtain ⟨Y, hY, hle, hlt⟩ := hbatch _ (consistent_launchClc hX hv hown (prod_wf _)) rfl
        (fun h hw _ => by simp [Execution.launchClc, hcl h hw])
      exact ⟨Y, hY, Execution.le_trans (launchClc_le hown) hle, by rwa [launchClc_size] at hlt⟩
    | some o =>
      cases o with
      | launched => exact hbatch X hX rfl (fun h hw _ => by rw [hcl h hw]; exact hown)
      | canceled r => exact (hp.2.1 ⟨g0, r, hown⟩).elim
  · have hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Step.Launched L X h := fun h hw => by
      obtain ⟨dh, hσh, hsh'⟩ := hall h hw
      exact .inl (coll_ne_nil ht hub hw.1.2.1 hσh hsh' hsh)
    cases s with
    | shfl => exact absurd rfl hsh
    | warpBar =>
      refine Step.warpBar_counted_extension hX (fun _ => CollSite.warpBar.pc) hg
        (fun lane hl => Step.warp_full hb hg hl.1) (fun h _ =>
          member_full (laneOf_lt L h)) hst hrels
        ?_ (fun _ => prod_wf _)
      intro h hw inst
      obtain ⟨t, t1, hr, hl, hf⟩ := hready h hw
      obtain ⟨u, hu⟩ := hf _ ⟨inst, rfl⟩
      exact ⟨t, t1, _, hr, hl, hu⟩
    | elect => exact elect_batch (s := .elect) hpre hX hg
                        (fun _ i l => ⟨i, l, rfl⟩) hst hrels hready
    | roleElect => exact elect_batch (s := .roleElect) hpre hX hg
                        (fun _ i l => ⟨i, l, rfl⟩) hst hrels hready
    | mmaElect => exact elect_batch (s := .mmaElect) hpre hX hg
                        (fun _ i l => ⟨i, l, rfl⟩) hst hrels hready
    | schedElect => exact elect_batch (s := .schedElect) hpre hX hg
                        (fun _ i l => ⟨i, l, rfl⟩) hst hrels hready

end

/-- **Progress at a warp-synchronous collective.** A pending thread at a collective site, whose last
event is released, steps: a lane of its warp before the site is an obligation of smaller rank, or
the whole warp performs the collective. -/
theorem warp_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length =
      some (some d))
    {s : CollSite} (hs : d.coll = some s) (hrel : Step.Released L X g) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  by_cases hlow : ∃ h, SameWarp L g h ∧
      ¬ ∃ dh, Frame.stateAt (code L) X h (X.tr h).length = some (some dh) ∧ dh.coll = some s
  · obtain ⟨h, hw, hn⟩ := hlow
    rcases ht.coll_lane hg hσ hs hw (noUb_of hub h) with ⟨j, e, he, hm⟩ | hstop |
      ⟨d', hσh, hat | hbe⟩
    · exact (coll_matched ht hX hg hσ hs hw he hm (Frame.run_some hX hub hp)).elim
    · obtain ⟨ho, hr⟩ := lane_lower ht hX hub hg hσ hs hrel hw (.inl hstop)
      exact .inr ⟨X, .thread h, hmax, ho, hr⟩
    · exact (hn ⟨d', hσh, hat⟩).elim
    · obtain ⟨ho, hr⟩ := lane_lower ht hX hub hg hσ hs hrel hw (.inr ⟨d', hσh, hbe⟩)
      exact .inr ⟨X, .thread h, hmax, ho, hr⟩
  · push Not at hlow
    exact .inl (warp_batch hpre ht hX hub hp hσ hs hrel hlow)

/-- **The warp collective class** (`NextSteps L mem0 .warp` of the assembly): a released pending
thread whose next event is a warp-synchronous collective steps. -/
theorem warp_steps (hpre : Pre P L mem0)
    (hfacts : ∀ Y, Consistent L kernel Prod mem0 Y → ThreadFacts L Y)
    (hsafe : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ Unsafe L kernel Prod mem0 Y) :
    ∀ (X : Execution) (g : Nat) (d : ThreadD), Maximal L kernel Prod mem0 X →
      Frame.Pending L X g → Frame.stateAt (code L) X g (X.tr g).length = some (some d) →
      nextKind d = .warp → Step.Released L X g → Descent.Steps L kernel Prod mem0 (Descent.Obl L)
        (rank L) X (.thread g) := by
  intro X g d hmax hp hσ hk hrel
  obtain ⟨s, hs⟩ := coll_of_warp hk
  exact warp_next_steps hpre (hfacts X hmax.1) (noUb_of_safe (hsafe X hmax.1)) hmax hp hσ hs hrel

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
