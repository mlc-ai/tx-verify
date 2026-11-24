-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.WarpWaitsLane
public import Kernels.Fp16Gemm8192.Proof.Progress.AllocPublish
public import Kernels.Fp16Gemm8192.Proof.Support.Scheduling
public import Lemmas.Clc.ClcCompleteConsistentLaunch

@[expose] public section

/-! # Progress at the warp-synchronous collectives

The class of the shuffle, the elections and the warp barrier (`ThreadD.coll`). A pending thread
`g` at such a site, with its last event released, steps (`warp_next_steps`):

* a lane of its warp that stopped before the site, or is at an earlier site, is a pending obligation
  of smaller rank (`lane_lower`); no lane is past the site (`coll_matched`);
* otherwise every lane of the warp is at the site, released (`lane_released`), and the warp performs
  one instance of the collective (`Step.shfl_counted_extension`, `Step.elect_counted_extension`,
  `Step.warpBar_counted_extension`): a counted extension. Before the shuffle, every lane's first
  event, the warp's cluster is launched first if no cancellation has decided it
  (`consistent_launchClc`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow Classical

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every lane of warp 0 is a lane of a paired Tensor Memory operation of its CTA pair. -/
theorem lane_enc (x : Nat) :
    Tmem.Pair.pairLane L 0 (x / L.block - x / L.block % 2) (x / L.block % 2) (x % L.block) =
      x := by
  simp only [Tmem.Pair.pairLane, Nat.zero_mul, Nat.add_zero]
  have h1 : x / L.block - x / L.block % 2 + x / L.block % 2 = x / L.block := by
    have := Nat.mod_le (x / L.block) 2
    omega
  rw [h1]
  exact Nat.div_add_mod' x L.block

section
variable (hpre : Pre P L mem0) (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X)
  (hub : ¬ HasUb X)
include hpre ht hX hub

omit hpre in
/-- A lane at the site of a pending thread is pending and can perform the site's events. -/
theorem lane_ready {g h : Nat} (hg : g < L.threads) (hp : Frame.Pending L X g) {d : ThreadD}
    {s : CollSite} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
      (hs : d.coll = some s)
    (hw : SameWarp L g h) {dh : ThreadD}
    (hσh : Frame.stateAt (code L) X h (X.tr h).length = some (some dh)) (hsh : dh.coll = some s) :
    ∃ t t1, Run kernel Prod L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau kernel Prod L h) t t1 ∧
      ∀ e, s.Fires L h e → ∃ u, EStep kernel Prod L h t1 e (some u) := by
  have hh := hw.1.2.1
  have hnx : ∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩ := by
    intro pc hl
    rw [ht.exited_state hh hl] at hσh
    cases hσh
  have hcl : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) := by rw [hw.1.2.2]
  have hnc : ¬ ClcCanceled L X h := by
    by_cases hsh0 : s = .shfl
    · subst hsh0
      have h0 : X.tr h = [] := ht.coll_before hh (noUb_of hub h) hσh hsh
      have g0 : X.tr g = [] := ht.coll_before hg (noUb_of hub g) hσ hs
      rintro ⟨-, r, hr⟩
      exact hp.2.1 ⟨g0, r, by rw [← hcl]; exact hr⟩
    · exact not_canceled_of_peer hX hg (coll_ne_nil ht hub hg hσ hs hsh0) hcl
  obtain ⟨t, hr⟩ := Frame.run_some hX hub ⟨hh, hnc, hnx⟩
  obtain ⟨t1, hl, hf⟩ := ht.coll_fire hh hσh hsh hr
  exact ⟨t, t1, hr, hl, hf⟩

/-- **A lane at the site is released.** -/
theorem lane_released {g h : Nat} (hg : g < L.threads) {d : ThreadD}
    {s : CollSite} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hs : d.coll = some s)
    (hrel : Step.Released L X g)
    (hall : ∀ h, SameWarp L g h → ∃ dh, Frame.stateAt (code L) X h (X.tr h).length =
      some (some dh) ∧
      dh.coll = some s)
    (hw : SameWarp L g h) : Step.Released L X h := by
  have hh := hw.1.2.1
  obtain ⟨dh, hσh, hsh⟩ := hall h hw
  have hbh := ht.coll_before hh (noUb_of hub h) hσh hsh
  have hbg := ht.coll_before hg (noUb_of hub g) hσ hs
  -- the register request of a role election, with its whole warp
  have hreg : (s ≠ .shfl ∧ s ≠ .elect ∧ s ≠ .warpBar) → Step.Released L X h := by
    rintro ⟨h1, h2, h3⟩
    have hb : ∀ x (hx : x < L.threads) (dx : ThreadD),
        Frame.stateAt (code L) X x (X.tr x).length = some (some dx) → dx.coll = some s →
        0 < (X.tr x).length ∧ ∃ pc inc n inst,
          X.get (x, (X.tr x).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ := by
      intro x hx dx hσx hsx
      have := ht.coll_before hx (noUb_of hub x) hσx hsx
      cases s <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 |
        exact this
    obtain ⟨hpg, pcg, incg, ng, ig, hqg⟩ := hb g hg d hσ hs
    obtain ⟨hph, pch, inch, nh, ih, hqh⟩ := hb h hh dh hσh hsh
    have hgr := hrel.ready pcg _ hqg rfl
    obtain ⟨hrg, hog, -⟩ := ht.reg_event hg hqg
    obtain ⟨hrh, hoh, -⟩ := ht.reg_event hh hqh
    rw [hw.2] at hrg
    have heq : (pcg, incg, ng) = (pch, inch, nh) := hrg.trans hrh.symm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hsame : SetMaxNReg.SameRequest L X (g, (X.tr g).length - 1) (h, (X.tr h).length - 1) :=
      ⟨hw, by simp only [SetMaxNReg.ordinal]; exact hog.trans hoh.symm, pcg, incg, ng, ig, ih, hqg,
        hqh⟩
    have hgh := SetMaxNReg.ready_of_sameRequest hqg hsame hgr
    refine ⟨fun pc k hq _ => ?_⟩
    rw [hqh] at hq
    cases hq
    exact hgh
  cases s with
  | shfl => exact released_nil hbh
  | elect =>
    obtain ⟨x, hx, hxs⟩ := hbh
    have hq : X.get (h, (X.tr h).length - 1) = some x := by
      change (X.tr h)[_]? = _
      rw [hx]
      rfl
    obtain ⟨pc, k⟩ := x
    cases k <;> simp only [Execution.isShfl, Bool.false_eq_true] at hxs
    exact released_of_kind hq (fun _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ h => by cases h)
  | warpBar =>
    -- `g`'s allocation is covered: it is `g`'s last event, or followed by lane 0's write
    obtain ⟨jg, pcg, grpg, dstg, actg, hqg, hopg, hlg⟩ := hbg
    have hw0 : g % L.block / 32 = 0 := (ht.tmem_event hg (noUb_of hub g) hqg).1
    have hact : ∀ {x j pc grp dst act}, x < L.threads →
        X.get (x, j) = some ⟨pc, .tc (.resource grp dst act)⟩ → tmemOps ((X.tr x).take j) = 0 →
        Tmem.Pair.MustWait X (x, j) := by
      intro x j pc grp dst act hx hq h0
      obtain ⟨-, -, -, hsh, -⟩ := ht.tmem_event hx (noUb_of hub x) hq
      rw [h0] at hsh
      obtain ⟨col, rfl⟩ := hsh
      exact ⟨pc, grp, dst, _, hq, trivial⟩
    have hcovg : Tmem.Pair.Covered L X (g, jg) := by
      rcases hlg with h1 | ⟨h2, -⟩
      · have hlj : (X.tr g).length - 1 = jg := by omega
        have hq' : X.get (g, (X.tr g).length - 1) = some ⟨pcg, .tc (.resource grpg dstg actg)⟩ :=
          by rw [hlj]; exact hqg
        have := (Tmem.Pair.ReturnReady.of_ready hq' (hrel.ready _ _ hq' rfl)).2
          (by rw [hlj]; exact hact hg hqg hopg)
        rwa [hlj] at this
      · exact hX.tmemPairBlocking.covered (hact hg hqg hopg) (by simp only; omega)
    -- every lane's allocation, covered with `g`'s, and made as one collective instance
    have hops : ∀ x, SameWarp L g x →
        ∃ jx, Tmem.Pair.TmemOp X x 0 jx ∧ Tmem.Pair.Covered L X (x, jx) ∧
        (jx + 1 = (X.tr x).length ∨ (jx + 2 = (X.tr x).length ∧
          ∃ pc' a bs, X.get (x, jx + 1) = some ⟨pc', .wr a bs⟩)) := by
      intro x hwx
      obtain ⟨dx, hσx, hsx⟩ := hall x hwx
      obtain ⟨jx, pcx, grpx, dstx, actx, hqx, hopx, hlx⟩ :=
        ht.coll_before hwx.1.2.1 (noUb_of hub x) hσx hsx
      have hx0 : x % L.block / 32 = 0 := hwx.2 ▸ hw0
      have hcta : x / L.block = g / L.block := hwx.1.2.2.symm
      refine ⟨jx, ⟨⟨_, _, _, _, hqx⟩, hopx⟩, ?_, hlx⟩
      have hm := Tmem.Pair.covered_all hX (ht.warpOps hpre)
        (key := g / L.block - g / L.block % 2)
        (s := g / L.block % 2) (ℓ := g % L.block) (s' := g / L.block % 2) (ℓ' := x % L.block)
        (n := 0) (j := jg) (j' := jx) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [lane_enc g]; exact ⟨⟨_, _, _, _, hqg⟩, hopg⟩) (by rw [lane_enc g]; exact hcovg)
        (by rw [← hcta, lane_enc x]; exact ⟨⟨_, _, _, _, hqx⟩, hopx⟩)
      rwa [← hcta, lane_enc x] at hm
    obtain ⟨jh, hoph, hcovh, hlh⟩ := hops h hw
    rcases hlh with h1 | ⟨h2, pc', a, bs, hwr⟩
    · have hlast : (X.tr h).length - 1 = jh := by omega
      obtain ⟨⟨pch, grph, dsth, acth, hqh⟩, -⟩ := id hoph
      have hq' : X.get (h, (X.tr h).length - 1) = some ⟨pch, .tc (.resource grph dsth acth)⟩ := by
        rw [hlast]; exact hqh
      refine ⟨fun pc k hq _ => ?_⟩
      rw [hq'] at hq
      cases hq
      have hret : Tmem.Pair.ReturnReady L X (h, (X.tr h).length - 1) := by
        rw [hlast]
        exact ⟨hcovh.performed hX.tmemPair, fun _ => hcovh⟩
      refine Tmem.Pair.ReturnReady.ready hX.tmemPair hq' hret ?_
      intro count hcount _
      subst acth
      -- An unpublished result leaves the leader at its store, before this barrier.
      rcases allocation_publication hpre ht hX hub hq' hret with hp | ⟨x, w, hs, _, _, hstate⟩
      · exact hp
      · have hsame : SameWarp L g x :=
          ⟨⟨hw.1.1, hs.1.2.1, hw.1.2.2.trans hs.1.2.2⟩, hw.2.trans hs.2⟩
        obtain ⟨d', hd', hcoll⟩ := hall x hsame
        rw [hstate] at hd'
        cases hd'
        cases hcoll
    · have hlast : (X.tr h).length - 1 = jh + 1 := by omega
      exact released_of_kind (by rw [hlast]; exact hwr) (fun _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h)
  | roleElect => exact hreg ⟨by simp, by simp, by simp⟩
  | mmaElect => exact hreg ⟨by simp, by simp, by simp⟩
  | schedElect => exact hreg ⟨by simp, by simp, by simp⟩

end

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
