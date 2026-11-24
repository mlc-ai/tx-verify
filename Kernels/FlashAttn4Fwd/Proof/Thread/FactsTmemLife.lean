-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemAlloc

@[expose] public section

/-! # The lifetime of the Tensor Memory allocation, from the MMA warp's run invariant

The MMA warp's barrier-2 events, hand-off and base word:

* an event of warp 12 on barrier 2 is one of its two `bar.sync 2, 416` (`Mma.bar2_site`), after
  its allocation (`Counts.tmem`); a deallocation, an MMA and the hand-off arrival come after the
  `bar.sync` of the ordinals 1, 0 and 1 (`Counts.bar2`, `bar2_nth`);
* the only arrival of warp 12 is the hand-off, once, on the peer's handshake barrier, a release
  widened to cluster scope (`Counts.handoff`, the assumption `clusterMbar` at `1121`); its only
  poll of a handshake barrier is of its own, parity 0, an acquire widened to cluster scope
  (`1122`), and the deallocation follows a successful one (`Counts.dealloc`);
* the only write of warp 12 is lane 0's address store, the event after its allocation; its reads
  of the base word follow its first `bar.sync 2` (`Counts.allocWrite`, `Counts.wrote`).

Only the MMA warp issues MMAs (`kernel_issue_pcs`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The hand-off and the handshake polls of warp 12 -/

theorem asms_cluster_1121 : asms.any (·.clusterScopeMbar 1121) = true := by decide +kernel
theorem asms_cluster_1122 : asms.any (·.clusterScopeMbar 1122) = true := by decide +kernel

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **An arrival of warp 12** is its hand-off: once, on the peer's handshake barrier, one arrival
without bytes, a release at cluster scope, at the site after its second `bar.sync 2`. -/
theorem mma_arrive {g k pc tx c : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (hw : warpOf L g = 12) (he : X.get (g, k) = some ⟨pc, .arrive m tx c rel sc⟩) :
    ∃ d : Mma.D, Mma.Counts L g d ((X.tr g).take k) ∧ d.site = .arrivePeer ∧
      m = FBar.loc L (Mma.peer L g) .dealloc ∧ tx = 0 ∧ c = 1 ∧ rel = true ∧ sc = .cluster := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, u, -, hJ, -, hpc, -, h, hc, hf⟩ :=
    mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
      (by rintro (⟨f, h⟩ | h) <;> cases h)
  have hev := Mma.site_event hpre hg h hc hf
  obtain ⟨hs, rfl, rfl, rfl⟩ := arrive_ev hev rfl
  obtain ⟨b, off, tx', c', cl, sc0, st, hop, hfl⟩ := fires_arrive_flags hf rfl
  rw [hs] at hc hpc
  code_at hc
  subst hc
  simp only [Op.mbarArrive.injEq] at hop
  obtain ⟨-, -, -, -, -, rfl, rfl, -⟩ := hop
  exact ⟨d, hJ, hs, rfl, rfl, rfl, rfl, hfl (by rw [hpc]; exact asms_cluster_1121) rfl rfl⟩

/-- **A poll of warp 12** is of its site's poll barrier of its CTA, with the site's parity. -/
theorem mma_wait {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope} (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ (d : Mma.D) (B : FBar) (t : TState) (ins : Instr), Mma.Counts L g d ((X.tr g).take k) ∧
      Mma.Inv L g d ∧ Mma.pollBar L d = some B ∧ m = Mma.bar L g B ∧ p = Mma.pollPar L d ∧
      t.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      ∃ p' b off par sc0, ins.op = .mbarWait p' b off par acq sc0 ∧
        (asms.any (·.clusterScopeMbar t.pc) = true → acq = true → sc0 = .cta → sc = .cluster) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, u, -, hJ, hi, hpc, -, h, hc, hf⟩ :=
    mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
      (by rintro (⟨f, h⟩ | h) <;> cases h)
  obtain ⟨B, hB, hm, hp⟩ := wait_ev (Mma.site_event hpre hg h hc hf) rfl
  exact ⟨d, B, t, ins, hJ, hi, hB, hm, hp, hpc, hc, fires_wait_flags hf rfl⟩

/-- **A poll of warp 12 on a handshake barrier** is of its own CTA's, parity 0, at the wait
site; a successful one acquires at cluster scope. -/
theorem mma_hs_wait {g k pc p cta : Nat} {ok acq : Bool} {sc : MbarScope} (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .wait (FBar.loc L cta .dealloc) p ok acq sc⟩) :
    ∃ d : Mma.D, Mma.Counts L g d ((X.tr g).take k) ∧ d.site = .waitDealloc ∧
      cta = ctaOf L g ∧ p = 0 ∧ acq = true ∧ sc = .cluster := by
  obtain ⟨d, B, t, ins, hJ, -, hB, hm, hp, hpc, hc, hfl⟩ := mma_wait hpre hX ht hw he
  obtain ⟨rfl, rfl⟩ := FBar.loc_inj hm
  have hs : d.site = .waitDealloc := by
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp [Mma.pollBar] at hB
    rfl
  rw [hs] at hc hpc
  code_at hc
  subst hc
  obtain ⟨p', b, off, par, sc0, hop, hfl⟩ := hfl
  simp only [Op.mbarWait.injEq] at hop
  obtain ⟨-, -, -, -, rfl, rfl⟩ := hop
  exact ⟨d, hJ, hs, rfl, by rw [hp, Mma.pollPar, hs], rfl,
    hfl (by rw [hpc]; exact asms_cluster_1122) rfl
    rfl⟩

/-- The site of an event of warp 12 on barrier 2: one of the two `bar.sync 2`. -/
theorem mma_bar2 {g k pc id : Nat} {cnt : Option Nat} {md : BarMode} (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩) (hid : id = 2) :
    ∃ d : Mma.D, Mma.Counts L g d ((X.tr g).take k) ∧ (d.site = .bar0 ∨ d.site = .bar1) := by
  subst hid
  obtain ⟨d, t, ins, u, -, hJ, -, -, -, -, hc, hf⟩ :=
    mma_state_cont hpre hX ht he hw (by simp [Prologue.ProKind])
      (by rintro (⟨f, h⟩ | h) <;> cases h)
  have hb := (Mma.bar2_site hpre hc hf).1
  refine ⟨d, hJ, ?_⟩
  obtain ⟨site, i, tt, base, pro⟩ := d
  cases site <;> simp_all [Execution.isBarId, Mma.bar2Ev]

/-! ### `TmemFacts` (handshake, warp 12) -/

/-- **The field `TmemFacts.hs_arrive`, for warp 12.** -/
theorem TmemFacts_hs_arrive_mma {g k pc tx c cta : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (_ : g < L.threads) (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .arrive m tx c rel sc⟩) (hm : m = FBar.loc L cta .dealloc) :
    warpOf L g = 12 ∧ cta = pairCta (ctaOf L g) ∧ tx = 0 ∧ c = 1 ∧
      ∀ k' pc' tx' c' rel' sc', X.get (g, k') = some ⟨pc', .arrive m tx' c' rel' sc'⟩ → k' = k := by
  obtain ⟨d, hJ, hs, hm', rfl, rfl, -, -⟩ := mma_arrive hpre hX ht hw he
  rw [hm] at hm'
  obtain ⟨-, rfl⟩ := FBar.loc_inj hm'
  refine ⟨hw, peer_eq hpre g, rfl, rfl, fun k' pc' tx' c' rel' sc' he' => ?_⟩
  obtain ⟨d', hJ', hs', -⟩ := mma_arrive hpre hX ht hw he'
  have h1 := hJ.handoff
  have h2 := hJ'.handoff
  rw [hs] at h1
  rw [hs'] at h2
  simp only [Mma.handoffA] at h1 h2
  have ha : ∀ j pcj txj cj relj scj, X.get (g, j) = some ⟨pcj, .arrive m txj cj relj scj⟩ →
      ((X.tr g).take (j + 1)).countP (arrivesOn (FBar.loc L (Mma.peer L g) .dealloc)) =
        ((X.tr g).take j).countP (arrivesOn (FBar.loc L (Mma.peer L g) .dealloc)) + 1 :=
    fun j pcj txj cj relj scj hj => PTX.Flow.countP_take_succ hj (by
      simp [arrivesOn, sourceArrive, hm])
  unfold arrivals at h1 h2
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := PTX.Flow.countP_take_mono (arrivesOn (FBar.loc L (Mma.peer L g) .dealloc)) (X.tr g)
      (show k + 1 ≤ k' by omega)
    have := ha k pc 0 1 rel sc he
    omega
  · exact heq.symm
  · have := PTX.Flow.countP_take_mono (arrivesOn (FBar.loc L (Mma.peer L g) .dealloc)) (X.tr g)
      (show k' + 1 ≤ k by omega)
    have := ha k' pc' tx' c' rel' sc' he'
    omega

/-- **The field `TmemFacts.hs_wait`, for warp 12.** -/
theorem TmemFacts_hs_wait_mma {g k pc p cta : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (_ : g < L.threads) (hw : warpOf L g = 12) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (hm : m = FBar.loc L cta .dealloc) :
    warpOf L g = 12 ∧ cta = ctaOf L g ∧ p = 0 := by
  subst hm
  obtain ⟨-, -, -, hc, hp, -⟩ := mma_hs_wait hpre hX ht hw he
  exact ⟨hw, hc, hp⟩

/-- **The field `ExitFacts.hs_wait`, for warp 12.** -/
theorem ExitFacts_hs_wait_mma {g k pc p cta : Nat} {acq : Bool} {sc : MbarScope} (_ : g < L.threads)
    (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .wait (FBar.loc L cta .dealloc) p true acq sc⟩) :
    acq = true ∧ sc = .cluster := by
  obtain ⟨-, -, -, -, -, ha, hs⟩ := mma_hs_wait hpre hX ht hw he
  exact ⟨ha, hs⟩

/-- **The field `TmemLifeFacts.hs_release`, for warp 12.** -/
theorem TmemLifeFacts_hs_release_mma {g y pc tx c cta : Nat} {rel : Bool} {sc : MbarScope}
    (_ : g < L.threads) (hw : warpOf L g = 12)
    (he : X.get (g, y) = some ⟨pc, .arrive (FBar.loc L cta .dealloc) tx c rel sc⟩) :
    rel = true ∧ sc = .cluster ∧ ∃ b < y, Bar2Sync X g b 1 := by
  obtain ⟨d, hJ, hs, -, -, -, hr, hsc⟩ := mma_arrive hpre hX ht hw he
  exact ⟨hr, hsc, bar2_nth hJ (by rw [hs]; decide)⟩

/-- **The field `ExitFacts.hs_arrive`, for warp 12.** -/
theorem ExitFacts_hs_arrive_mma {g k pc tx cnt cta : Nat} {rel : Bool} {sc : MbarScope}
    (hg : g < L.threads) (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .arrive (FBar.loc L cta .dealloc) tx cnt rel sc⟩) :
    rel = true ∧ sc = .cluster ∧
      ∃ i < k, ∃ pci cnti, X.IsBarrier (g, i) 2 cnti pci ∧ barOrd X g i 2 = 1 := by
  obtain ⟨hr, hsc, b, hb, pcb, hgb, ho⟩ := TmemLifeFacts_hs_release_mma hpre hX ht hg hw he
  exact ⟨hr, hsc, b, hb, pcb, some 416, hgb, ho⟩

/-! ### `TmemLifeFacts` -/

/-- **The field `TmemLifeFacts.bar2_alloc`.** -/
theorem TmemLifeFacts_bar2_alloc {g b pc : Nat} {cnt : Option Nat} {m : BarMode}
    (hg : g < L.threads) (hw : warpOf L g = 12) (he : X.get (g, b) = some ⟨pc, .bar 2 cnt m⟩) :
    ∃ j < b, ∃ pca grp dst n, X.get (g, j) = some ⟨pca, .tc (.resource grp dst (.alloc n))⟩ := by
  obtain ⟨d, hJ, hs⟩ := mma_bar2 hpre hX ht hw he rfl
  have h1 : 0 + 1 ≤ Tmem.Pair.tmemOps ((X.tr g).take b) := by
    rw [hJ.tmem]
    rcases hs with hs | hs <;> rw [hs] <;> decide
  obtain ⟨j, e, hj, hej, hp, hcnt⟩ := exists_nthEv (X := X) (p := Tmem.Pair.isTmemOp) h1
  unfold Tmem.Pair.isTmemOp at hp
  split at hp
  · rename_i grp dst act hk
    obtain ⟨-, -, hsh, -⟩ := TmemFacts_event hpre hX ht hg (get_kind hej hk)
    have hz : Tmem.Pair.tmemOps ((X.tr g).take j) = 0 := hcnt
    rw [hz] at hsh
    exact ⟨j, hj, e.pc, grp, dst, 512, by rw [get_kind hej hk, show act = _ from hsh]⟩
  · cases hp

/-- The site of a deallocation. -/
theorem dealloc_state {g k pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) :
    warpOf L g = 12 ∧ ∃ d : Mma.D, Mma.Counts L g d ((X.tr g).take k) ∧ d.site = .dealloc := by
  obtain ⟨hw, d, t, ins, u, hJ, -, -, hs, h, hc, hf⟩ := tmem_state hpre hX ht he
  rcases tmem_site hpre hs h hc hf with ⟨-, -, -, h'⟩ | ⟨-, -, h'⟩ | ⟨hd, -⟩
  · cases h'
  · cases h'
  · exact ⟨hw, d, hJ, hd⟩

/-- **The field `TmemLifeFacts.dealloc_sync`.** -/
theorem TmemLifeFacts_dealloc_sync {g k pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}
    (_ : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) :
    ∃ b < k, Bar2Sync X g b 1 := by
  obtain ⟨-, d, hJ, hd⟩ := dealloc_state hpre hX ht he
  exact bar2_nth hJ (by rw [hd]; decide)

/-- **The field `TmemLifeFacts.dealloc_wait`.** -/
theorem TmemLifeFacts_dealloc_wait {g k pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}
    (_ : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) :
    ∃ w < k, ∃ pcw p, X.get (g, w) =
      some ⟨pcw, .wait (FBar.loc L (ctaOf L g) .dealloc) p true true .cluster⟩ := by
  obtain ⟨hw, d, hJ, hd⟩ := dealloc_state hpre hX ht he
  have h1 := hJ.dealloc
  rw [hd] at h1
  obtain ⟨j, pcj, p, acq, sc, hj, hgj⟩ := exists_okPoll (X := X) (by rw [h1]; decide)
  obtain ⟨-, -, -, -, -, rfl, rfl⟩ := mma_hs_wait hpre hX ht hw hgj
  exact ⟨j, hj, pcj, p, hgj⟩
end

/-- The positions of the MMAs. -/
abbrev issuePcs : List Nat := Flow.mma.toList

theorem kernel_issue_pcs : OpPcsFast kernel.code tcMmaOp issuePcs = true := by
  decide +kernel

theorem Loader.site_not_issue (s : Loader.Site) : s.pc ∉ issuePcs := by
  cases s <;> site_decide

theorem Store.site_not_issue (s : Store.Site) : s.pc ∉ issuePcs := by
  cases s <;> site_decide

theorem Idle.site_not_issue (s : Idle.Site) : s.pc ∉ issuePcs := by
  cases s <;> site_decide

theorem Correction.site_not_issue (s : Correction.Site) : s.pc ∉ issuePcs := by
  cases s <;> site_decide

theorem Softmax.site_not_issue (s : Softmax.Site) : s.pc ∉ issuePcs := by
  cases s <;> site_decide

/-- **An MMA fires at an MMA site of the MMA role.** -/
theorem mma_issue_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {x : EvId} (hm : IsMma X x) :
    warpOf L x.1 = 12 ∧ ∃ d : Mma.D, Mma.Counts L x.1 d ((X.tr x.1).take x.2) ∧ Mma.Inv L x.1 d ∧
      d.site.isMma = true := by
  obtain ⟨g, k⟩ := x
  obtain ⟨dd, sp, acc, mask, pc, he⟩ := hm
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  have hpc := OpPcsFast.mem kernel_issue_pcs hc (fires_tcMma_op hf rfl)
  rcases d with p | r
  · exact absurd (pro_event hpre hX he hσ (fun f h => by cases h)).proKind
      (by simp [Prologue.ProKind])
  cases r with
  | idle s => exact absurd hpc (Idle.site_not_issue s.site)
  | loader l => exact absurd hpc (Loader.site_not_issue l.site)
  | store s => exact absurd hpc (Store.site_not_issue s.site)
  | softmax s => exact absurd hpc (Softmax.site_not_issue s.site)
  | corr c => exact absurd hpc (Correction.site_not_issue c.site)
  | mma m =>
    have hw : RoleKind.Warp .mma (warpOf L g) :=
      role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k
        (.mma m) hσ
    refine ⟨hw, m, hJ, hi.1, ?_⟩
    cases hs : m.site.isMma
    · have := Mma.isMma_ev (Mma.site_event hpre hg hat.2.2.2.2 hc hf) hs
      simp [Mma.isMma] at this
    · rfl

/-- **The field `TmemLifeFacts.mma_sync`.** -/
theorem TmemLifeFacts_mma_sync (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {x : EvId} (hm : IsMma X x) :
    ∃ b < x.2, Bar2Sync X x.1 b 0 := by
  obtain ⟨-, d, hJ, -, hs⟩ := mma_issue_state hpre hX ht hm
  refine bar2_nth hJ ?_
  obtain ⟨site, i, tt, base, pro⟩ := d
  cases site <;> simp_all [Mma.Site.isMma, Mma.bar2A]

/-! ### The base word -/

/-- **The field `OlderFacts.base_written`.** -/
theorem OlderFacts_base_written (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g i pc : Nat} {cnt : Option Nat} {m : BarMode}
    (_ : g < L.threads) (h384 : g % L.block = 384) (he : X.get (g, i) = some ⟨pc, .bar 2 cnt m⟩) :
    ∃ k < i, ∃ a bs, X.Writes (g, k) a bs ∧ a.loc = baseLoc L (ctaOf L g) ∧ a.size = 4 := by
  have hw : warpOf L g = 12 := by simp only [warpOf, h384]
  obtain ⟨d, hJ, hs⟩ := mma_bar2 hpre hX ht hw he rfl
  obtain ⟨x, hx, a, bs, hk, hloc, hsz⟩ := hJ.wrote (by simp only [laneOf, h384])
    (by rcases hs with hs | hs <;> rw [hs] <;> decide)
  obtain ⟨k, hk', hgk⟩ := mem_take_get hx
  exact ⟨k, hk', a, bs, ⟨x.pc, by rw [hgk, ← hk]⟩, hloc, hsz⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
