-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsOn
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftEvents
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftRegs
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Credit
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.SFull

@[expose] public section

/-! # The softmax warps' polls

`CreditPollFacts.poll` and `SFullPollFacts.poll`: a softmax thread at a statistics-credit poll
(`statsW k`) or an S-full poll (`sW lp`) polls its stage's barrier of its CTA with the parity its
register holds (`Softmax.regs_*`, `ev_waitPar`; the address and parity registers evaluate, so the
template is not undefined behaviour), which is that of its successful polls of the barrier, plus
one for the credit (`Softmax.Counts.stats`, `Softmax.Counts.score`, with `Softmax.Inv.tile0` and
`Softmax.Inv.tail`), as in `soft_wait`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A softmax poll site: its template is a wait on the thread's CTA's barrier at `off`, with the
parity its register holds. -/
theorem soft_wait_site (hpre : Pre P L mem0) {g : Nat} {t : TState} {ins : Instr}
    {pc p r q off x : Nat}
    (hcode : kernel.code[pc]? = some ⟨none, .mbarWait p r 0 (.reg q) true .cta⟩)
    (hr : t.regs r = some (Prologue.sb L off)) (hq : t.regs q = some (b32 (x % 2)))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins) :
    (∀ f, eventTmpl asms L g t ins.op ≠ .ub f) ∧
      ∀ l p' ok acq sc u, Fires pc (eventTmpl asms L g t ins.op) ⟨pc, .wait l p' ok acq sc⟩
        (some u) → l = Softmax.ownLoc L g off ∧ p' = x % 2 := by
  refine ⟨fun f => ?_, fun l p' ok acq sc u hf => ?_⟩
  · obtain rfl := Option.some.inj (hins.symm.trans hcode)
    have hbase := hpre.sharedRange
    have hal := hpre.sharedAlignment
    unfold sharedBytes at hbase
    have hr' := hr
    simp only [Prologue.sb] at hr'
    obtain ⟨k, sc', h⟩ := eventTmpl_mbarWait_ok (A := asms) (p := p) (acq := true) (sc := .cta)
      (mbarLoc_b32 (L := L) (g := g) hr' (by omega) (by omega)) (readBits_b32' hq)
    rw [h]
    simp
  · obtain ⟨ok', acq', sc', hk⟩ := ev_waitPar hpre hcode hr hq hoff h8 hins hf
    simp only [Kind.wait.injEq] at hk
    exact ⟨hk.1, hk.2.1⟩

/-- The common part of a softmax poll. -/
theorem soft_pollsOn (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g : Nat} {d : Softmax.D} {off δ : Nat}
    (hg : g < L.threads) (hσ : St L X g (X.tr g).length = some (some (.inr (.softmax d))))
    (hk : softmaxKind d.site = .wait)
    (hsite : ∀ t ins, Holds t.regs (Softmax.facts L g d) →
      kernel.code[d.site.pc]? = some ins → ∃ x,
      (∀ f, eventTmpl asms L g t ins.op ≠ .ub f) ∧
      (∀ l p' ok acq sc u, Fires d.site.pc (eventTmpl asms L g t ins.op)
        ⟨d.site.pc, .wait l p' ok acq sc⟩ (some u) → l = Softmax.ownLoc L g off ∧ p' = x % 2) ∧
      (Softmax.Counts L g d (X.tr g) → Softmax.Inv L g d →
        x % 2 = (okPolls (Softmax.ownLoc L g off) (X.tr g) + δ) % 2)) :
    PollsOn L X g (Softmax.ownLoc L g off) δ := by
  refine pollsOn_of_end hpre hX ht hg hσ hk (fun _ t ins hat _ hc f => ?_)
    (fun hJ t ins hat hi hc l p ok acq sc u hf => ?_)
  · obtain ⟨x, hub, -⟩ := hsite t ins hat.2.2.2.2 hc
    exact hub f
  · obtain ⟨x, -, hev, hpar⟩ := hsite t ins hat.2.2.2.2 hc
    obtain ⟨rfl, rfl⟩ := hev l p ok acq sc u hf
    exact ⟨rfl, by rw [Nat.mod_mod]; exact hpar hJ hi⟩

/-- **`CreditPollFacts.poll`**. -/
theorem CreditPollFacts_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat} {d : Softmax.D}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.softmax d))) → (∃ k, d.site = .statsW k) →
        PollsOn L X g (statsBar L (ctaOf L g) (warpOf L g / 4)) 1 := by
  intro g d hg hσ ⟨w, hsd⟩
  have hst : Softmax.stOf L g < 2 := by
    have hw : warpOf L g < 8 := Cross.role_of_state hpre hX hg hσ
    simp only [Softmax.stOf]
    omega
  show PollsOn L X g (Softmax.ownLoc L g (240 + 8 * Softmax.stOf L g)) 1
  refine soft_pollsOn hpre hX ht hg hσ (by rw [hsd]; rfl) fun t ins h4 hcode => ?_
  rw [hsd] at hcode
  rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := Softmax.regs_statsW0 hsd h4
    obtain ⟨hu, hv⟩ := soft_wait_site hpre Flow.code_mbarWait_30 h1 h2 (by omega) (by omega) hcode
    refine ⟨_, hu, by rw [hsd]; exact hv, fun hc hi => ?_⟩
    have hs := hc.stats
    have ht0 := hi.tile0
    rw [hs]
    have := ht0 (by rw [hsd]; rfl)
    simp [Softmax.statsIdx, Softmax.statsPos, Softmax.Site.inItem, hsd] at this ⊢
    omega
  · obtain ⟨h1, h2⟩ := Softmax.regs_statsW1 hsd h4
    obtain ⟨hu, hv⟩ := soft_wait_site hpre Flow.code_mbarWait_32 h1 h2 (by omega) (by omega) hcode
    refine ⟨_, hu, by rw [hsd]; exact hv, fun hc hi => ?_⟩
    have hs := hc.stats
    have ht0 := hi.tile0
    rw [hs]
    have := ht0 (by rw [hsd]; rfl)
    simp [Softmax.statsIdx, Softmax.statsPos, Softmax.Site.inItem, Softmax.Site.tile0, hsd]
      at this ⊢
    omega
  · obtain ⟨h1, h2⟩ := Softmax.regs_statsW2 hsd h4
    obtain ⟨hu, hv⟩ := soft_wait_site hpre Flow.code_mbarWait_34 h1 h2 (by omega) (by omega) hcode
    refine ⟨_, hu, by rw [hsd]; exact hv, fun hc hi => ?_⟩
    rw [hc.stats]
    simp [Softmax.statsIdx, Softmax.statsPos, Softmax.Site.inItem, Softmax.Site.tile0, hsd]
    omega
  · obtain ⟨h1, h2⟩ := Softmax.regs_statsW3 hsd h4
    obtain ⟨hu, hv⟩ := soft_wait_site hpre Flow.code_mbarWait_35 h1 h2 (by omega) (by omega) hcode
    refine ⟨_, hu, by rw [hsd]; exact hv, fun hc hi => ?_⟩
    rw [hc.stats]
    have := (hi.tail (.inl hsd)).2
    simp [Softmax.statsIdx, Softmax.tailPos, Softmax.Site.inItem, hsd] at this ⊢
    omega

/-- **`SFullPollFacts.poll`**. -/
theorem SFullPollFacts_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat} {d : Softmax.D} {lp : Bool}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.softmax d))) → d.site = .sW lp →
        PollsOn L X g (sFullBar L (ctaOf L g) (warpOf L g / 4)) 0 := by
  intro g d lp hg hσ hsd
  have hst : Softmax.stOf L g < 2 := by
    have hw : warpOf L g < 8 := Cross.role_of_state hpre hX hg hσ
    simp only [Softmax.stOf]
    omega
  show PollsOn L X g (Softmax.ownLoc L g (128 + 8 * Softmax.stOf L g)) 0
  refine soft_pollsOn hpre hX ht hg hσ (by rw [hsd]; rfl) fun t ins h4 hcode => ?_
  rw [hsd] at hcode
  cases lp
  · obtain ⟨h1, h2⟩ := Softmax.regs_sW0 hsd h4
    obtain ⟨hu, hv⟩ := soft_wait_site hpre Flow.code_mbarWait_31 h1 h2 (by omega) (by omega) hcode
    refine ⟨_, hu, by rw [hsd]; exact hv, fun hc hi => ?_⟩
    rw [hc.score]
    have := hi.tile0 (by rw [hsd]; rfl)
    simp [Softmax.tileIdx, Softmax.sPos, hsd, Softmax.Site.tile0Ld, Softmax.Site.tile0,
      Softmax.Site.inTrip] at this ⊢
  · obtain ⟨h1, h2⟩ := Softmax.regs_sW1 hsd h4
    obtain ⟨hu, hv⟩ := soft_wait_site hpre Flow.code_mbarWait_33 h1 h2 (by omega) (by omega) hcode
    refine ⟨_, hu, by rw [hsd]; exact hv, fun hc hi => ?_⟩
    rw [hc.score]
    simp [Softmax.tileIdx, Softmax.sPos, hsd, Softmax.Site.tile0]
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
