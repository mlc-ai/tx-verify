-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsOn
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsCorrRegs
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.OFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Free

@[expose] public section

/-! # The correction warps' polls

`OFullPollFacts.poll` and `FreePollFacts.poll`: a correction thread at its O-full poll
(`oWait st`) or its staging-free poll (`fWait st`, or the last one `tailWait` of stage 1) polls
the stage's barrier of its CTA with the parity its register holds (`Correction.ev_waitOwn`; the
address and parity registers evaluate, so the template is not undefined behaviour), which is that
of its successful polls of the barrier, plus one for the free barrier (`Correction.Counts.oFull`,
`Correction.Counts.oFree`), as in `Facts.Corr.o_poll` and `Facts.Corr.free_poll`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A correction poll site: its template is a wait on the thread's CTA's barrier at `off`, with
the parity its register holds. -/
theorem corr_wait_site (hpre : Pre P L mem0) {g : Nat} {t : TState} {ins : Instr}
    {pc p r q off x : Nat}
    (hcode : kernel.code[pc]? = some ⟨none, .mbarWait p r 0 (.reg q) true .cta⟩)
    (hr : t.regs r = some (b32 (Correction.sb L + off))) (hq : t.regs q = some (b32 (x % 2)))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins) :
    (∀ f, eventTmpl asms L g t ins.op ≠ .ub f) ∧
      ∀ l p' ok acq sc u, Fires pc (eventTmpl asms L g t ins.op) ⟨pc, .wait l p' ok acq sc⟩
        (some u) → l = Correction.ownLoc L g off ∧ p' = x % 2 := by
  refine ⟨fun f => ?_, fun l p' ok acq sc u hf => ?_⟩
  · obtain rfl := Option.some.inj (hins.symm.trans hcode)
    have hbase := hpre.sharedRange
    have hal := hpre.sharedAlignment
    unfold sharedBytes at hbase
    obtain ⟨k, sc', h⟩ := eventTmpl_mbarWait_ok (A := asms) (p := p) (acq := true) (sc := .cta)
      (mbarLoc_b32 (L := L) (g := g) hr (by simp only [Correction.sb]; omega)
        (by simp only [Correction.sb]; omega)) (Correction.readBits_word hq (by omega))
    rw [h]
    simp
  · obtain ⟨ok', acq', sc', hk⟩ := Correction.ev_waitOwn hpre hcode hr hq hoff h8 hins hf
    simp only [Kind.wait.injEq] at hk
    exact ⟨hk.1, hk.2.1⟩

/-- The common part of a correction poll. -/
theorem corr_pollsOn (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g : Nat} {d : Correction.D} {off δ : Nat}
    (hg : g < L.threads) (hσ : St L X g (X.tr g).length = some (some (.inr (.corr d))))
    (hk : corrKind d.site = .wait)
    (hsite : ∀ t ins, Holds t.regs (Correction.facts L g d) →
      kernel.code[d.site.pc]? = some ins → ∃ x,
      (∀ f, eventTmpl asms L g t ins.op ≠ .ub f) ∧
      (∀ l p' ok acq sc u, Fires d.site.pc (eventTmpl asms L g t ins.op)
        ⟨d.site.pc, .wait l p' ok acq sc⟩ (some u) → l = Correction.ownLoc L g off ∧
          p' = x % 2) ∧
      (Correction.Counts L g d (X.tr g) →
        x % 2 = (okPolls (Correction.ownLoc L g off) (X.tr g) + δ) % 2)) :
    PollsOn L X g (Correction.ownLoc L g off) δ := by
  refine pollsOn_of_end hpre hX ht hg hσ hk (fun _ t ins hat _ hc f => ?_)
    (fun hJ t ins hat _ hc l p ok acq sc u hf => ?_)
  · obtain ⟨x, hub, -⟩ := hsite t ins hat.2.2.2.2 hc
    exact hub f
  · obtain ⟨x, -, hev, hpar⟩ := hsite t ins hat.2.2.2.2 hc
    obtain ⟨rfl, rfl⟩ := hev l p ok acq sc u hf
    exact ⟨rfl, by rw [Nat.mod_mod]; exact hpar hJ⟩

/-- **`OFullPollFacts.poll`**. -/
theorem OFullPollFacts_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat} {d : Correction.D} {st : Fin 2}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.corr d))) → d.site = .oWait st →
        PollsOn L X g (oFullBar L (ctaOf L g) st) 0 := by
  intro g d st hg hσ hsd
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hsd
  subst hsd
  rcases Store.fin2_cases st with rfl | rfl
  · show PollsOn L X g (Correction.ownLoc L g 192) 0
    have h1 := corr_pollsOn (off := 192) (δ := 0) hpre hX ht hg hσ rfl
    refine h1 fun t ins h4 hcode => ?_
    obtain ⟨hu, hv⟩ := corr_wait_site (x := i) (off := 192) hpre Flow.code_mbarWait_36
      (Correction.regs_oWait0 h4).1
      (Correction.regs_oWait0 h4).2 (by decide) (by decide) hcode
    refine ⟨i, hu, hv, fun hc => ?_⟩
    rw [Nat.add_zero, hc.oFull 0 (by decide)]
    simp [Correction.oPos]
  · show PollsOn L X g (Correction.ownLoc L g 200) 0
    have h1 := corr_pollsOn (off := 200) (δ := 0) hpre hX ht hg hσ rfl
    refine h1 fun t ins h4 hcode => ?_
    obtain ⟨hu, hv⟩ := corr_wait_site (x := i) (off := 200) hpre Flow.code_mbarWait_38
      (Correction.regs_oWait1 h4).1
      (Correction.regs_oWait1 h4).2 (by decide) (by decide) hcode
    refine ⟨i, hu, hv, fun hc => ?_⟩
    rw [Nat.add_zero, hc.oFull 1 (by decide)]
    simp [Correction.oPos]

/-- **`FreePollFacts.poll`**. -/
theorem FreePollFacts_poll (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat} {d : Correction.D} {st : Fin 2}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.corr d))) → FreeSite d.site st →
        PollsOn L X g (freeBar L (ctaOf L g) st) 1 := by
  intro g d st hg hσ hsd
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  rcases hsd with hsd | ⟨hsd, rfl⟩ <;> simp only at hsd <;> subst hsd
  · rcases Store.fin2_cases st with rfl | rfl
    · show PollsOn L X g (Correction.ownLoc L g 272) 1
      have h1 := corr_pollsOn (off := 272) (δ := 1) hpre hX ht hg hσ rfl
      refine h1 fun t ins h4 hcode => ?_
      obtain ⟨hu, hv⟩ := corr_wait_site (x := i + 1) (off := 272) hpre Flow.code_mbarWait_37
        (Correction.regs_fWait0 h4).1 (Correction.regs_fWait0 h4).2 (by decide) (by decide) hcode
      refine ⟨i + 1, hu, hv, fun hc => ?_⟩
      rw [hc.oFree 0 (by decide)]
      simp [Correction.fPos]
    · show PollsOn L X g (Correction.ownLoc L g 280) 1
      have h1 := corr_pollsOn (off := 280) (δ := 1) hpre hX ht hg hσ rfl
      refine h1 fun t ins h4 hcode => ?_
      obtain ⟨hu, hv⟩ := corr_wait_site (x := i + 1) (off := 280) hpre Flow.code_mbarWait_39
        (Correction.regs_fWait1 h4).1 (Correction.regs_fWait1 h4).2 (by decide) (by decide) hcode
      refine ⟨i + 1, hu, hv, fun hc => ?_⟩
      rw [hc.oFree 1 (by decide)]
      simp [Correction.fPos]
  · show PollsOn L X g (Correction.ownLoc L g 280) 1
    have h1 := corr_pollsOn (off := 280) (δ := 1) hpre hX ht hg hσ rfl
    refine h1 fun t ins h4 hcode => ?_
    obtain ⟨hu, hv⟩ := corr_wait_site (x := i + 1) (off := 280) hpre Flow.code_mbarWait_40
      (Correction.regs_tailWait h4).1 (Correction.regs_tailWait h4).2 (by decide) (by decide) hcode
    refine ⟨i + 1, hu, hv, fun hc => ?_⟩
    rw [hc.oFree 1 (by decide)]
    simp [Correction.fPos]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
