-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll

public section

/-! # The producer's last-store success poll -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof MBarrier

private theorem last_store_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {d : Wg1Tma.D} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = .waitLast) (ha : (Wg1Tma.code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ k, eventTmpl Assumptions.all L g t ins.op =
      .wait ⟨.shared, ctaOf L g, L.sharedBase + 222768⟩ 0 k true .cta := by
  have hpc : d.site.pc = 2209 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2209)
  have hb : t.regs 672 = some (sb L 222768) :=
    Wg1Tma.atD_regAt ha hpc (by decide +kernel)
  have hp : t.regs 670 = some (b32 0) :=
    Wg1Tma.atD_regAt ha hpc (by decide +kernel)
  exact poll_regs_template hpre hb hp (by decide) (by decide) (by decide)

/-- The released TMA producer can return from its last-store poll once the phase turns. -/
theorem last_store_poll_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Tma.D} {before : State}
    (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.tma d)))
    (hd : d.site = .waitLast)
    (hstate : stateBefore (X.objects ⟨.shared, ctaOf L g, L.sharedBase + 222768⟩)
      (X.objects ⟨.shared, ctaOf L g, L.sharedBase + 222768⟩).length = some before)
    (hready : before.phase % 2 ≠ 0) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hr hσ
  obtain ⟨k, htmpl⟩ := last_store_template hpre hd ha hc
  rw [htmpl] at hout
  exact poll_extension hX hp.1 hne hrel hr hτ hout hstate hready

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
