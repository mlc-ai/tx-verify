-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll

@[expose] public section

/-! # Successful polls in the query-copy prologue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow PTX.Proof MBarrier

/-- A Tensor Core thread waits for the query TMA. The MMA, gather and dequant roles wait for the
query Tensor Memory copy. -/
inductive QueryWait (d : Machine.ThreadD) : Bool → Prop where
  | tensor (s : Wg1Mma.D) :
      d = .mma s → s.site = .qWait → QueryWait d false
  | copy (s : Wg1Mma.D) :
      d = .mma s → s.site = .qCopyWait → QueryWait d true
  | gather (s : Wg1Tma.D) :
      d = .tma s → s.site = .waitQ → QueryWait d true
  | dequant (s : Wg2.D) :
      d = .wg2 s → s.site = .qUtccp → QueryWait d true

def queryWaitObject (L : Launch) (g : Nat) (copy : Bool) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + if copy then 222784 else 222776⟩

private theorem query_wait_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {d : Machine.ThreadD} {copy : Bool} {ins : Instr} (hpre : Pre P L mem0)
    (hd : QueryWait d copy) (ha : (Machine.code P L g).AtD d t)
    (hv : (Machine.code P L g).inv d)
    (hc : kernel.code[(Machine.code P L g).pc d]? = some ins) :
    ∃ k, eventTmpl Assumptions.all L g t ins.op =
      .wait (queryWaitObject L g copy) 0 k true .cta := by
  cases hd with
  | tensor s hstate hsite =>
    subst d
    change (Wg1Mma.code P L g).AtD s t at ha
    have hpc : s.site.pc = 1931 := by rw [hsite]; rfl
    change kernel.code[s.site.pc]? = some ins at hc
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_3)
    have hb : t.regs 811 = some (sb L 222776) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some, sb,
        Wg1Mma.qTmaAddr_eq] using Wg1Mma.atD_reg ha (r := 811) hpc (by decide +kernel)
    have hp : t.regs 812 = some (b32 0) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some] using
        Wg1Mma.atD_reg ha (r := 812) hpc (by decide +kernel)
    exact poll_regs_template hpre hb hp (by decide) (by decide) (by decide)
  | copy s hstate hsite =>
    subst d
    change (Wg1Mma.code P L g).AtD s t at ha
    have hpc : s.site.pc = 1983 := by rw [hsite]; rfl
    change kernel.code[s.site.pc]? = some ins at hc
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_4)
    have hb : t.regs 843 = some (sb L 222784) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some, sb,
        Wg1Mma.qUtccpAddr_eq] using Wg1Mma.atD_reg ha (r := 843) hpc (by decide +kernel)
    have hp : t.regs 812 = some (b32 0) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some] using
        Wg1Mma.atD_reg ha (r := 812) hpc (by decide +kernel)
    exact poll_regs_template hpre hb hp (by decide) (by decide) (by decide)
  | gather s hstate hsite =>
    subst d
    change (Wg1Tma.code P L g).AtD s t at ha
    have hpc : s.site.pc = 2205 := by rw [hsite]; rfl
    change kernel.code[s.site.pc]? = some ins at hc
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2205)
    have hb : t.regs 669 = some (sb L 222784) :=
      Wg1Tma.atD_regAt ha hpc (by decide +kernel)
    have hp : t.regs 670 = some (b32 0) :=
      Wg1Tma.atD_regAt ha hpc (by decide +kernel)
    exact poll_regs_template hpre hb hp (by decide) (by decide) (by decide)
  | dequant s hstate hsite =>
    subst d
    change Wg2.AtD P L g s t at ha
    change Wg2.Inv P L g s at hv
    have hpc : s.site.pc = 2644 := by rw [hsite]; rfl
    change kernel.code[s.site.pc]? = some ins at hc
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_13)
    have hPar : s.par = 0 := by rw [hv.parBlock, hv.qUtccpBlock hsite]
    have hBase : t.regs 2434 = some (sb L Wg2.qUtccpOff) :=
      Wg2.AtD.regAt ha hpc (by decide +kernel)
    have hParity : t.regs 2435 = some (b32 0) := by
      rw [← hPar]
      exact Wg2.AtD.regAt ha hpc (by decide +kernel)
    exact poll_regs_template hpre hBase hParity (by decide) (by decide) (by decide)

/-- The producer can pass its query-load or query-copy wait once the object's phase turns. -/
theorem query_poll_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Machine.ThreadD} {copy : Bool} {before : State}
    (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hd : QueryWait d copy)
    (hstate : stateBefore (X.objects (queryWaitObject L g copy))
      (X.objects (queryWaitObject L g copy)).length = some before)
    (hready : before.phase % 2 ≠ 0) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    cases hd <;> contradiction
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, ha, hv, hc, hout⟩ := Frame.end_at hs hp.1 hr hσ
  obtain ⟨k, htmpl⟩ := query_wait_template hpre hd ha hv hc
  rw [htmpl] at hout
  exact poll_extension hX hp.1 hne hrel hr hτ hout hstate hready

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
