-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingPhases
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaGemmTrace

@[expose] public section

/-! # Successful input polls of the MMA loop -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof MBarrier

/-- The two producer handoffs acquired by the MMA lane in each block. -/
inductive MmaWait where
  | dequant
  | score

def MmaWait.site : MmaWait → Wg1Mma.Site
  | .dequant => .kvWait
  | .score => .soWait

def MmaWait.stream : MmaWait → Wg1MmaGemmTrace.Stream
  | .dequant => .dequant
  | .score => .score

def MmaWait.object (w : MmaWait) (L : Launch) (g : Nat) (d : Wg1Mma.D) : Loc :=
  w.stream.loc L g (Protocol.rawSlot d.i)

private theorem mma_wait_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {d : Wg1Mma.D} {w : MmaWait} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = w.site) (ha : (Wg1Mma.code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ k, eventTmpl Assumptions.all L g t ins.op =
      .wait (w.object L g d) (Wg1Mma.parOf d.i) k true .cta := by
  have hpar : Wg1Mma.parOf d.i < 2 := by
    change d.i / 2 % 2 < 2
    omega
  have hi : d.i % 2 < 2 := Nat.mod_lt _ (by decide)
  cases w with
  | dequant =>
    have hpc : d.site.pc = 2012 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_5)
    have hb : t.regs 855 = some (sb L (222792 + 8 * (d.i % 2))) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some, sb,
        Wg1Mma.dequantAddr_eq, Nat.add_assoc] using
        Wg1Mma.atD_reg ha (r := 855) hpc (by decide +kernel)
    have hp : t.regs 879 = some (b32 (Wg1Mma.parOf d.i)) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some] using
        Wg1Mma.atD_reg ha (r := 879) hpc (by decide +kernel)
    exact poll_regs_template (off := 222792 + 8 * (d.i % 2)) hpre hb hp
      (by omega) (by omega) hpar
  | score =>
    have hpc : d.site.pc = 2107 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_6)
    have hb : t.regs 878 = some (sb L (222920 + 8 * (d.i % 2))) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some, sb,
        Wg1Mma.soReadyAddr_eq, Nat.add_assoc] using
        Wg1Mma.atD_reg ha (r := 878) hpc (by decide +kernel)
    have hp : t.regs 879 = some (b32 (Wg1Mma.parOf d.i)) := by
      simpa [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some] using
        Wg1Mma.atD_reg ha (r := 879) hpc (by decide +kernel)
    exact poll_regs_template (off := 222920 + 8 * (d.i % 2)) hpre hb hp
      (by omega) (by omega) hpar

/-- When a GEMM producer has published the requested phase, the MMA thread can acquire it. -/
theorem mma_poll_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Mma.D} {w : MmaWait} {before : State} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = w.site)
    (hstate : stateBefore (X.objects (w.object L g d)) (X.objects (w.object L g d)).length =
      some before)
    (hready : before.phase % 2 ≠ Wg1Mma.parOf d.i % 2) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hr hσ
  obtain ⟨k, htmpl⟩ := mma_wait_template hpre hd ha hc
  rw [htmpl] at hout
  exact poll_extension hX hp.1 hne hrel hr hτ hout hstate hready

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
