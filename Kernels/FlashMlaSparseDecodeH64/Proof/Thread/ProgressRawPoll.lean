-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingLogs

public section

/-! # Successful raw-buffer reuse polls -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof MBarrier Protocol

/-- The physical raw slot used by this block. -/
@[expose] def rawSlot (block : Nat) : Fin 2 := ⟨block % 2, Nat.mod_lt _ (by decide)⟩

private theorem raw_free_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : Wg1Tma.D} {t : TState} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = .waitFree) (ha : (Wg1Tma.code P L g).AtD d t)
    (hi : Wg1Tma.Inv P L g d) (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ k, eventTmpl Assumptions.all L g t ins.op =
      .wait (RawRing.free L (ctaOf L g) (rawSlot d.block)) (1 - d.block / 2 % 2) k true .cta := by
  have hSite : d.site.pc = 2245 := by rw [hd]; rfl
  rw [hSite] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_10)
  have hb : t.regs 688 = some (sb L (Wg1Tma.rawFreeOff d.buf)) :=
    Wg1Tma.atD_regAt ha hSite (by decide +kernel)
  have hp : t.regs 689 = some (b32 (1 - d.rpar)) :=
    Wg1Tma.atD_regAt ha hSite (by decide +kernel)
  have hBuf := hi.buf_eq (by rw [hd]; decide) (by rw [hd]; decide)
  have hPar := hi.rpar_eq (by rw [hd]; decide) (by rw [hd]; decide)
  rw [hBuf] at hb
  rw [hPar] at hp
  exact poll_regs_template (off := Wg1Tma.rawFreeOff (d.block % 2)) hpre hb hp
    (by unfold Wg1Tma.rawFreeOff; omega) (by unfold Wg1Tma.rawFreeOff; omega) (by omega)

/-- The TMA producer can acquire the raw buffer once the slot's phase has turned. -/
theorem raw_free_poll_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Tma.D} {before : State}
    (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.tma d)))
    (hd : d.site = .waitFree)
    (hstate : stateBefore (X.objects (RawRing.free L (ctaOf L g) (rawSlot d.block)))
      (X.objects (RawRing.free L (ctaOf L g) (rawSlot d.block))).length = some before)
    (hready : before.phase % 2 ≠ (1 - d.block / 2 % 2) % 2) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hr hσ
  obtain ⟨k, htmpl⟩ := raw_free_template hpre hd ha hi hc
  rw [htmpl] at hout
  exact poll_extension hX hp.1 hne hrel hr hτ hout hstate hready

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
