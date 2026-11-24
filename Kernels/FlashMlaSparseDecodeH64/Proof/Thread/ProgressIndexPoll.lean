-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll

@[expose] public section

/-! # Success extensions for the index ring's three poll sites -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof MBarrier Protocol

/-- The softmax and TMA consumers wait for publication. The index producer waits for reuse. -/
inductive IndexWait : Machine.ThreadD → Bool → Nat → Prop where
  | softmax {d : Wg0.D} : d.site = .maskReady → IndexWait (.wg0 d) false d.block
  | gather {d : Wg1Tma.D} : d.site = .waitCoord → IndexWait (.tma d) false d.block
  | producer {d : Wg1Index.D} {extra : Bool} :
      d.site = .waitFree extra → IndexWait (.index d) true d.block

/-- The ring slot associated with the current logical block. -/
def indexWaitSlot (block : Nat) : Fin 4 := ⟨block % 4, Nat.mod_lt _ (by decide)⟩

/-- Reuse of a slot polls the opposite parity from its consumers. -/
def indexWaitParity (free : Bool) (block : Nat) : Nat :=
  if free then 1 - block / 4 % 2 else block / 4 % 2

def indexWaitObject (L : Launch) (g : Nat) (free : Bool) (block : Nat) : Loc :=
  if free then IndexRing.free L (ctaOf L g) (indexWaitSlot block)
  else IndexRing.ready L (ctaOf L g) (indexWaitSlot block)

private theorem index_wait_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : Machine.ThreadD} {free : Bool} {block : Nat} {t : TState} {ins : Instr}
    (hpre : Pre P L mem0) (hd : IndexWait d free block)
    (ha : (Machine.code P L g).AtD d t) (hi : (Machine.code P L g).inv d)
    (hc : kernel.code[(Machine.code P L g).pc d]? = some ins) :
    ∃ k, eventTmpl Assumptions.all L g t ins.op =
      .wait (indexWaitObject L g free block) (indexWaitParity free block) k true .cta := by
  cases hd
  case softmax q hd =>
    have hsite : q.site.pc = 264 := by rw [hd]; rfl
    change kernel.code[q.site.pc]? = some ins at hc
    rw [hsite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_0)
    have hb : t.regs 974 = some (sb L (Wg0.validReadyOff (q.block % 4))) :=
      Wg0.reg974 ha hd
    have hp := Wg0.reg975 ha hd
    simpa [indexWaitObject, indexWaitParity, indexWaitSlot, IndexRing.ready, Mbar.loc,
      Mbar.off, Wg0.validReadyOff, ctaOf] using poll_regs_template hpre hb hp
        (by unfold Wg0.validReadyOff; omega) (by unfold Wg0.validReadyOff; omega) (by omega)
  case gather q hd =>
    have hsite : q.site.pc = 2234 := by rw [hd]; rfl
    change (Wg1Tma.code P L g).AtD q t at ha
    change Wg1Tma.Inv P L g q at hi
    change kernel.code[q.site.pc]? = some ins at hc
    rw [hsite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_9)
    have hb : t.regs 685 = some (sb L (Wg1Tma.readyOff q.phase)) :=
      Wg1Tma.atD_regAt ha hsite (by decide +kernel)
    have hp : t.regs 686 = some (b32 q.par) :=
      Wg1Tma.atD_regAt ha hsite (by decide +kernel)
    have hslot := hi.phase_eq (by rw [hd]; decide) (by rw [hd]; decide)
    have hphase := hi.par_eq (by rw [hd]; decide) (by rw [hd]; decide)
    rw [hslot] at hb
    rw [hphase] at hp
    simpa [indexWaitObject, indexWaitParity, indexWaitSlot, IndexRing.ready, Mbar.loc,
      Mbar.off, Wg1Tma.readyOff, ctaOf] using poll_regs_template hpre hb hp
        (by unfold Wg1Tma.readyOff; omega) (by unfold Wg1Tma.readyOff; omega) (by omega)
  case producer q extra hd =>
    change Wg1Index.AtD P L g q t at ha
    change Wg1Index.Inv P L g q at hi
    change kernel.code[q.site.pc]? = some ins at hc
    have hne : q.site ≠ .barrier := by rw [hd]; intro h; cases h
    have of_regs {base par dst : Nat}
        (hm : base ∈ (Flow.live q.site.pc).filter (fun r => Wg1Index.tracked.contains r))
        (hp : par ∈ (Flow.live q.site.pc).filter (fun r => Wg1Index.tracked.contains r))
        (hbase : Wg1Index.valueOf P L g q base = sb L (Wg1Index.freeOff q.phase))
        (hpar : Wg1Index.valueOf P L g q par = b32 (1 - q.par)) :
        ∃ k, eventTmpl Assumptions.all L g t (.mbarWait dst base 0 (.reg par) true .cta) =
          .wait (indexWaitObject L g true q.block) (indexWaitParity true q.block) k true .cta := by
      have hb := Wg1Index.AtD.reg ha hm
      have hp := Wg1Index.AtD.reg ha hp
      rw [hbase, hi.phase_block hne] at hb
      rw [hpar, hi.par_block hne] at hp
      simpa [indexWaitObject, indexWaitParity, indexWaitSlot, IndexRing.free, Mbar.loc,
        Mbar.off, Wg1Index.freeOff, ctaOf] using poll_regs_template hpre hb hp
          (by unfold Wg1Index.freeOff; omega) (by unfold Wg1Index.freeOff; omega) (by omega)
    cases extra
    · rw [show q.site.pc = 2446 by rw [hd]; rfl] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_11)
      exact of_regs (by rw [hd]; decide +kernel) (by rw [hd]; decide +kernel) rfl rfl
    · rw [show q.site.pc = 2534 by rw [hd]; rfl] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_12)
      exact of_regs (by rw [hd]; decide +kernel) (by rw [hd]; decide +kernel) rfl rfl

/-- A released lane may take the success branch once the slot phase differs from its parity. -/
theorem index_poll_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Machine.ThreadD} {free : Bool} {block : Nat} {before : State}
    (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hd : IndexWait d free block)
    (hstate : stateBefore (X.objects (indexWaitObject L g free block))
      (X.objects (indexWaitObject L g free block)).length = some before)
    (hready : before.phase % 2 ≠ indexWaitParity free block % 2) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    cases hd
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hr hσ
  obtain ⟨k, htmpl⟩ := index_wait_template hpre hd ha hi hc
  rw [htmpl] at hout
  exact poll_extension hX hp.1 hne hrel hr hτ hout hstate hready

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
