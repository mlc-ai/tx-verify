-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAStepsA
public import Kernels.InklingRelDecode.Proof.Thread.ProAStepsB
public import Kernels.InklingRelDecode.Proof.Thread.ProAStepsQ
public import Kernels.InklingRelDecode.Proof.Thread.ProAStepsS

@[expose] public section

/-! # The prologue's obligations as a code machine

Every state of `code` (`ProASiteTac`) satisfies its step obligation (`stepAt`, from the four site
files, checked in parallel), and the machine stops at a fired event only for the reason `Stop`
(`stops`: a received word without bits, or a base word without an outcome). `entry` turns the
registers at pc 20 (just after the common code's branch) into the first state, and `handoff`
states the facts at the first instruction of the softmax region (pc 574) after the last event. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- **The steps.** Every state of the region satisfies its obligation. -/
theorem stepAt (P : Inh) (d : D) : (code L g P).StepAt d := by
  by_cases h1 : d.site.pc < 180
  · exact stepAt_setup P d h1
  by_cases h2 : d.site.pc < 320
  · exact stepAt_pre P d ⟨by omega, h2⟩
  by_cases h3 : d.site.pc < 520
  · exact stepAt_ldq P d ⟨by omega, h3⟩
  · exact stepAt_stq P d (by omega)

/-- Each site is an event instruction whose guard holds by its facts. -/
theorem site_ok (hi : Inv L g d) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard :=
  (stepAt (L := L) (g := g) d.dt.pro d).site hi

/-- **Why the machine stops.** At a fired event the successor is `none` only at the election
after a broadcast whose received word has no bits, or on a base word without an outcome. -/
theorem stops (P : Inh) (d : D) : (code L g P).StopsFor (Stop L g) d := by
  obtain ⟨s, dt⟩ := d
  stops_cases s trans [next, Stop] stop_by (first
    | (left; exact ⟨0, by decide, rfl, by assumption⟩)
    | (left; exact ⟨1, by decide, rfl, by assumption⟩)
    | (left; exact ⟨2, by decide, rfl, by assumption⟩)
    | (right; simp_all [elDt]; done)
    | (right; tauto))

/-- The first state satisfies the invariant when the registers satisfy `ArgsOk`. -/
theorem inv_start {P : Inh} {w : Value} (ha : ArgsOk L g P) : Inv L g (D.start P w) :=
  ⟨ha, rfl, fun _ _ => rfl, fun _ => rfl⟩

/-! ### The entry -/

/-- **The entry.** From the registers live at pc 20 (just after the branch of the common code),
valued as the first state's table values them (the inherited registers of `P`), the seven
`ld.param` of pc 20 to 26 reach `setmaxnreg.inc` with the facts of the first state. The
parameters are those `ArgsOk` names. -/
theorem entry (P : Inh) {w : Value} (ha : ArgsOk L g P) {t : TState}
    (h : At t 20 (factsAt L g 20 (Dat.start P w))) :
    ∃ t', run kernel asms L g 7 t = some t' ∧
      At t' Flow.setMaxReg_0 (facts L g (D.start P w)) := by
  obtain ⟨t', hr, ht⟩ := Seg.comp (seg_20_21 L g (Dat.start P w) ha.p17)
    (Seg.comp (seg_21_22 L g (Dat.start P w) ha.p16)
    (Seg.comp (seg_22_23 L g (Dat.start P w) ha.p15)
    (Seg.comp (seg_23_24 L g (Dat.start P w) ha.p9) (Seg.comp (seg_24_25 L g (Dat.start P w) ha.p8)
    (Seg.comp (seg_25_26 L g (Dat.start P w) ha.p6) (seg_26_27 L g (Dat.start P w) ha.p0)))))) t h
  exact ⟨t', hr, ht⟩

/-! ### The hand-off -/

/-- The facts at the first instruction of the softmax region (pc 574, `setmaxnreg.inc`), after the
last event of this region: the registers live there, valued by the table of the data the thread
holds at its last site. The registers are those of `exitRegs`; `ProAExit` states what the
ones the softmax region uses mean (`q_len`, `past`, `num_iters`, the barrier addresses, …). -/
def exitFacts (L : Launch) (g : Nat) (dt : Dat) : List (Nat × Value) :=
  factsAt L g Flow.setMaxReg_1 dt

/-- **The hand-off.** After the event of `barrier.sync 1` (pc 573) the thread is at pc 574 with
`exitFacts` of its data. -/
theorem handoff {dt : Dat} (h : AtS L g ⟨.bar18, dt⟩ t)
    (hc : kernel.code[Flow.bar_18]? = some ins)
    (hf : Fires Flow.bar_18 (eventTmpl asms L g t ins.op) e (some u)) :
    At u Flow.setMaxReg_1 (exitFacts L g dt) := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_18)
  obtain rfl := fires_async_next (by exact trivial) hf
  exact at_next_live (h.at rfl rfl) (by table_decide)

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
