-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturn
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Loop
import Lemmas.Flow.Footprint

@[expose] public section

/-! # The softmax loop counters do not depend on score or mask data -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The registers changed by the softmax ring advance. -/
def softmaxLoopRegs : List Nat := [2883, 2884, 2952, 2953, 451, 452]

/-- Loop length, current ordinal, both slot indices and both parities. -/
def softmaxLoopWord (block total : Nat) (r : Nat) : Value :=
  match r with
  | 2883 => b32 (block + 1)
  | 2884 => b32 ((block + 1 + (2 ^ 32 - total)) % 2 ^ 32)
  | 2952 => b32 (block % 4)
  | 2953 => b32 (block % 2)
  | 451 => .bits 16 (BitVec.ofNat 64 (block / 4 % 2))
  | 452 => .bits 16 (BitVec.ofNat 64 (block / 2 % 2))
  | _ => b32 0

/-- Control facts at the start and end of a softmax block. -/
def softmaxLoopFacts (block total : Nat) : List (Nat × Value) :=
  factsFrom softmaxLoopRegs (softmaxLoopWord block total)

set_option maxRecDepth 100000 in
private theorem softmax_loop_windows : ∀ r ∈ softmaxLoopRegs,
    stableRegisterWindow r 256 1122 = true := by
  intro r hr
  exact List.all_eq_true.mp
    (show softmaxLoopRegs.all (fun r => stableRegisterWindow r 256 1122) = true by
      decide +kernel) r hr

/-- At the probability publication, the replay has retained the block's loop
counters, regardless of all intermediate memory and Tensor Memory values. -/
theorem softmax_loop_facts_at_publication {t : TState} {e : Event} {o : Option TState}
    {before tail : List Event} {block total : Nat}
    (hFirst : 256 ≤ t.pc) (hLast : t.pc ≤ 1122)
    (hFacts : Holds t.regs (softmaxLoopFacts block total))
    (hTag : e.pc = Wg0.Site.soReady.pc) (hPrev : ∀ f ∈ before, f.pc ≠ Wg0.Site.soReady.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ u, u.pc = Wg0.Site.soReady.pc ∧ Holds u.regs (softmaxLoopFacts block total) ∧
      Run kernel Assumptions.all L g u (e :: tail) o := by
  obtain ⟨u, hPc, hRegs, hBody⟩ :=
    resume_register_window_end softmax_loop_windows (by decide) hFirst hLast hTag hPrev hRun
  refine ⟨u, hPc, ?_, hBody⟩
  apply holds_of_pointwise
  intro r hr
  rw [hRegs r hr]
  exact holds_mem hFacts (mem_factsFrom hr)

private def afterTwoSlot (block total : Nat) (r : Nat) : Value :=
  if r ∈ ([452, 2953] : List Nat) then softmaxLoopWord (block + 1) total r
  else softmaxLoopWord block total r

private def afterRingSlots (block total : Nat) (r : Nat) : Value :=
  if r ∈ ([2883, 2884] : List Nat) then softmaxLoopWord block total r
  else softmaxLoopWord (block + 1) total r

private theorem softmax_two_slot_step {block total : Nat} {t : TState}
    (hAt : At t 1125 (softmaxLoopFacts block total)) :
    ∃ u, run kernel Assumptions.all L g 7 t = some u ∧
      At u 1132 (factsFrom softmaxLoopRegs (afterTwoSlot block total)) := by
  have hPrefix : ∃ u, run kernel Assumptions.all L g 5 t = some u ∧ At u 1130
      ((1718, .bits 32 (truncBits 32 (~~~(truncBits 32 (BitVec.ofNat 64 (block % 2)))))) ::
        (114, .pred (decide ((block + 1) / 2 % 2 = 1))) :: softmaxLoopFacts block total) := by
    seg_fp hAt using norm_signed [Wg0.land255, Wg0.phase2_succ]
  obtain ⟨a, ha, haAt⟩ := hPrefix
  have hSlot : (block + 1) % 2 = 1 - block % 2 := by omega
  have hFlip : Value.bits 32 ((truncBits 32 (truncBits 32
      (~~~(truncBits 32 (BitVec.ofNat 64 (block % 2)))))) &&&
      truncBits 32 (BitVec.ofInt 64 1)) = b32 (1 - block % 2) := by
    have hBits : block % 2 = 0 ∨ block % 2 = 1 := by omega
    rcases hBits with h | h <;> rw [h] <;> rfl
  have tail : ∃ u, run kernel Assumptions.all L g 2 a = some u ∧
      At u 1132 (factsFrom softmaxLoopRegs (afterTwoSlot block total)) := by
    by_cases hp : (block + 1) / 2 % 2 = 1 <;>
      simp only [hp, decide_true, decide_false] at haAt <;> seg_fp haAt using
        first
        | (change _ = b32 ((block + 1) % 2); rw [hSlot]; exact hFlip)
        | (have hPhase : (block + 1) / 2 % 2 = 1 ∨ (block + 1) / 2 % 2 = 0 := by omega
           change _ = Value.bits 16 (BitVec.ofNat 64 ((block + 1) / 2 % 2))
           simp_all only [or_false, false_or, Nat.one_ne_zero]; rfl)
  obtain ⟨u, hu, huAt⟩ := tail
  exact ⟨u, run_comp ha hu, huAt⟩

private theorem softmax_four_slot_step {block total : Nat} {t : TState}
    (hAt : At t 1132 (factsFrom softmaxLoopRegs (afterTwoSlot block total))) :
    ∃ u, run kernel Assumptions.all L g 11 t = some u ∧
      At u 1143 (factsFrom softmaxLoopRegs (afterRingSlots block total)) := by
  have pick : ∃ u, run kernel Assumptions.all L g 1 t = some u ∧
      At u 1133 ((115, .pred (decide (block % 4 = 3))) ::
        factsFrom softmaxLoopRegs (afterTwoSlot block total)) := by
    have hSlot : block % 4 < 4 := Nat.mod_lt _ (by decide)
    seg_fp hAt using norm_signed [afterRingSlots, softmaxLoopWord, b32]
  obtain ⟨a, ha, haAt⟩ := pick
  have phase : ∃ u, run kernel Assumptions.all L g 3 a = some u ∧
      At u 1136 ((116, .pred (decide ((block + 1) / 4 % 2 = 1))) ::
        factsFrom softmaxLoopRegs (afterTwoSlot block total)) := by
    by_cases hWrap : block % 4 = 3 <;>
      simp only [hWrap, decide_true, decide_false] at haAt <;>
      seg_fp haAt using norm_signed [Wg0.land255, Wg0.phase4_succ, hWrap]
  obtain ⟨b, hb, hbAt⟩ := phase
  have tail : ∃ u, run kernel Assumptions.all L g 7 b = some u ∧
      At u 1143 (factsFrom softmaxLoopRegs (afterRingSlots block total)) := by
    have hs : block % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hp : (block + 1) / 4 % 2 = 1 <;>
      simp only [hp, decide_true, decide_false] at hbAt <;> seg_fp hbAt using
        first
        | (change _ = b32 ((block + 1) % 4); norm_signed [])
        | (have hPhase : (block + 1) / 4 % 2 = 1 ∨ (block + 1) / 4 % 2 = 0 := by omega
           change _ = Value.bits 16 (BitVec.ofNat 64 ((block + 1) / 4 % 2))
           simp_all only [or_false, false_or, Nat.one_ne_zero]; rfl)
  obtain ⟨u, hu, huAt⟩ := tail
  exact ⟨u, run_comp (run_comp ha hb) hu, huAt⟩

private theorem softmax_counter_step {block total : Nat} {t : TState}
    (hLive : block + 1 < total) (hLimit : total < 2 ^ 31)
    (hAt : At t 1143 (factsFrom softmaxLoopRegs (afterRingSlots block total))) :
    ∃ u, run kernel Assumptions.all L g 3 t = some u ∧
      At u 1146 ((117, .pred true) :: softmaxLoopFacts (block + 1) total) := by
  seg_fp hAt using norm_signed [afterRingSlots, softmaxLoopWord, b32]

/-- The concrete loop back-edge advances the ring and block counters using just their
retained register words. -/
theorem softmax_control_advance {block total : Nat} {t : TState}
    (hLive : block + 1 < total) (hLimit : total < 2 ^ 31)
    (hAt : At t 1125 (softmaxLoopFacts block total)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      At u 253 (softmaxLoopFacts (block + 1) total) := by
  obtain ⟨a, ha, haAt⟩ := softmax_two_slot_step (L := L) (g := g) hAt
  obtain ⟨b, hb, hbAt⟩ := softmax_four_slot_step (L := L) (g := g) haAt
  obtain ⟨c, hc, hcAt⟩ := softmax_counter_step (L := L) (g := g) hLive hLimit hbAt
  obtain ⟨u, hu, huAt⟩ := run_bra (K := kernel) (A := Assumptions.all) (L := L) (g := g)
    Flow.code_1146 true hcAt hcAt.2.2.2.2.1
    (Thread.asms_localRule_bra (by rw [hcAt.1]; decide) (by rw [hcAt.1]; decide))
  exact ⟨u, (run_rtg ha).trans ((run_rtg hb).trans ((run_rtg hc).trans (run_rtg hu))),
    huAt.mono huAt.2.2.2.2.2⟩

/-- A unit arrival with no result register continues at the following instruction. -/
theorem softmax_unit_arrival_return {t u : TState} {e : Event} {base : Nat}
    (hCode : kernel.code[t.pc]? = some
      ⟨none, .mbarArrive base 0 (.imm 0) (.imm 1) false true .cta none⟩)
    (he : EStep kernel Assumptions.all L g t e (some u)) :
    u = PTX.next t ∧ t.fault = none := by
  have hfault : t.fault = none := by
    obtain ⟨m, hOut, hf⟩ := he
    cases h : t.fault
    · rfl
    · simp [out, h] at hOut
      subst m
      cases hf.2
  obtain ⟨ins, hc, _, hf⟩ := PTX.EventFrame.estep_event_source he
  obtain rfl := Option.some.inj (hc.symm.trans hCode)
  simp only at hf
  cases hm : mbarLoc L g t base 0 with
  | error f =>
    have hf' : Fires t.pc (.ub f) e (some u) := by
      simpa only [eventTmpl, tmaTmpl, widenMbarScope,
        show Assumptions.all.any (·.clusterScopeMbar t.pc) = false from rfl,
        Bool.false_eq_true, ↓reduceIte, hm, bind, Except.bind, ofExec] using hf
    cases hf'.2
  | ok m =>
    have hm' : (if false then mbarClusterLoc L g t base 0 else mbarLoc L g t base 0) = .ok m := hm
    obtain ⟨_, _, _, hu⟩ := fires_arrive_next hm' (by rfl) (by rfl) hf
    exact ⟨Option.some.inj hu, hfault⟩

variable {t : TState} {e : Event} {tail : List Event} {o : Option TState}

/-- Consume the actual probability publication when the recorded execution continues. -/
theorem softmax_run_after_publication (hpc : t.pc = Wg0.Site.soReady.pc)
    (hr : Run kernel Assumptions.all L g t (e :: tail) o) (hTail : tail ≠ []) :
    t.fault = none ∧ Run kernel Assumptions.all L g (PTX.next t) tail o := by
  have hCode := Flow.code_1122
  have hpc' : t.pc = 1122 := hpc
  rw [← hpc'] at hCode
  have hStop : Stops kernel Assumptions.all L g t := by
    cases h : t.fault with
    | some f => exact ⟨.ub f, by simp [out, h]⟩
    | none => exact ⟨_, out_event h hCode rfl rfl⟩
  cases hr with
  | step hTau hStep hRest =>
    rw [stop_unique hTau .refl (stops_of_estep hStep) hStop] at hStep
    obtain ⟨rfl, hFault⟩ := softmax_unit_arrival_return hCode hStep
    exact ⟨hFault, hRest⟩
  | last => exact (hTail rfl).elim

private theorem softmax_final_test {block total : Nat} {t : TState}
    (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 1123 (softmaxLoopFacts block total) t.sub t.acc) :
    ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
      AtVector v 1124 ((113, .pred (decide (block + 1 = total))) ::
        softmaxLoopFacts block total) t.sub t.acc := by
  seg_fp hAt using
    (simp only [Value.pred.injEq, Option.getD_some]
     exact Wg0.last_block_compare hBlock hLimit)

private theorem softmax_skips_final_branch {block total : Nat} {t : TState}
    (hMore : block + 1 < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 1123 (softmaxLoopFacts block total) t.sub t.acc) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      At u 1125 (softmaxLoopFacts block total) := by
  have hTest := softmax_final_test (L := L) (g := g) (by omega) hLimit hAt
  simp only [show block + 1 ≠ total by omega, decide_false] at hTest
  obtain ⟨v, hv, hvAt⟩ := hTest
  have hStep : Tau kernel Assumptions.all L g v (skip v) := by
    unfold Tau
    simp [out, hvAt.1, hvAt.2.2.2.1, Flow.code_1124, guardHolds, readReg,
      hvAt.2.2.2.2.1, bind, Except.bind, pure, Except.pure]
  refine ⟨skip v, (run_rtg hv).trans (.single hStep), ?_⟩
  exact ⟨by change v.pc + 1 = 1125; rw [hvAt.1], rfl, rfl, hvAt.2.2.2.1, hvAt.2.2.2.2.2⟩

/-- Returning from the probability publication of a non-final block reaches a new
loop head with its incremented, concrete slot and parity registers. -/
theorem softmax_next_head_after_publication {block total : Nat} (hMore : block + 1 < total)
    (hLimit : total < 2 ^ 31) (hpc : t.pc = Wg0.Site.soReady.pc)
    (hFacts : Holds t.regs (softmaxLoopFacts block total))
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) (hTail : tail ≠ []) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) (PTX.next t) u ∧
      At u 253 (softmaxLoopFacts (block + 1) total) ∧
      Run kernel Assumptions.all L g (PTX.next t) tail o := by
  obtain ⟨hFault, hRun'⟩ := softmax_run_after_publication hpc hRun hTail
  have hpc' : (PTX.next t).pc = 1123 := by change t.pc + 1 = 1123; rw [hpc]; rfl
  have hAt : AtVector (PTX.next t) 1123 (softmaxLoopFacts block total)
      (PTX.next t).sub (PTX.next t).acc :=
    ⟨hpc', rfl, rfl, hFault, hFacts⟩
  obtain ⟨v, hv, hvAt⟩ := softmax_skips_final_branch (L := L) (g := g) hMore hLimit hAt
  obtain ⟨u, hu, huAt⟩ := softmax_control_advance (L := L) (g := g) hMore hLimit hvAt
  exact ⟨u, hv.trans hu, huAt, hRun'⟩

private theorem softmax_last_counter {block : Nat} {t : TState}
    (hLimit : block + 1 < 2 ^ 31)
    (hAt : AtVector t 1143 (softmaxLoopFacts block (block + 1)) t.sub t.acc) :
    ∃ u, run kernel Assumptions.all L g 3 t = some u ∧
      AtVector u 1146 [(117, .pred false), (2953, b32 (block % 2)),
        (452, .bits 16 (BitVec.ofNat 64 (block / 2 % 2)))] t.sub t.acc := by
  seg_fp hAt using norm_signed [softmaxLoopWord, b32]

/-- The last probability publication leads through the final block test to the epilogue. -/
theorem softmax_final_slot_after_publication {block : Nat} (hLimit : block + 1 < 2 ^ 31)
    (hpc : t.pc = Wg0.Site.soReady.pc) (hFacts : Holds t.regs (softmaxLoopFacts block (block + 1)))
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) (hTail : tail ≠ []) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) (PTX.next t) u ∧
      u.pc = 1147 ∧ u.regs 2953 = some (b32 (block % 2)) ∧
      u.regs 452 = some (.bits 16 (BitVec.ofNat 64 (block / 2 % 2))) ∧
      Run kernel Assumptions.all L g (PTX.next t) tail o := by
  obtain ⟨hFault, hRun'⟩ := softmax_run_after_publication hpc hRun hTail
  have hpc' : (PTX.next t).pc = 1123 := by change t.pc + 1 = 1123; rw [hpc]; rfl
  have hAt : AtVector (PTX.next t) 1123 (softmaxLoopFacts block (block + 1))
      (PTX.next t).sub (PTX.next t).acc := ⟨hpc', rfl, rfl, hFault, hFacts⟩
  obtain ⟨v, hv, hvAt⟩ :=
    softmax_final_test (L := L) (g := g) (Nat.lt_succ_self block) hLimit hAt
  have hPred : v.regs 113 = some (.pred true) := by simpa using hvAt.2.2.2.2.1
  let w := { v with pc := 1143 }
  have hRules := Thread.asms_localRule_bra (L := L) (g := g) (t := v)
    (target := 1143) (uni := false) (by rw [hvAt.1]; decide) (by rw [hvAt.1]; decide)
  have hBranch : Tau kernel Assumptions.all L g v w := by
    simp [Tau, out, hvAt.1, hvAt.2.2.2.1, Flow.code_1124, guardHolds, readReg, hPred,
      bind, Except.bind, pure, Except.pure, execLocalA_noSegment (Proof.asms_segment_free v),
      execLocalRule_of_none hRules, execLocal, Op.rule, execBranch, Op.isLocal, w]
  have hwAt : AtVector w 1143 (softmaxLoopFacts block (block + 1)) w.sub w.acc :=
    ⟨rfl, rfl, rfl, hvAt.2.2.2.1, hvAt.2.2.2.2.2⟩
  obtain ⟨z, hz, hzAt⟩ := softmax_last_counter (L := L) (g := g) hLimit hwAt
  have hStop : Tau kernel Assumptions.all L g z (skip z) := by
    simp [Tau, out, hzAt.1, hzAt.2.2.2.1, Flow.code_1146, guardHolds, readReg,
      hzAt.2.2.2.2.1, bind, Except.bind, pure, Except.pure]
  refine ⟨skip z, (run_rtg hv).trans
    ((Relation.ReflTransGen.single hBranch).trans ((run_rtg hz).tail hStop)),
    ?_, hzAt.2.2.2.2.2.1, hzAt.2.2.2.2.2.2.1, hRun'⟩
  change z.pc + 1 = 1147
  rw [hzAt.1]

/-- The last probability publication leads through the final block test to the epilogue. -/
theorem softmax_final_head_after_publication {block : Nat} (hLimit : block + 1 < 2 ^ 31)
    (hpc : t.pc = Wg0.Site.soReady.pc) (hFacts : Holds t.regs (softmaxLoopFacts block (block + 1)))
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) (hTail : tail ≠ []) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) (PTX.next t) u ∧
      u.pc = 1147 ∧ Run kernel Assumptions.all L g (PTX.next t) tail o := by
  obtain ⟨u, hu, hHead, _, _, hTail⟩ :=
    softmax_final_slot_after_publication hLimit hpc hFacts hRun hTail
  exact ⟨u, hu, hHead, hTail⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
