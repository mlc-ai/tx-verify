-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxLoopControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Loop
public import Lemmas.Flow.Footprint

@[expose] public section

/-! # Restore the next actual mask acquire from its loop-control registers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A known local prefix can be removed from a nonempty concrete run. -/
theorem after_softmax_local_prefix {t u : TState} {head : Event} {tail : List Event}
    {o : Option TState} (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u)
    (hRun : Run kernel Assumptions.all L g t (head :: tail) o) :
    Run kernel Assumptions.all L g u (head :: tail) o := by
  have beforeStop {v : TState} (hv : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t v)
      (hs : Stops kernel Assumptions.all L g v) :
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v := by
    rcases rtg_tau_total hLocal hv with h | h
    · exact h
    · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨_, hStep, _⟩
      · exact .refl
      · exact (not_tau_of_stops hs hStep).elim
  cases hRun with
  | step hTau hStep hRest => exact .step (beforeStop hTau (stops_of_estep hStep)) hStep hRest
  | last hTau hStep => exact .last (beforeStop hTau (stops_of_estep hStep)) hStep

private theorem softmax_head_registers : ∀ r ∈ softmaxLoopRegs,
    stableRegisterWindow r 253 256 = true := by
  intro r hr
  exact List.all_eq_true.mp
    (show softmaxLoopRegs.all (fun r => stableRegisterWindow r 253 256) = true by
      decide +kernel) r hr

set_option maxRecDepth 100000 in
private theorem head_local_instructions : (kernel.code.zipIdx.all fun p =>
    !(decide (253 ≤ p.2 ∧ p.2 < 256)) || p.1.op.isLocal) = true := by
  decide +kernel

/-- The opening instructions cannot reach a later block event before their barrier. -/
theorem softmax_opening_event_bound {t : TState} {e : Event} {tail : List Event}
    {o : Option TState} (hPc : t.pc = 253)
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) : e.pc ≤ 256 := by
  have hRegister (v : TState)
      (hv : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t v)
      {out : Option TState} (hf : EStep kernel Assumptions.all L g v e out) :
      e.pc ≤ 256 := by
    have hBound := local_path_in_register_window (softmax_head_registers 2883 (by decide))
      (show inRegisterWindow 253 256 t.pc by rw [hPc]; decide) hv
    rw [estep_source_pc hf]
    exact hBound.2
  cases hRun with
  | step hv hf _ => exact hRegister _ hv hf
  | last hv hf => exact hRegister _ hv hf

/-- A continuing softmax loop opens each block with its warpgroup barrier. -/
theorem head_barrier_tag {t : TState} {e : Event} {tail : List Event}
    {o : Option TState} (hPc : t.pc = 253)
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) (hTail : tail ≠ []) :
    e.pc = 256 := by
  cases hRun with
  | step hTau hStep hRest =>
    obtain ⟨ins, hc, hl, _⟩ := estep_event_source hStep
    have hReach := local_path_in_register_window (softmax_head_registers 2883 (by decide))
      (show inRegisterWindow 253 256 t.pc by rw [hPc]; decide) hTau
    have hSource := estep_source_pc hStep
    rw [← hSource] at hc hReach
    change 253 ≤ e.pc ∧ e.pc ≤ 256 at hReach
    by_contra! hTag
    have hLocal := List.all_eq_true.mp head_local_instructions (ins, e.pc)
      (List.mem_zipIdx_iff_getElem?.mpr hc)
    have hp : 253 ≤ e.pc ∧ e.pc < 256 := ⟨hReach.1, by omega⟩
    simp [hp, hl] at hLocal
  | last => exact (hTail rfl).elim

private theorem after_opening_barrier {t u : TState} {e : Event} (hPc : t.pc = 256)
    (he : EStep kernel Assumptions.all L g t e (some u)) : u = PTX.next t ∧ t.fault = none := by
  have hFault : t.fault = none := by
    obtain ⟨m, ho, hf⟩ := he
    cases h : t.fault
    · rfl
    · simp [out, h] at ho
      subst m
      cases hf.2
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [hPc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_256)
  simp only [eventTmpl, barTmpl] at hf
  repeat' split at hf
  all_goals first | exact ⟨Option.some.inj hf.2, hFault⟩ | cases hf.2

/-- Recover the first event of the next block and resume its actual suffix at the
opening barrier without using accumulated numerical state. -/
theorem softmax_opening_barrier_of_run {block total : Nat} {t : TState}
    {e : Event} {tail : List Event} {o : Option TState}
    (hAt : At t 253 (softmaxLoopFacts block total))
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) (hTail : tail ≠ []) :
    ∃ u, AtVector u 257 (softmaxLoopFacts block total) u.sub u.acc ∧
      Run kernel Assumptions.all L g u tail o := by
  have hTag := head_barrier_tag hAt.1 hRun hTail
  have hRu : Run kernel Assumptions.all L g t ([] ++ e :: tail) o := hRun
  obtain ⟨v, hPc, hRegs, hResume⟩ := resume_register_window_end softmax_head_registers
    (by decide) (by rw [hAt.1]) (by simpa only [hAt.1] using (by decide : 253 ≤ 256))
    hTag (by simp) hRu
  have hStop : Stops kernel Assumptions.all L g v := by
    cases h : v.fault with
    | none => exact ⟨_, out_event h (hPc ▸ Flow.code_256) rfl rfl⟩
    | some f => exact ⟨.ub f, by simp [out, h]⟩
  cases hResume with
  | step hTau he hRest =>
    rw [stop_unique hTau .refl (stops_of_estep he) hStop] at he
    obtain ⟨rfl, hFault⟩ := after_opening_barrier hPc he
    refine ⟨PTX.next v, ⟨by change v.pc + 1 = 257; rw [hPc], rfl, rfl, hFault, ?_⟩, hRest⟩
    apply holds_of_pointwise
    intro r hr
    change v.regs r = _
    rw [hRegs r hr]
    exact holds_mem hAt.2.2.2.2 (mem_factsFrom hr)
  | last => exact (hTail rfl).elim

/-- The next mask acquire's address, parity, and the slot value retained for its release. -/
def softmaxMaskFacts (L : Launch) (block total : Nat) : List (Nat × Value) :=
  (974, b32 (L.sharedBase + (222840 + 8 * (block % 4)))) ::
    (975, b32 (block / 4 % 2)) :: (477, b32 (L.sharedBase + 8 * (block % 4))) ::
    (981, b32 L.sharedBase) :: softmaxLoopFacts block total

private theorem softmax_mask_setup {block total sub : Nat} {acc : List Value} {t : TState}
    (hpre : Pre P L mem0)
    (ht : AtVector t 257 (softmaxLoopFacts block total) sub acc) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      AtVector u 264 (softmaxMaskFacts L block total) sub acc := by
  have hShared := sharedBase_lt hpre
  have hRun : ∃ u, run kernel Assumptions.all L g 7 t = some u ∧
      AtVector u 264 (softmaxMaskFacts L block total) sub acc := by
    seg_fp ht using
      (try unfold b32)
      (try norm_bits [Wg0.land255, Nat.add_zero, Nat.add_assoc])
  obtain ⟨u, hu, hAt⟩ := hRun
  exact ⟨u, run_rtg hu, hAt⟩

/-- Resume the next actual mask acquire after a non-final probability publication.
Only the block, total length, and the recorded suffix determine its address and parity. -/
theorem softmax_next_mask_after_publication {t : TState} {publish opening poll : Event}
    {tail : List Event} {o : Option TState} {block total : Nat}
    (hpre : Pre P L mem0) (hMore : block + 1 < total) (hLimit : total < 2 ^ 31)
    (hPc : t.pc = Wg0.Site.soReady.pc) (hFacts : Holds t.regs (softmaxLoopFacts block total))
    (hRun : Run kernel Assumptions.all L g t (publish :: opening :: poll :: tail) o) :
    ∃ u, AtVector u 264 (softmaxMaskFacts L (block + 1) total) u.sub u.acc ∧
      Run kernel Assumptions.all L g u (poll :: tail) o := by
  obtain ⟨head, hLocal, hAt, hRest⟩ :=
    softmax_next_head_after_publication hMore hLimit hPc hFacts hRun (by simp)
  obtain ⟨v, hv, hAfter⟩ :=
    softmax_opening_barrier_of_run hAt (after_softmax_local_prefix hLocal hRest) (by simp)
  obtain ⟨u, hu, hMask⟩ := softmax_mask_setup hpre hv
  exact ⟨u, ⟨hMask.1, rfl, rfl, hMask.2.2.2.1, hMask.2.2.2.2⟩, after_softmax_local_prefix hu hAfter⟩

/-- The concrete mask-acquire template at the recovered loop entry. -/
theorem mask_poll_template {t : TState} {block total : Nat}
    (hpre : Pre P L mem0)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc) :
    out kernel Assumptions.all L g t =
      .ev (.wait ⟨.shared, ctaOf L g, L.sharedBase + (222840 + 8 * (block % 4))⟩
        (block / 4 % 2) (fun ok => PTX.next (setReg t 4075 (.pred ok))) true .cta) := by
  have hAddr : t.regs 974 = some (b32 (L.sharedBase + (222840 + 8 * (block % 4)))) :=
    hAt.2.2.2.2.1
  have hParity : t.regs 975 = some (b32 (block / 4 % 2)) := hAt.2.2.2.2.2.1
  have hSlot : block % 4 < 4 := Nat.mod_lt _ (by decide)
  have hBound : block / 4 % 2 < 2 ^ 32 := by omega
  have hm := mbarLoc_b32 (L := L) (g := g) (base := 974) hAddr
    (Wg0.maskAddr_lt hpre hSlot) (Wg0.maskAddr_mod8 hpre (block % 4))
  have hp := readBits_b32 (L := L) (g := g) hParity hBound
  rw [out_event hAt.2.2.2.1 (hAt.1 ▸ Flow.code_264) rfl rfl]
  have hScope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hScope, Bool.false_eq_true, ↓reduceIte, tmaTmpl,
    hm, hp, pure, Except.pure, bind, Except.bind, ofExec]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : block / 4 % 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : block / 4 % 2 < 2)]
  rfl

/-- A false mask poll restarts with the same address and loop registers. -/
theorem retry_mask_poll {t : TState} {block total : Nat}
    (ht : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
        (PTX.next (setReg t 4075 (.pred false))) u ∧
      AtVector u 264 (softmaxMaskFacts L block total) u.sub u.acc := by
  let v := PTX.next (setReg t 4075 (.pred false))
  let w := skip v
  let u := { w with pc := 264 }
  have hv : v.pc = 265 := by change t.pc + 1 = 265; rw [ht.1]
  have hw : w.pc = 266 := by change v.pc + 1 = 266; rw [hv]
  have hPred : v.regs 4075 = some (.pred false) := by simp [v, PTX.next, setReg]
  have hFault : v.fault = none := ht.2.2.2.1
  have hSkip : Tau kernel Assumptions.all L g v w := by
    simp [Tau, out, hFault, hv, Flow.code_265, guardHolds, readReg, hPred,
      pure, Except.pure, bind, Except.bind, w]
  have hNoLocal := Thread.asms_localRule_bra (L := L) (g := g) (t := w)
    (target := 264) (uni := false) (by rw [hw]; decide) (by rw [hw]; decide)
  have hBranch : Tau kernel Assumptions.all L g w u := by
    have hwFault : w.fault = none := hFault
    simp [Tau, out, hwFault, hw, Flow.code_266, guardHolds, pure, Except.pure,
      execLocalA_noSegment (Proof.asms_segment_free w), execLocalRule_of_none hNoLocal,
      execLocal, Op.rule, execBranch, Op.isLocal, u]
  refine ⟨u, (Relation.ReflTransGen.single hSkip).tail hBranch, ⟨rfl, rfl, rfl, hFault, ?_⟩⟩
  apply holds_update ht.2.2.2.2
  intro p hp
  simp [softmaxMaskFacts, softmaxLoopFacts, softmaxLoopRegs, factsFrom] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

/-- Any continuing softmax mask poll uses the actual block's ring slot and acquire parity. -/
theorem softmax_mask_poll_from_run {t : TState} {block total : Nat}
    {e : Event} {tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) (hTail : tail ≠ []) :
    ∃ ok, e =
        ⟨264, .wait ⟨.shared, ctaOf L g, L.sharedBase + (222840 + 8 * (block % 4))⟩
          (block / 4 % 2) ok true .cta⟩ ∧
      Run kernel Assumptions.all L g (PTX.next (setReg t 4075 (.pred ok))) tail o := by
  have hOut := mask_poll_template (g := g) hpre hAt
  cases hRun with
  | step hTau hStep hRest =>
    rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
    obtain ⟨m, hm, hf⟩ := hStep
    rw [hOut] at hm
    cases hm
    rw [hAt.1] at hf
    obtain ⟨ok, he, hState⟩ := hf
    obtain rfl := Option.some.inj hState
    exact ⟨ok, he, hRest⟩
  | last => exact (hTail rfl).elim

/-- An actual later event at the mask-return site has passed a successful mask acquire
of the current block, with any earlier failures retaining the same slot and parity. -/
theorem successful_softmax_mask_poll_before_return {t : TState} {block total i : Nat}
    {e : Event} {events : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hRun : Run kernel Assumptions.all L g t events o)
    (he : events[i]? = some e) (hTag : e.pc = Wg0.Site.validFree.pc) :
    ∃ j < i, events[j]? = some
      ⟨264, .wait ⟨.shared, ctaOf L g, L.sharedBase + (222840 + 8 * (block % 4))⟩
        (block / 4 % 2) true true .cta⟩ := by
  induction events generalizing t i with
  | nil => cases he
  | cons front tail ih =>
    cases i with
    | zero =>
      have hFirst : front = e := Option.some.inj he
      subst front
      cases hRun with
      | step hTau hStep _ =>
        have hOut := mask_poll_template (g := g) hpre hAt
        rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
        have h := estep_source_pc hStep
        rw [hTag, hAt.1] at h
        cases h
      | last hTau hStep =>
        have hOut := mask_poll_template (g := g) hpre hAt
        rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
        have h := estep_source_pc hStep
        rw [hTag, hAt.1] at h
        cases h
    | succ i =>
      have he' : tail[i]? = some e := he
      have hTail := List.ne_nil_of_mem (List.mem_of_getElem? he')
      obtain ⟨ok, hFront, hRest⟩ := softmax_mask_poll_from_run hpre hAt hRun hTail
      cases ok with
      | true => exact ⟨0, Nat.zero_lt_succ i, congrArg some hFront⟩
      | false =>
        obtain ⟨u, hLocal, huAt⟩ := retry_mask_poll hAt
        obtain ⟨next, after, rfl⟩ := List.exists_cons_of_ne_nil hTail
        obtain ⟨j, hj, hr⟩ := ih huAt (after_softmax_local_prefix hLocal hRest) he'
        exact ⟨j + 1, Nat.succ_lt_succ hj, hr⟩

private def softmaxEpilogueRegion (pc : Nat) : Prop := 1147 ≤ pc

private instance (pc : Nat) : Decidable (softmaxEpilogueRegion pc) :=
  inferInstanceAs (Decidable (1147 ≤ pc))

set_option maxRecDepth 100000 in
private theorem softmax_epilogue_closed : controlRegionClosed softmaxEpilogueRegion = true := by
  decide +kernel

variable {t : TState} {e picked : Event} {tail : List Event} {o : Option TState} {block : Nat}
    (hLimit : block + 1 < 2 ^ 31) (hpc : t.pc = Wg0.Site.soReady.pc)
    (hFacts : Holds t.regs (softmaxLoopFacts block (block + 1)))
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o)
include hLimit hpc hFacts hRun

/-- A recorded final probability publication can only be followed by epilogue events. -/
theorem event_after_final_publication_lower (hPicked : picked ∈ tail) : 1147 ≤ picked.pc := by
  have hTail := List.ne_nil_of_mem hPicked
  obtain ⟨u, hu, hEpilogue, hRest⟩ :=
    softmax_final_head_after_publication hLimit hpc hFacts hRun hTail
  obtain ⟨next, events, rfl⟩ := List.exists_cons_of_ne_nil hTail
  have hBound := run_in_control_region softmax_epilogue_closed
    (show softmaxEpilogueRegion u.pc by rw [hEpilogue]; exact le_rfl)
    (after_softmax_local_prefix hu hRest) picked hPicked
  exact hBound

/-- A recorded final probability publication cannot be followed by another mask release. -/
theorem no_mask_return_after_final_publication (hPicked : picked ∈ tail)
    (hTag : picked.pc = Wg0.Site.validFree.pc) : False := by
  have h := event_after_final_publication_lower hLimit hpc hFacts hRun hPicked
  rw [hTag] at h
  exact (by decide : ¬ 1147 ≤ Wg0.Site.validFree.pc) h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
