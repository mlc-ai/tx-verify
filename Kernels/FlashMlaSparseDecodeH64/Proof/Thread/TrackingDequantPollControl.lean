-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantLoopControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxMaskControl

@[expose] public section

/-! # The actual raw poll and its two local continuations -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem raw_poll_template {t : TState} {block : Nat}
    (hpre : Pre P L mem0) (hAt : AtVector t 2677 (dequantPollFacts L g block) t.sub t.acc) :
    out kernel Assumptions.all L g t =
      .ev (.wait ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff (block % 2)⟩
        (block / 2 % 2) (fun ok => PTX.next (setReg t 4125 (.pred ok))) true .cta) := by
  have hAddr : t.regs 2458 = some (b32 (L.sharedBase + Wg2.rawReadyOff (block % 2))) :=
    hAt.2.2.2.2.1
  have hParity : t.regs 2459 = some (b32 (block / 2 % 2)) := hAt.2.2.2.2.2.1
  have hSlot := Nat.mod_lt block (by decide : 0 < 2)
  have hBound : L.sharedBase + Wg2.rawReadyOff (block % 2) < 2 ^ 32 := by
    have hShared := sharedBase_lt hpre
    unfold Wg2.rawReadyOff
    omega
  have hm := mbarLoc_b32 (L := L) (g := g) (base := 2458) hAddr hBound
    (Wg2.sharedAddr_align hpre (by unfold Wg2.rawReadyOff; omega))
  have hp := readBits_b32 (L := L) (g := g) hParity (by omega)
  rw [out_event hAt.2.2.2.1 (hAt.1 ▸ Flow.code_2677) rfl rfl]
  have hScope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hScope, Bool.false_eq_true, ↓reduceIte, tmaTmpl,
    hm, hp, bind, Except.bind, pure, Except.pure, ofExec]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : block / 2 % 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : block / 2 % 2 < 2)]
  rfl

-- Both branches preserve every retained register by reduction.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem raw_poll_return {t : TState} {block : Nat} {ok : Bool}
    (hAt : AtVector t 2678 ((4125, .pred ok) :: dequantPollFacts L g block) t.sub t.acc) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      AtVector u (if ok then 2680 else 2677) (dequantPollFacts L g block) u.sub u.acc := by
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hRun :
        ∃ v, run kernel Assumptions.all L g 2 t = some v ∧
          AtVector v 2677 (dequantPollFacts L g block) 0 [] := by
      simp only [dequantPollFacts, dequantHeadFacts, List.cons_append, List.nil_append] at hAt ⊢
      seg_fp hAt using skip
    obtain ⟨u, hu, hFacts⟩ := hRun
    exact ⟨u, run_rtg hu, hFacts.1, rfl, rfl, hFacts.2.2.2.1, hFacts.2.2.2.2⟩
  · simp only [↓reduceIte]
    have hRun :
        ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
          AtVector v 2680 (dequantPollFacts L g block) t.sub t.acc := by
      simp only [dequantPollFacts, dequantHeadFacts, List.cons_append, List.nil_append] at hAt ⊢
      seg_fp hAt using skip
    obtain ⟨u, hu, hFacts⟩ := hRun
    exact ⟨u, run_rtg hu, hFacts.1, rfl, rfl, hFacts.2.2.2.1, hFacts.2.2.2.2⟩

/-- The concrete raw wait either repeats the same phase or enters the current block's body. -/
theorem dequant_raw_poll_of_run {t : TState} {block : Nat} {e : Event}
    {tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 2677 (dequantPollFacts L g block) t.sub t.acc)
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) :
    ∃ ok, e = ⟨2677, .wait ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff (block % 2)⟩
        (block / 2 % 2) ok true .cta⟩ ∧
      (tail ≠ [] → ∃ u,
        AtVector u (if ok then 2680 else 2677) (dequantPollFacts L g block) u.sub u.acc ∧
        Run kernel Assumptions.all L g u tail o) := by
  have hOut := raw_poll_template hpre hAt
  have hStop : Stops kernel Assumptions.all L g t := ⟨_, hOut⟩
  cases hRun with
  | step hTau hStep hRest =>
    rw [stop_unique hTau .refl (stops_of_estep hStep) hStop] at hStep
    obtain ⟨m, hEvent, hFire⟩ := hStep
    rw [hOut] at hEvent
    obtain rfl := Out.ev.inj hEvent.symm
    obtain ⟨ok, he, hRet⟩ := hFire
    have hTag : t.pc = 2677 := hAt.1
    rw [hTag] at he
    refine ⟨ok, he, ?_⟩
    intro hTail
    obtain rfl := Option.some.inj hRet
    have hStart : AtVector (PTX.next (setReg t 4125 (.pred ok))) 2678
        ((4125, .pred ok) :: dequantPollFacts L g block) t.sub t.acc := by
      refine ⟨by change t.pc + 1 = 2678; rw [hTag], rfl, rfl, hAt.2.2.2.1, rfl, ?_⟩
      apply holds_update hAt.2.2.2.2
      intro p hp
      simp [dequantPollFacts, dequantHeadFacts] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨u, hLocal, hu⟩ := raw_poll_return hStart
    cases tail with
    | nil => exact (hTail rfl).elim
    | cons hd tl => exact ⟨u, hu, after_softmax_local_prefix hLocal hRest⟩
  | last hTau hStep =>
    rw [stop_unique hTau .refl (stops_of_estep hStep) hStop] at hStep
    obtain ⟨m, hEvent, hFire⟩ := hStep
    rw [hOut] at hEvent
    obtain rfl := Out.ev.inj hEvent.symm
    obtain ⟨_, _, hBad⟩ := hFire
    cases hBad

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
