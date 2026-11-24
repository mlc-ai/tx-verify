-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxMaskControl
import Lemmas.Flow.EventCont
import Lemmas.Flow.Footprint
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Lemmas.Flow.Polls
import Lemmas.Flow.Final
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

@[expose] public section

/-! # The actual QK wait operands are fixed by the loop control -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

def qkPollFacts (L : Launch) (block : Nat) : List (Nat × Value) :=
  [(977, b32 (L.sharedBase + (222904 + 8 * (block % 2)))), (978, b32 (block / 2 % 2))]

/-- A successful mask poll sets up the QK object's address and parity without score data. -/
theorem softmax_qk_setup {t : TState} {block total : Nat}
    (hpre : Pre P L mem0) (ht : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
        (PTX.next (setReg t 4075 (.pred true))) u ∧
      AtVector u 272 (qkPollFacts L block) t.sub t.acc := by
  let s := PTX.next (setReg t 4075 (.pred true))
  have hp : s.pc = 265 := by change t.pc + 1 = 265; rw [ht.1]
  have hAt : AtVector s 265 ((4075, .pred true) :: softmaxMaskFacts L block total) t.sub t.acc := by
    refine ⟨hp, rfl, rfl, ht.2.2.2.1, ?_⟩
    change Holds (setReg t 4075 (.pred true)).regs _
    refine (holds_cons _ _ _ _).mpr ⟨by simp [setReg], holds_update ht.2.2.2.2 ?_⟩
    intro p hp
    simp [softmaxMaskFacts, softmaxLoopFacts, softmaxLoopRegs, factsFrom] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hB := sharedBase_lt hpre
  have hPhase : block / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hSlot : block % 2 < 2 := Nat.mod_lt _ (by decide)
  have hRun : ∃ u, run kernel Assumptions.all L g 6 s = some u ∧
      AtVector u 272 (qkPollFacts L block) t.sub t.acc := by
    seg_fp hAt using
      (try unfold b32)
      (try norm_bits [Wg0.land255, Nat.add_zero, Nat.add_assoc])
  obtain ⟨u, hu, hState⟩ := hRun
  exact ⟨u, run_rtg hu, hState⟩

/-- The recovered operands determine the actual QK notification acquire. -/
theorem qk_poll_template {t : TState} {block : Nat}
    (hpre : Pre P L mem0) (ht : AtVector t 272 (qkPollFacts L block) t.sub t.acc) :
    ∃ scope, out kernel Assumptions.all L g t =
      .ev (.wait ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩
        (block / 2 % 2) (fun ok => PTX.next (setReg t 4076 (.pred ok))) true scope) := by
  have hm := mbarLoc_b32 (L := L) (g := g) (t := t) (base := 977)
    ht.2.2.2.2.1 (Wg0.ringAddr_lt hpre (buf := block % 2) (by omega))
    (Wg0.ringAddr_mod8 hpre (off := 222904) (by decide))
  have hp := readBits_b32 (L := L) (g := g) (t := t) (r := 978) (a := block / 2 % 2)
    ht.2.2.2.2.2.1 (by omega)
  obtain ⟨scope, h⟩ := eventTmpl_mbarWait_next (A := Assumptions.all)
    (p := 4076) (acq := true) (sc := .cta) hm hp
  rw [out_event ht.2.2.2.1 (ht.1 ▸ Flow.code_272) rfl rfl, h]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : block / 2 % 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2))]
  exact ⟨scope, rfl⟩

/-- A failed QK acquire retains the same operands for its retry. -/
theorem retry_qk_poll {t : TState} {block : Nat}
    (ht : AtVector t 272 (qkPollFacts L block) t.sub t.acc) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
        (PTX.next (setReg t 4076 (.pred false))) u ∧
      AtVector u 272 (qkPollFacts L block) u.sub u.acc := by
  let v := PTX.next (setReg t 4076 (.pred false))
  let w := skip v
  let u := { w with pc := 272 }
  have hv : v.pc = 273 := by change t.pc + 1 = 273; rw [ht.1]
  have hw : w.pc = 274 := by change v.pc + 1 = 274; rw [hv]
  have hPred : v.regs 4076 = some (.pred false) := by simp [v, PTX.next, setReg]
  have hFault : v.fault = none := ht.2.2.2.1
  have hSkip : Tau kernel Assumptions.all L g v w := by
    simp [Tau, out, hFault, hv, Flow.code_273, guardHolds, readReg, hPred,
      pure, Except.pure, bind, Except.bind, w]
  have hNoLocal := Thread.asms_localRule_bra (L := L) (g := g) (t := w)
    (target := 272) (uni := false) (by rw [hw]; decide) (by rw [hw]; decide)
  have hBranch : Tau kernel Assumptions.all L g w u := by
    have hwFault : w.fault = none := hFault
    simp [Tau, out, hwFault, hw, Flow.code_274, guardHolds, pure, Except.pure,
      execLocalA_noSegment (Proof.asms_segment_free w), execLocalRule_of_none hNoLocal,
      execLocal, Op.rule, execBranch, Op.isLocal, u]
  refine ⟨u, (Relation.ReflTransGen.single hSkip).tail hBranch, ⟨rfl, rfl, rfl, hFault, ?_⟩⟩
  apply holds_update ht.2.2.2.2
  intro p hp
  simp [qkPollFacts] at hp
  rcases hp with rfl | rfl <;> simp

private theorem qk_poll_step {t : TState} {block : Nat} {e : Event}
    {tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 272 (qkPollFacts L block) t.sub t.acc)
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) :
    ∃ ok scope, e =
        ⟨272, .wait ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩
          (block / 2 % 2) ok true scope⟩ ∧
      Run kernel Assumptions.all L g (PTX.next (setReg t 4076 (.pred ok))) tail o := by
  obtain ⟨scope, hOut⟩ := qk_poll_template hpre hAt
  cases hRun with
  | step hTau hStep hRest =>
    rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
    obtain ⟨m, hm, hf⟩ := hStep
    rw [hOut] at hm
    cases hm
    rw [hAt.1] at hf
    obtain ⟨ok, he, hState⟩ := hf
    obtain rfl := Option.some.inj hState
    exact ⟨ok, scope, he, hRest⟩
  | last hTau hStep =>
    rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
    obtain ⟨m, hm, hf⟩ := hStep
    rw [hOut] at hm
    cases hm
    obtain ⟨ok, _, hState⟩ := hf
    cases hState

set_option maxRecDepth 100000 in
private theorem after_qk_window : stableRegisterWindow 2953 275 1122 = true := by
  decide +kernel

private theorem qk_poll_pass {t : TState} {block : Nat}
    (hAt : AtVector t 272 (qkPollFacts L block) t.sub t.acc) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
        (PTX.next (setReg t 4076 (.pred true))) u ∧ u.pc = 275 := by
  let s := PTX.next (setReg t 4076 (.pred true))
  let v := { s with pc := 275 }
  have hPc : s.pc = 273 := by change t.pc + 1 = 273; rw [hAt.1]
  have hFault : s.fault = none := hAt.2.2.2.1
  have hPred : s.regs 4076 = some (.pred true) := by simp [s, PTX.next, setReg]
  have hNoLocal := Thread.asms_localRule_bra (L := L) (g := g) (t := s)
    (target := 275) (uni := false) (by rw [hPc]; decide) (by rw [hPc]; decide)
  have hTau : Tau kernel Assumptions.all L g s v := by
    simp [Tau, out, hFault, hPc, Flow.code_273, guardHolds, readReg, hPred, pure, Except.pure,
      bind, Except.bind, execLocalA_noSegment (Proof.asms_segment_free s),
      execLocalRule_of_none hNoLocal, execLocal, Op.rule, execBranch, Op.isLocal, v]
  exact ⟨v, .single hTau, rfl⟩

/-- A successful poll issued by the QK wait on the selected object. -/
def successfulQkPoll (m : Loc) (e : Event) : Bool :=
  (e.pc == 272) && okPoll m e

private theorem qk_poll_in_round {t : TState} {block : Nat} {e : Event} {m : Loc}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 272 (qkPollFacts L block) t.sub t.acc)
    (hTag : e.pc = 272) (hNoPub : ∀ f ∈ before, f.pc ≠ 1122)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    before.countP (successfulQkPoll m) = 0 ∧
      ∃ ok scope, e.kind = .wait
        ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩
        (block / 2 % 2) ok true scope := by
  induction before generalizing t with
  | nil =>
    obtain ⟨ok, scope, he, _⟩ := qk_poll_step hpre hAt hRun
    exact ⟨rfl, ok, scope, congrArg Event.kind he⟩
  | cons f before ih =>
    obtain ⟨ok, scope, hF, hRest⟩ := qk_poll_step hpre hAt hRun
    change Run kernel Assumptions.all L g _ (before ++ e :: tail) o at hRest
    cases ok with
    | false =>
      obtain ⟨u, hu, hU⟩ := retry_qk_poll hAt
      obtain ⟨front, after, hEq⟩ := List.exists_cons_of_ne_nil
        (show before ++ e :: tail ≠ [] by simp)
      rw [hEq] at hRest
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      obtain ⟨hZero, hEvent⟩ := ih hU (fun f hf => hNoPub f (List.mem_cons_of_mem _ hf)) hSuffix
      exact ⟨by simp [hF, successfulQkPoll, sourceWaitSuccess, hZero], hEvent⟩
    | true =>
      obtain ⟨u, hu, hU⟩ := qk_poll_pass hAt
      obtain ⟨front, after, hEq⟩ := List.exists_cons_of_ne_nil
        (show before ++ e :: tail ≠ [] by simp)
      rw [hEq] at hRest
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      obtain ⟨v, a, p, hFirst, hLast, _, hLocal, hFire⟩ :=
        register_at_event_in_window after_qk_window Flow.code_1121 rfl hU.ge
          (hU ▸ by decide) (fun f hf => hNoPub f (List.mem_cons_of_mem _ hf)) hSuffix
      have hRegion := local_path_in_register_window after_qk_window ⟨hFirst, hLast.le⟩ hLocal
      have hpc := estep_source_pc hFire
      rw [← hpc, hTag] at hRegion
      exact ((by decide : ¬ inRegisterWindow 275 1122 272) hRegion).elim

/-- Within one loop block all actual QK polls have its slot and parity. -/
theorem softmax_qk_poll_in_round {t : TState} {block total : Nat} {e : Event} {m : Loc}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = 272) (hNoPub : ∀ f ∈ before, f.pc ≠ 1122)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    before.countP (successfulQkPoll m) = 0 ∧
      ∃ ok scope, e.kind = .wait
        ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩
        (block / 2 % 2) ok true scope := by
  induction before generalizing t with
  | nil =>
    have hOut := mask_poll_template (g := g) hpre hAt
    cases hRun with
    | step hTau hStep _ | last hTau hStep =>
      rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
      have h := estep_source_pc hStep
      rw [hTag, hAt.1] at h
      cases h
  | cons f before ih =>
    have hTail : before ++ e :: tail ≠ [] := by simp
    obtain ⟨ok, hF, hRest⟩ := softmax_mask_poll_from_run hpre hAt hRun hTail
    change Run kernel Assumptions.all L g _ (before ++ e :: tail) o at hRest
    obtain ⟨front, after, hEq⟩ := List.exists_cons_of_ne_nil hTail
    rw [hEq] at hRest
    have hPrefix (f : Event) (hf : f ∈ before) : f.pc ≠ 1122 :=
      hNoPub f (List.mem_cons_of_mem _ hf)
    cases ok with
    | false =>
      obtain ⟨u, hu, hU⟩ := retry_mask_poll hAt
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      obtain ⟨hZero, hEvent⟩ := ih hU hPrefix hSuffix
      exact ⟨by simp [hF, successfulQkPoll, hZero], hEvent⟩
    | true =>
      obtain ⟨u, hu, hU⟩ := softmax_qk_setup hpre hAt
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      have hU' : AtVector u 272 (qkPollFacts L block) u.sub u.acc := by
        simpa only [hU.2.1, hU.2.2.1] using hU
      obtain ⟨hZero, hEvent⟩ := qk_poll_in_round (m := m) hpre hU' hTag hPrefix hSuffix
      exact ⟨by simp [hF, successfulQkPoll, hZero], hEvent⟩

private theorem no_qk_poll_after_pass {t : TState} {m : Loc}
    {e : Event} {before tail : List Event} {o : Option TState}
    (ht : t.pc = 275) (hNoPub : ∀ f ∈ before, f.pc ≠ 1122)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    before.countP (successfulQkPoll m) = 0 := by
  apply List.countP_eq_zero.mpr
  intro f hf
  obtain ⟨front, after, hEq⟩ := List.append_of_mem hf
  have ht' : Run kernel Assumptions.all L g t (front ++ f :: (after ++ e :: tail)) o := by
    rw [hEq, List.append_assoc, List.cons_append] at hRun
    exact hRun
  obtain ⟨_, _, _, hFirst, hLast, _, hLocal, hStep⟩ :=
    register_at_event_in_window after_qk_window Flow.code_1121 rfl ht.ge
      (ht ▸ by decide) (fun x hx => hNoPub x (by rw [hEq]; exact List.mem_append_left _ hx)) ht'
  have h := local_path_in_register_window after_qk_window ⟨hFirst, hLast.le⟩ hLocal
  have hPc := estep_source_pc hStep
  rw [← hPc] at h
  have hNe : f.pc ≠ 272 := by obtain ⟨h, _⟩ := h; omega
  simp [successfulQkPoll, hNe]

private theorem qk_count_to_publication {t : TState} {block : Nat} {m : Loc}
    {e : Event} {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 272 (qkPollFacts L block) t.sub t.acc)
    (hTag : e.pc = 1122) (hNoPub : ∀ f ∈ before, f.pc ≠ 1122)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    before.countP (successfulQkPoll m) =
      if m = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩ then 1 else 0 := by
  induction before generalizing t with
  | nil =>
    obtain ⟨ok, scope, he, _⟩ := qk_poll_step hpre hAt hRun
    rw [he] at hTag
    cases hTag
  | cons f before ih =>
    obtain ⟨ok, scope, hf, hRest⟩ := qk_poll_step hpre hAt hRun
    change Run kernel Assumptions.all L g _ (before ++ e :: tail) o at hRest
    have hPrefix (f : Event) (hf : f ∈ before) : f.pc ≠ 1122 :=
      hNoPub f (List.mem_cons_of_mem _ hf)
    obtain ⟨front, after, hEq⟩ := List.exists_cons_of_ne_nil
      (show before ++ e :: tail ≠ [] by simp)
    rw [hEq] at hRest
    cases ok with
    | false =>
      obtain ⟨u, hu, hU⟩ := retry_qk_poll hAt
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      have h := ih hU hPrefix hSuffix
      simpa [hf, successfulQkPoll, sourceWaitSuccess] using h
    | true =>
      obtain ⟨u, hu, hU⟩ := qk_poll_pass hAt
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      have h := no_qk_poll_after_pass (m := m) hU hPrefix hSuffix
      rw [List.countP_cons, h, hf]
      simp only [Nat.zero_add, successfulQkPoll, sourceWaitSuccess, beq_self_eq_true,
        Bool.true_and, decide_eq_true_eq]
      exact if_congr eq_comm rfl rfl

/-- An actual completed loop body contains one QK success, on that block's object. -/
theorem softmax_qk_count_in_round {t : TState} {block total : Nat} {m : Loc}
    {e : Event} {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = 1122) (hNoPub : ∀ f ∈ before, f.pc ≠ 1122)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    before.countP (successfulQkPoll m) =
      if m = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩ then 1 else 0 := by
  induction before generalizing t with
  | nil =>
    have hOut := mask_poll_template (g := g) hpre hAt
    cases hRun with
    | step hTau hStep _ | last hTau hStep =>
      rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
      have h := estep_source_pc hStep
      rw [hTag, hAt.1] at h
      cases h
  | cons f before ih =>
    have hTail : before ++ e :: tail ≠ [] := by simp
    obtain ⟨ok, hf, hRest⟩ := softmax_mask_poll_from_run hpre hAt hRun hTail
    change Run kernel Assumptions.all L g _ (before ++ e :: tail) o at hRest
    obtain ⟨front, after, hEq⟩ := List.exists_cons_of_ne_nil hTail
    rw [hEq] at hRest
    have hPrefix (f : Event) (hf : f ∈ before) : f.pc ≠ 1122 :=
      hNoPub f (List.mem_cons_of_mem _ hf)
    cases ok with
    | false =>
      obtain ⟨u, hu, hU⟩ := retry_mask_poll hAt
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      simpa [hf, successfulQkPoll] using ih hU hPrefix hSuffix
    | true =>
      obtain ⟨u, hu, hU⟩ := softmax_qk_setup hpre hAt
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      have hU' : AtVector u 272 (qkPollFacts L block) u.sub u.acc := by
        simpa only [hU.2.1, hU.2.2.1] using hU
      simpa [hf, successfulQkPoll] using qk_count_to_publication hpre hU' hTag hPrefix hSuffix

/-- Concrete QK polls follow their block's parity and destination even after dismissals. -/
theorem softmax_qk_poll_in_trace {t : TState} {block total : Nat} {e : Event}
    {before tail : List Event} {o : Option TState} (slot : Fin 2)
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = 272) (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    let visit := block + before.countP isProbabilityPublication
    let qk : Loc := ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * slot.val)⟩
    (before.countP (successfulQkPoll qk) =
      (visit + (1 - slot.val)) / 2 - (block + (1 - slot.val)) / 2) ∧
    ∃ ok scope, e.kind = .wait
      ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (visit % 2))⟩
      (visit / 2 % 2) ok true scope := by
  let qk : Loc := ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * slot.val)⟩
  let seen := before.takeWhile (!isProbabilityPublication ·)
  let later := before.dropWhile (!isProbabilityPublication ·)
  have hSplit : before = seen ++ later := List.takeWhile_append_dropWhile.symm
  have hPrefix : ∀ f ∈ seen, f.pc ≠ 1122 := by
    intro f hf
    have h := List.all_eq_true.mp List.all_takeWhile f hf
    exact (show f.pc ≠ Wg0.Site.soReady.pc by
      simpa [isProbabilityPublication, Bool.not_eq_true'] using h)
  have hNone : seen.countP isProbabilityPublication = 0 := by
    apply List.countP_eq_zero.mpr
    intro f hf
    have hNo : f.pc ≠ Wg0.Site.soReady.pc := hPrefix f hf
    simp [isProbabilityPublication, hNo]
  cases hLater : later with
  | nil =>
    have hBefore : before = seen := by simpa only [hLater, List.append_nil] using hSplit
    dsimp only
    rw [hBefore, hNone, Nat.add_zero]
    obtain ⟨hZero, hEvent⟩ :=
      softmax_qk_poll_in_round (m := qk) hpre hAt hTag
        (fun f hf => hPrefix f (hBefore ▸ hf)) hRun
    rw [hBefore] at hZero
    exact ⟨by rw [hZero, Nat.sub_self], hEvent⟩
  | cons pub remaining =>
    have hHead := List.head?_dropWhile_not (!isProbabilityPublication ·) before
    change before.dropWhile (!isProbabilityPublication ·) = pub :: remaining at hLater
    rw [hLater] at hHead
    have hPub : pub.pc = Wg0.Site.soReady.pc := by simpa [isProbabilityPublication] using hHead
    change before = seen ++ before.dropWhile (!isProbabilityPublication ·) at hSplit
    rw [hLater] at hSplit
    have hTrace : before ++ e :: tail = seen ++ pub :: (remaining ++ e :: tail) := by
      rw [hSplit, List.append_assoc, List.cons_append]
    have hRun' : Run kernel Assumptions.all L g t (seen ++ pub :: (remaining ++ e :: tail)) o :=
      hTrace ▸ hRun
    have hThis := softmax_qk_count_in_round (m := qk) hpre hAt hPub hPrefix hRun'
    have hStep :
        (if qk = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩
          then 1 else 0) =
        (block + 1 + (1 - slot.val)) / 2 - (block + (1 - slot.val)) / 2 := by
      have hEq : qk = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩ ↔
          slot.val = block % 2 := by
        simp only [qk, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
        omega
      simp only [hEq]
      have := slot.isLt
      split <;> omega
    rw [hStep] at hThis
    have hFacts : Holds t.regs (softmaxLoopFacts block total) := hAt.2.2.2.2.2.2.2.2
    obtain ⟨u, hu, hRegs, hPubRun⟩ := softmax_loop_facts_at_publication
      (by rw [hAt.1]; decide) (by rw [hAt.1]; decide) hFacts hPub hPrefix hRun'
    by_cases hMore : block + 1 < total
    · have hNonempty : remaining ≠ [] := by
        intro hNil
        rw [hNil] at hPubRun
        obtain ⟨v, hLocal, hv, hRun''⟩ :=
          softmax_next_head_after_publication hMore hLimit hu hRegs hPubRun (by simp)
        have hFirst := softmax_opening_event_bound hv.1
          (after_softmax_local_prefix hLocal hRun'')
        rw [hTag] at hFirst
        omega
      obtain ⟨opening, rest, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
      have hOpening : opening.pc ≤ 256 := by
        obtain ⟨v, hv, hV, hOpen⟩ := softmax_next_head_after_publication hMore hLimit hu hRegs
          hPubRun (by simp)
        exact softmax_opening_event_bound hV.1 (after_softmax_local_prefix hv hOpen)
      have hBody : ∃ v, AtVector v 264 (softmaxMaskFacts L (block + 1) total) v.sub v.acc ∧
          Run kernel Assumptions.all L g v (rest ++ e :: tail) o := by
        obtain ⟨poll, after, hEq⟩ := List.exists_cons_of_ne_nil
          (show rest ++ e :: tail ≠ [] by simp)
        rw [List.cons_append, hEq] at hPubRun
        rw [hEq]
        exact softmax_next_mask_after_publication hpre hMore hLimit hu hRegs hPubRun
      obtain ⟨v, hv, hRest⟩ := hBody
      obtain ⟨hRec, hKind⟩ := softmax_qk_poll_in_trace slot hpre hMore hLimit hv hTag hRest
      have hOpen : isProbabilityPublication opening = false := by
        simp [isProbabilityPublication, show opening.pc ≠ Wg0.Site.soReady.pc from by
          change opening.pc ≠ 1122; omega]
      have hPub' : isProbabilityPublication pub = true := by
        simp [isProbabilityPublication, hPub]
      have hVisit : block + before.countP isProbabilityPublication =
          block + 1 + rest.countP isProbabilityPublication := by
        rw [hSplit, List.countP_append, hNone]
        simp [hPub', hOpen, Nat.add_comm, Nat.add_left_comm]
      have h0 : successfulQkPoll qk opening = false := by
        simp [successfulQkPoll, show opening.pc ≠ 272 from by omega]
      have h1 : successfulQkPoll qk pub = false := by
        have hPc : pub.pc = 1122 := hPub
        simp [successfulQkPoll, hPc]
      dsimp only
      rw [hVisit]
      refine ⟨?_, hKind⟩
      change before.countP (successfulQkPoll qk) = _
      rw [hSplit, List.countP_append, hThis]
      simp only [List.countP_cons, h0, h1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      change rest.countP (successfulQkPoll qk) =
        (block + 1 + rest.countP isProbabilityPublication + (1 - slot.val)) / 2 -
          (block + 1 + (1 - slot.val)) / 2 at hRec
      rw [hRec]
      omega
    · have hFinal : total = block + 1 := by omega
      subst total
      have hNo := event_after_final_publication_lower hLimit hu hRegs hPubRun
        (List.mem_append_right remaining (List.mem_cons_self))
      rw [hTag] at hNo
      omega
termination_by before.length
decreasing_by
  simp only [hSplit, List.length_append, List.length_cons]
  omega

/-- Probability publications issued on this score object. -/
def scorePublishedTo (m : Loc) (e : Event) : Bool :=
  isProbabilityPublication e && arrivesOn m e

/-- Every slot's observed QK completions precede that slot's probability releases. At the
current release there has been one more QK success for the selected slot. -/
theorem softmax_probability_history_in_trace {t : TState} {block total : Nat} {e : Event}
    {before tail : List Event} {o : Option TState} (slot : Fin 2)
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = Wg0.Site.soReady.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    let qk : Loc := ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * slot.val)⟩
    let score : Loc := ⟨.shared, ctaOf L g, L.sharedBase + (222920 + 8 * slot.val)⟩
    let visit := block + before.countP isProbabilityPublication
    (before.countP (successfulQkPoll qk) =
      (visit + 1 + (1 - slot.val)) / 2 - (block + (1 - slot.val)) / 2) ∧
    (before.countP (scorePublishedTo score) =
      (visit + (1 - slot.val)) / 2 - (block + (1 - slot.val)) / 2) ∧
    e.kind = .arrive
      ⟨.shared, ctaOf L g, L.sharedBase + (222920 + 8 * (visit % 2))⟩ 0 1 true .cta := by
  let qk : Loc := ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * slot.val)⟩
  let score : Loc := ⟨.shared, ctaOf L g, L.sharedBase + (222920 + 8 * slot.val)⟩
  let seen := before.takeWhile (!isProbabilityPublication ·)
  let later := before.dropWhile (!isProbabilityPublication ·)
  have hSplit : before = seen ++ later := List.takeWhile_append_dropWhile.symm
  have hPrefix : ∀ f ∈ seen, f.pc ≠ 1122 := by
    intro f hf
    have h := List.all_eq_true.mp List.all_takeWhile f hf
    exact (show f.pc ≠ Wg0.Site.soReady.pc by
      simpa [isProbabilityPublication, Bool.not_eq_true'] using h)
  have hNone : seen.countP isProbabilityPublication = 0 := by
    apply List.countP_eq_zero.mpr
    intro f hf
    have hNo : f.pc ≠ Wg0.Site.soReady.pc := hPrefix f hf
    simp [isProbabilityPublication, hNo]
  have hNoScore : seen.countP (scorePublishedTo score) = 0 := by
    apply List.countP_eq_zero.mpr
    intro f hf
    have hNo : f.pc ≠ Wg0.Site.soReady.pc := hPrefix f hf
    simp [scorePublishedTo, isProbabilityPublication, hNo]
  have hSlot := slot.isLt
  have hCount (n : Nat) :
      (if qk = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (n % 2))⟩ then 1 else 0) =
        (n + 1 + (1 - slot.val)) / 2 - (n + (1 - slot.val)) / 2 := by
    have hEq : qk = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (n % 2))⟩ ↔
        slot.val = n % 2 := by
      simp only [qk, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
      omega
    simp only [hEq]
    split <;> omega
  cases hLater : later with
  | nil =>
    have hBefore : before = seen := by simpa only [hLater, List.append_nil] using hSplit
    dsimp only
    rw [hBefore, hNone, Nat.add_zero]
    have hRun' : Run kernel Assumptions.all L g t (seen ++ e :: tail) o := hBefore ▸ hRun
    refine ⟨?_, ?_, probability_arrival_in_round hpre hAt hTag hPrefix hRun'⟩
    · rw [softmax_qk_count_in_round (m := qk) hpre hAt hTag hPrefix hRun']
      exact hCount block
    · rw [hNoScore, Nat.add_zero, Nat.sub_self]
  | cons pub remaining =>
    have hHead := List.head?_dropWhile_not (!isProbabilityPublication ·) before
    change before.dropWhile (!isProbabilityPublication ·) = pub :: remaining at hLater
    rw [hLater] at hHead
    have hPub : pub.pc = Wg0.Site.soReady.pc := by simpa [isProbabilityPublication] using hHead
    change before = seen ++ before.dropWhile (!isProbabilityPublication ·) at hSplit
    rw [hLater] at hSplit
    have hTrace : before ++ e :: tail = seen ++ pub :: (remaining ++ e :: tail) := by
      rw [hSplit, List.append_assoc, List.cons_append]
    have hRun' : Run kernel Assumptions.all L g t (seen ++ pub :: (remaining ++ e :: tail)) o :=
      hTrace ▸ hRun
    have hThis := softmax_qk_count_in_round (m := qk) hpre hAt hPub hPrefix hRun'
    rw [hCount] at hThis
    have hPubKind := probability_arrival_in_round hpre hAt hPub hPrefix hRun'
    have hPubCount : (if scorePublishedTo score pub then 1 else 0) =
        (block + 1 + (1 - slot.val)) / 2 - (block + (1 - slot.val)) / 2 := by
      rw [← hCount]
      have hPub' : isProbabilityPublication pub = true := by simp [isProbabilityPublication, hPub]
      simp only [scorePublishedTo, hPub', Bool.true_and, arrivesOn, sourceArrive, hPubKind,
        decide_eq_true_eq]
      apply if_congr
      · simp only [qk, score, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
        omega
      · rfl
      · rfl
    have hFacts : Holds t.regs (softmaxLoopFacts block total) := hAt.2.2.2.2.2.2.2.2
    obtain ⟨u, hu, hRegs, hPubRun⟩ := softmax_loop_facts_at_publication
      (by rw [hAt.1]; decide) (by rw [hAt.1]; decide) hFacts hPub hPrefix hRun'
    by_cases hMore : block + 1 < total
    · have hNonempty : remaining ≠ [] := by
        intro hNil
        rw [hNil] at hPubRun
        obtain ⟨v, hLocal, hv, hRun''⟩ :=
          softmax_next_head_after_publication hMore hLimit hu hRegs hPubRun (by simp)
        have hFirst := softmax_opening_event_bound hv.1
          (after_softmax_local_prefix hLocal hRun'')
        rw [hTag] at hFirst
        exact (by decide : ¬ Wg0.Site.soReady.pc ≤ 256) hFirst
      obtain ⟨opening, rest, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
      have hOpening : opening.pc ≤ 256 := by
        obtain ⟨v, hv, hV, hOpen⟩ := softmax_next_head_after_publication hMore hLimit hu hRegs
          hPubRun (by simp)
        exact softmax_opening_event_bound hV.1 (after_softmax_local_prefix hv hOpen)
      have hBody : ∃ v, AtVector v 264 (softmaxMaskFacts L (block + 1) total) v.sub v.acc ∧
          Run kernel Assumptions.all L g v (rest ++ e :: tail) o := by
        obtain ⟨poll, after, hEq⟩ := List.exists_cons_of_ne_nil
          (show rest ++ e :: tail ≠ [] by simp)
        rw [List.cons_append, hEq] at hPubRun
        rw [hEq]
        exact softmax_next_mask_after_publication hpre hMore hLimit hu hRegs hPubRun
      obtain ⟨v, hv, hRest⟩ := hBody
      obtain ⟨hRec, hRecScore, hRecKind⟩ :=
        softmax_probability_history_in_trace slot hpre hMore hLimit hv hTag hRest
      change rest.countP (successfulQkPoll qk) =
        (block + 1 + rest.countP isProbabilityPublication + 1 + (1 - slot.val)) / 2 -
          (block + 1 + (1 - slot.val)) / 2 at hRec
      have hOpen : isProbabilityPublication opening = false := by
        simp [isProbabilityPublication, show opening.pc ≠ Wg0.Site.soReady.pc from by
          change opening.pc ≠ 1122; omega]
      have hPub' : isProbabilityPublication pub = true := by simp [isProbabilityPublication, hPub]
      have h0 : successfulQkPoll qk opening = false := by
        simp [successfulQkPoll, show opening.pc ≠ 272 from by omega]
      have h1 : successfulQkPoll qk pub = false := by
        have hPc : pub.pc = 1122 := hPub
        simp [successfulQkPoll, hPc]
      have hOpenScore : scorePublishedTo score opening = false := by
        simp [scorePublishedTo, hOpen]
      have hVisit : block + before.countP isProbabilityPublication =
          block + 1 + rest.countP isProbabilityPublication := by
        rw [hSplit, List.countP_append, hNone]
        simp [hPub', hOpen, Nat.add_comm, Nat.add_left_comm]
      dsimp only
      rw [hVisit]
      refine ⟨?_, ?_, hRecKind⟩
      · change before.countP (successfulQkPoll qk) = _
        rw [hSplit, List.countP_append, hThis]
        simp only [List.countP_cons, h0, h1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [hRec]
        omega
      · change rest.countP (scorePublishedTo score) =
          (block + 1 + rest.countP isProbabilityPublication + (1 - slot.val)) / 2 -
            (block + 1 + (1 - slot.val)) / 2 at hRecScore
        change before.countP (scorePublishedTo score) = _
        rw [hSplit, List.countP_append, hNoScore, Nat.zero_add]
        simp only [List.countP_cons, hOpenScore, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [hRecScore, hPubCount]
        omega
    · have hFinal : total = block + 1 := by omega
      subst total
      have hNo := event_after_final_publication_lower hLimit hu hRegs hPubRun
        (List.mem_append_right remaining (List.mem_cons_self))
      rw [hTag] at hNo
      exact (by decide : ¬ 1147 ≤ Wg0.Site.soReady.pc) hNo |>.elim
termination_by before.length
decreasing_by
  simp only [hSplit, List.length_append, List.length_cons]
  omega

variable {X : Execution}

/-- The actual QK poll uses the slot and parity of its concrete block. -/
theorem actual_softmax_qk_wait {i : Nat} {e : Event} {m : Loc} {parity : Nat}
    {ok acq : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e) (hWg : wgOf L g = 0) (hTag : e.pc = Wg0.Site.qkDone.pc)
    (hKind : e.kind = .wait m parity ok acq scope) :
    ∃ block, e.kind = .wait
      ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩
      (block / 2 % 2) ok true scope := by
  have hg := Frame.lt_of_get hX he
  rcases Frame.fired hs hX he with ⟨state, _, hd, hFire⟩ | ⟨_, _, _, hUb⟩
  · cases state with
    | some state =>
      have hSite := RingSourceSites.poll_site hFire hKind
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      cases state with
      | wg0 d =>
        have hp := Frame.event_pc hs hX he hd
        change e.pc = d.site.pc at hp
        have hQk : d.site = .qkDone := by
          rcases hSite with h | h | h
          · rw [h, hTag] at hp
            cases hp
          · exact h
          · rw [h, hTag] at hp
            cases hp
        obtain ⟨r, s, hEvent⟩ := RingEvents.gemmDone_wait_exact hpre (.inl hQk) hFire
        simp only [hQk, ↓reduceIte, Wg0.qkDoneOff] at hEvent
        obtain ⟨_, _, hOk, _, hScope⟩ := Kind.wait.inj (hKind.symm.trans hEvent)
        exact ⟨d.block, hOk ▸ hScope ▸ hEvent⟩
      | wg2 d => change wgOf L g = 2 at hRole; omega
      | mma _ => change warpOf L g = 4 at hRole; unfold wgOf warpOf at *; omega
      | tma _ => change warpOf L g = 5 at hRole; unfold wgOf warpOf at *; omega
      | index _ => change warpOf L g = 7 at hRole; unfold wgOf warpOf at *; omega
      | prologue _ | head | idle _ | done => exact hSite.elim
    | none =>
      obtain ⟨j, hj, d, f, hf, hState, hn⟩ := prior_dismissal (PTX.len_of_get he).le hd
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
      cases dismissal_is_consumer hpre hX hs hf hState hn with
      | wg0 d =>
        obtain ⟨start, hBefore, initial, hSite, hInitial, hAnchor⟩ :=
          dismissed_wg0_first_mask_ready hpre hX hs hf hState hn
        let events := (X.tr g).drop start
        let k := i - start
        have hGet : events[k]? = some e := by
          change ((X.tr g).drop start)[i - start]? = _
          rw [List.getElem?_drop, Nat.add_sub_of_le (show start ≤ i by omega)]
          exact he
        have hMem := List.mem_of_getElem? hGet
        obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hAnchor
          (List.ne_nil_of_mem hMem)
        have hAt := softmax_mask_entry_facts hSite
          (show (Wg0.code P L g).AtD initial t from hGood.1)
        have hBlock : initial.block < Wg0.blocksOf P L g :=
          (show Wg0.Inv P L g initial from hGood.2).blockLt
        have hTotal : Wg0.blocksOf P L g < 2 ^ 31 := by
          have h := (Wg0.blocksOf_word_bounds hpre (Wg1Mma.batchOf_lt hpre hg)).2
          omega
        have hShort : k < events.length := (List.getElem?_eq_some_iff.mp hGet).1
        have hSplit : events = events.take k ++ e :: events.drop (k + 1) := by
          have hDrop := List.drop_eq_getElem_cons hShort
          rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
          rw [← hDrop]
          exact (List.take_append_drop ..).symm
        change Run kernel Assumptions.all L g t events o at hRun
        rw [hSplit] at hRun
        obtain ⟨_, r, s, hEvent⟩ :=
          softmax_qk_poll_in_trace 0 hpre hBlock hTotal hAt hTag hRun
        have hFields := Kind.wait.inj (hKind.symm.trans hEvent)
        exact ⟨_, hFields.2.2.1 ▸ hFields.2.2.2.2 ▸ hEvent⟩
      | wg2 d => change wgOf L g = 2 at hRole; omega
  · rw [hUb] at hKind
    cases hKind

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
