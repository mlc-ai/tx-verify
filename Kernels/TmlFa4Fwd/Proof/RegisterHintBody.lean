-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.RegisterHint
public import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRolePrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents
public import Kernels.TmlFa4Fwd.Proof.EpilogueLinearEvents
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Lemmas.Flow.NotRegister
public import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open Prologue Mma Softmax Correction Epilogue

noncomputable section

/-- The only decoded PCs that can issue a register adjustment. -/
def registerHintSites : List Nat := [179, 1907, 2769, 3102, 7746]

private theorem registerHintCode : OpPcsFast kernel.code setMaxRegOp registerHintSites = true := by
  decide +kernel

/-- A register request has one of the kernel's five audited PCs. -/
theorem registerRequestSite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc n inst : Nat} {inc : Bool}
    (he : SetMaxNReg.Request X i pc inc n inst) : pc ∈ registerHintSites := by
  rcases get_source hX he with ⟨_, hU⟩ | ⟨_, _, _, _, hc, hf⟩
  · cases hU
  · have hOp := fires_setMaxReg_op hf rfl
    exact OpPcsFast.mem registerHintCode hc (by rw [hOp]; rfl)

private def EventPcs (allowed : Nat → Prop) (events : List Event) : Prop :=
  ∀ e ∈ events, allowed e.pc

private theorem terminalEventPcs {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} {vs : List Visit} {allowed : Nat → Prop} (hReturn : allowed 9205)
    (hn : Next kernel Assumptions.all l g s u .exit) (hp : u.pc = 9205)
    (hW : Walk kernel Assumptions.all l g s es vs) : EventPcs allowed es := by
  have hOut := hn.stop
  have hStop : Stops kernel Assumptions.all l g u := ⟨_, hOut⟩
  suffices go : ∀ {t events visits},
      Walk kernel Assumptions.all l g t events visits →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u → EventPcs allowed events from
    go hW hn.steps
  intro t events visits hw ht
  induction hw with
  | stop => simp [EventPcs]
  | tau he _ ih =>
    rcases Relation.ReflTransGen.cases_head ht with rfl | ⟨_, h, hTail⟩
    · exact (not_tau_of_stops hStop he).elim
    · obtain rfl := tau_det h he
      exact ih hTail
  | ev he _ =>
    obtain rfl := stop_unique .refl ht (stops_of_estep he) hStop
    obtain ⟨tm, ho, hf⟩ := he
    rw [hOut] at ho
    obtain rfl := Out.ev.inj ho
    cases hf.2
  | last he =>
    obtain rfl := stop_unique .refl ht (stops_of_estep he) hStop
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    rw [estep_source_pc he, hp]
    exact hReturn

section
variable {l : Launch} {g : Nat} {s : TState} {es : List Event} {vs : List Visit}

private theorem bodyEventPcs {P Q : TState → Prop} {allowed : Nat → Prop}
    (hPc : ∀ t, P t → allowed t.pc)
    (hStep : ∀ {t u e}, P t → WStep kernel Assumptions.all l g t e u → P u ∨ Q u)
    (hTail : ∀ {t es vs}, Q t → Walk kernel Assumptions.all l g t es vs → EventPcs allowed es)
    (hs : P s) (hW : Walk kernel Assumptions.all l g s es vs) : EventPcs allowed es := by
  induction hW with
  | stop => simp [EventPcs]
  | tau he hW ih =>
    exact (hStep hs (.inl ⟨rfl, he⟩)).elim ih (fun h => hTail h hW)
  | ev he hW ih =>
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (estep_source_pc he).symm ▸ hPc _ hs
    · exact ((hStep hs (.inr ⟨_, rfl, he⟩)).elim ih (fun h => hTail h hW)) _ hm
  | last he =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    exact (estep_source_pc he).symm ▸ hPc _ hs

private def BranchBody (i : Fin 3) : Nat × Nat :=
  match i with
  | 0 => (2770, 3099)
  | 1 => (3103, 7742)
  | _ => (7747, 9205)

private def retOp : Op → Bool
  | .ret => true
  | _ => false

private def branchBodyCode (i : Fin 3) (op : Op) : Bool :=
  (op.isLocal || correctionReturningOp op || epilogueExtraOp op || retOp op) &&
    !(writesRegs op).contains 1062 && !(scoreEventWrites op).contains 1062 &&
    !(epilogueExtraWrites op).contains 1062 &&
    match op with
    | .bra dest _ => (BranchBody i).1 ≤ dest && dest ≤ (BranchBody i).2
    | .brx .. => false
    | _ => true

private theorem branchBodyCodeAt (i : Fin 3) {pc : Nat} {ins : Instr}
    (hLo : (BranchBody i).1 ≤ pc) (hHi : pc < (BranchBody i).2)
    (hc : kernel.code[pc]? = some ins) : branchBodyCode i ins.op = true := by
  let lo := (BranchBody i).1
  let hi := (BranchBody i).2
  have hAll : ((kernel.code.drop lo).take (hi - lo)).all (fun ins => branchBodyCode i ins.op) =
      true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  have hGet : ((kernel.code.drop lo).take (hi - lo))[pc - lo]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  exact List.all_eq_true.mp hAll _ (List.mem_of_getElem? hGet)

private theorem bodySegments (i : Fin 3) {s u : TState} {m : SegMatch CuteSlot}
    (hLo : (BranchBody i).1 ≤ s.pc) (hHi : s.pc < (BranchBody i).2)
    (hs : s.pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel s.pc = some m)
    (hU : Assumptions.execSwExp2 m s = .ok u) :
    (BranchBody i).1 ≤ u.pc ∧ u.pc ≤ (BranchBody i).2 ∧ u.sub ≤ 3 ∧
      u.regs 1062 = s.regs 1062 := by
  have hAll : Assumptions.swExp2Sites.all (fun pc => (match cuteExp2.matchAt kernel pc with
      | none => false
      | some m => !(Softmax.scoreSegmentWrites m).contains 1062 &&
          decide (3103 ≤ m.stop ∧ m.stop ≤ 7742))) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCode := List.all_eq_true.mp hAll _ hs
  rw [hm] at hCode
  have hRange : i = 1 := by
    fin_cases i
    · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hs
      change s.pc < 3099 at hHi
      omega
    · rfl
    · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hs
      change 7747 ≤ s.pc at hLo
      omega
  subst i
  obtain ⟨hp, hSub, _, hKeep⟩ := Softmax.scoreSegmentFrame hU
  have hrange : 3103 ≤ m.stop ∧ m.stop ≤ 7742 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hCode).2
  exact ⟨hp.symm ▸ hrange.1, hp.symm ▸ hrange.2, hSub ▸ Nat.zero_le _, hKeep 1062
    (by simpa using (Bool.and_eq_true_iff.mp hCode).1)⟩

private theorem branchBodyStep (i : Fin 3) {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : (BranchBody i).1 ≤ s.pc) (hHi : s.pc < (BranchBody i).2) (hSub : s.sub ≤ 3)
    (hw : WStep kernel Assumptions.all l g s e u) :
    (BranchBody i).1 ≤ u.pc ∧ u.pc ≤ (BranchBody i).2 ∧ u.sub ≤ 3 ∧
      u.regs 1062 = s.regs 1062 := by
  rcases hw with ⟨_, hTau⟩ | ⟨e, _, he⟩
  · obtain ⟨ins, hc, _, hSource⟩ := Softmax.tauScoreSource hTau
    have hCode := branchBodyCodeAt i hLo hHi hc
    simp only [branchBodyCode, Bool.and_eq_true] at hCode
    rcases hSource with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · exact ⟨by change _ ≤ s.pc + 1; omega, by change s.pc + 1 ≤ _; omega,
        Nat.zero_le _, rfl⟩
    · rcases scoreExecLocal hLocal with hF | ⟨m, hs, hm, hU⟩
      · have hR : 1062 ∉ writesRegs ins.op := by simpa using hCode.1.1.1.2
        have hp := hF.pc
        refine ⟨?_, ?_, hF.sub ▸ hSub, hF.regs 1062 hR⟩
        all_goals
          cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hp
          case bra dst uni =>
            simp only [hop, Bool.and_eq_true, decide_eq_true_eq] at hCode
            omega
          case brx => simp [hop] at hCode
          all_goals omega
      · exact bodySegments i hLo hHi hs hm hU
  · obtain ⟨ins, hc, hl, hFire⟩ := estep_event_source he
    have hCode := branchBodyCodeAt i hLo hHi hc
    simp only [branchBodyCode, hl, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at hCode
    rcases hCode.1.1.1.1 with (hOp | hOp) | hOp
    · have hr : 1062 ∉ scoreEventWrites ins.op := by simpa using hCode.1.1.2
      obtain ⟨hs, hR⟩ := correctionEventProgress hc hOp hSub hr he
      rcases hs.pc with ⟨hPc, _⟩ | ⟨hPc, _⟩
      all_goals exact ⟨by omega, by omega, hs.sub, hR⟩
    · have hr : 1062 ∉ epilogueExtraWrites ins.op := by simpa using hCode.1.2
      obtain ⟨hPc, hs, _, _⟩ := epilogueExtraProgress hc hOp he
      exact ⟨by omega, by omega, hs ▸ hSub, epilogueExtraRegs hc hOp hr he⟩
    · have hRet : ins.op = .ret := by cases ho : ins.op <;> simp_all [retOp]
      rw [hRet] at hFire
      cases hFire.2

private theorem faultEventPcs {allowed : Nat → Prop} (hFault : s.fault ≠ none) (hPc : allowed s.pc)
    (hW : Walk kernel Assumptions.all l g s es vs) : EventPcs allowed es := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp
    (show s.fault.isSome from by cases hs : s.fault <;> simp_all)
  have hOut : out kernel Assumptions.all l g s = .ev (.ub f) := by simp [out, hf]
  cases hW with
  | stop => simp [EventPcs]
  | tau he _ => exact (not_tau_of_stops ⟨_, hOut⟩ he).elim
  | ev he _ =>
    obtain ⟨tm, ht, hFire⟩ := he
    obtain rfl := Out.ev.inj (ht.symm.trans hOut)
    cases hFire.2
  | last he =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    exact (estep_source_pc he).symm ▸ hPc

private theorem branchBodyEventPcs (i : Fin 3) {l : Launch} {g warp : Nat}
    {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s (BranchBody i).1 [(1062, b32 warp), (2535, b32 l.sharedBase)])
    (hW : Walk kernel Assumptions.all l g s es vs) {allowed : Nat → Prop}
    (hRange : ∀ pc, (BranchBody i).1 ≤ pc → pc ≤ (BranchBody i).2 → allowed pc)
    (hReturn : allowed 9205)
    (hExit : ∀ {t}, t.pc = (BranchBody i).2 → t.fault = none →
      t.regs 1062 = some (b32 warp) →
      ∃ u, u.pc = 9205 ∧ Next kernel Assumptions.all l g t u .exit) : EventPcs allowed es := by
  let P := fun t : TState => (BranchBody i).1 ≤ t.pc ∧ t.pc < (BranchBody i).2 ∧
    t.sub ≤ 3 ∧ t.regs 1062 = some (b32 warp)
  let Q := fun t : TState => t.pc = (BranchBody i).2 ∧ t.regs 1062 = some (b32 warp)
  apply bodyEventPcs (allowed := allowed) (P := P) (Q := Q) (s := s)
    (fun t h => hRange t.pc h.1 h.2.1.le) _ _ _ hW
  · intro t u e h hStep
    obtain ⟨hl, hh, hS, hR⟩ := branchBodyStep i h.1 h.2.1 h.2.2.1 hStep
    rcases Nat.eq_or_lt_of_le hh with he | ht
    · exact .inr ⟨he, hR.trans h.2.2.2⟩
    · exact .inl ⟨hl, ht, hS, hR.trans h.2.2.2⟩
  · intro t es vs h hw
    by_cases hf : t.fault = none
    · obtain ⟨_, hp, hNext⟩ := hExit h.1 hf h.2
      exact terminalEventPcs hReturn hNext hp hw
    · exact faultEventPcs hf (h.1.symm ▸ hRange _ (by fin_cases i <;> decide) le_rfl) hw
  · exact ⟨hs.1.symm ▸ le_rfl, hs.1.symm ▸ (by fin_cases i <;> decide),
      hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.2.2.1⟩

private theorem epilogueCommonExit {l : Launch} {g warp : Nat} {t : TState}
    (hp : t.pc = 3099) (hf : t.fault = none) (hw : warp = 12 ∨ warp = 13)
    (hr : t.regs 1062 = some (b32 warp)) :
    ∃ u, u.pc = 9205 ∧ Next kernel Assumptions.all l g t u .exit := by
  have hModel {s : TState} (hpc : s.pc ∈ [3099, 3100, 7742, 7743, 7744, 9205]) :
      out kernel Assumptions.all l g s = out kernel [] l g s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    exact epilogue_out_all_eq_nil (by unfold EpiloguePc; omega)
  obtain ⟨u, hu, hPos, hOut⟩ := finishSchedulerOfWarpWith l g t hModel hp hf hw hr
  exact ⟨u, hPos, run_rtg hu, hOut⟩

private theorem mmaNextAfterHint {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 1908 ≤ s.pc) (hHi : s.pc < 2768) (hw : WStep kernel Assumptions.all l g s e u) :
    1908 ≤ u.pc := by
  rcases hw with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← Mma.out_eq_core (by omega) hHi]
    obtain ⟨i, hc⟩ := tau_core_has_code ht'
    have hAll : ((kernel.code.drop 1908).take 860).all (fun i => match i.op with
        | .bra dst _ => 1908 ≤ dst
        | .brx .. => false
        | _ => true) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hGet : ((kernel.code.drop 1908).take 860)[s.pc - 1908]? = some i := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
    have hCode := List.all_eq_true.mp hAll i (List.mem_of_getElem? hGet)
    rcases tau_core_frame hc ht' with rfl | hf
    · change 1908 ≤ s.pc + 1
      omega
    · have h := hf.pc
      cases hOp : i.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at h
      case bra dst uni => rw [h]; exact of_decide_eq_true (by simpa only [hOp] using hCode)
      case brx => simp [hOp] at hCode
      all_goals omega
  · have hE : EStep kernel [] l g s e (some u) := by
      obtain ⟨tm, hOut, hF⟩ := he
      exact ⟨tm, by rwa [← Mma.out_eq_core (by omega) hHi], hF⟩
    rcases (estep_return_pc hE (fun _ _ _ h => execLocal_frame h)).2 with h | h <;> omega

private theorem mmaEventPcs (hs : At s 1908 [(1062, b32 12), (2535, b32 l.sharedBase)])
    (hW : Walk kernel Assumptions.all l g s es vs) {allowed : Nat → Prop}
    (hRange : ∀ pc, 1908 ≤ pc → pc < 2768 → allowed pc) (hReturn : allowed 9205)
    : EventPcs allowed es := by
  let P := fun t : TState => 1908 ≤ t.pc ∧ t.pc < 2768 ∧
    RoleShape t ∧ t.regs 1062 = some (b32 12)
  let Q := fun t : TState => t.pc = 3099 ∧ t.fault = none ∧ t.regs 1062 = some (b32 12)
  apply bodyEventPcs (allowed := allowed) (P := P) (Q := Q) (s := s) _ _ _ _ hW
  · exact fun t h => hRange t.pc h.1 h.2.1
  · intro t u e h hStep
    obtain ⟨hP | hQ, hShape, hW⟩ := mmaCutStep (by have := h.1; omega) h.2.1 hStep h.2.2
    · exact .inl ⟨mmaNextAfterHint h.1 h.2.1 hStep, hP.2, hShape, hW⟩
    · exact .inr ⟨by simpa using hQ.1, hQ.2, hW⟩
  · intro t es vs h hw
    obtain ⟨_, hp, hNext⟩ := epilogueCommonExit (g := g) h.1 h.2.1 (.inl rfl) h.2.2
    exact terminalEventPcs hReturn hNext hp hw
  · exact ⟨hs.1.symm ▸ le_rfl, hs.1.symm ▸ (by decide),
      ⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩, hs.2.2.2.2.1⟩

private theorem loaderEventPcs (warp : Fin 2)
    (hs : At s 180 [(1062, b32 (14 + warp.val)), (2535, b32 l.sharedBase)])
    (hW : Walk kernel Assumptions.all l g s es vs) {allowed : Nat → Prop}
    (hRange : ∀ pc, 180 ≤ pc → pc ≤ 1901 → allowed pc) (hReturn : allowed 9205)
    : EventPcs allowed es := by
  let F := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]
  let P := fun t : TState => 180 ≤ t.pc ∧ t.pc < 1901 ∧ Loader.RingShape t ∧ Holds t.regs F
  let Q := fun t : TState => t.pc = 1901 ∧ Loader.RingShape t ∧ Holds t.regs F
  have hFrame (bound : Nat) : ((kernel.code.drop 180).take (1901 - 180)).all
      (fun ins => Loader.loaderPipelineCutOp 180 1901 bound (F.map Prod.fst) ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply bodyEventPcs (allowed := allowed) (P := P) (Q := Q) (s := s) _ _ _ _ hW
  · exact fun t h => hRange t.pc h.1 h.2.1.le
  · intro t u e h hStep
    obtain ⟨hl, hh, hShape, hR⟩ := Loader.pipelineCutStep (by decide : 174 ≤ 180)
      (by decide : 1901 ≤ 1901) ⟨h.1, h.2.1⟩ (hFrame u.pc) hStep h.2.2.1 h.2.2.2
    rcases Nat.eq_or_lt_of_le (hh.resolve_right (Nat.lt_irrefl _)) with he | hlt
    · exact .inr ⟨he, hShape, hR⟩
    · exact .inl ⟨hl, hlt, hShape, hR⟩
  · intro t es vs h hw
    by_cases hf : t.fault = none
    · have ht := Loader.pipelineAtCut h.1 h.2.1 h.2.2 hf ⟨_, Flow.code_1901, rfl⟩
      obtain ⟨_, hp, hNext⟩ := Loader.loaderRoleExit (g := g) warp ht
      exact terminalEventPcs hReturn hNext hp hw
    · exact faultEventPcs hf (h.1.symm ▸ hRange 1901 (by decide) le_rfl) hw
  · exact ⟨hs.1.symm ▸ le_rfl, hs.1.symm ▸ (by decide), Loader.ringShapeOfAt hs,
      hs.2.2.2.2.2.1, hs.2.2.2.2.1, trivial⟩

/-- A loader suffix at the drain exit can emit only a fault at the branch or the common exit. -/
theorem loaderExitEventPcs (warp : Fin 2) (hp : s.pc = 1901) (hShape : Loader.RingShape s)
    (hR : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, e.pc = 1901 ∨ e.pc = 9205 := by
  by_cases hf : s.fault = none
  · have hs := Loader.pipelineAtCut hp hShape hR hf ⟨_, Flow.code_1901, rfl⟩
    obtain ⟨_, hu, hNext⟩ := Loader.loaderRoleExit (g := g) warp hs
    exact terminalEventPcs (allowed := fun pc => pc = 1901 ∨ pc = 9205) (.inr rfl) hNext hu hw
  · exact faultEventPcs (allowed := fun pc => pc = 1901 ∨ pc = 9205) hf (.inl hp) hw

/-- After either Tensor Core or epilogue work reaches the common exit branch,
only the terminal event can follow in the actual walk. -/
theorem mmaEpilogueExitEvents {l : Launch} {g warp : Nat} {t : TState}
    {es : List Event} {vs : List Visit}
    (hp : t.pc = 3099) (hf : t.fault = none) (hw : warp = 12 ∨ warp = 13)
    (hr : t.regs 1062 = some (b32 warp))
    (hWalk : Walk kernel Assumptions.all l g t es vs) :
    ∀ e ∈ es, e.pc = 9205 := by
  obtain ⟨_, hPc, hNext⟩ := epilogueCommonExit (g := g) hp hf hw hr
  exact terminalEventPcs (allowed := (· = 9205)) rfl hNext hPc hWalk

/-- The physical event PCs reachable in each warp role after its register request. -/
def roleBodyPc (warp : Nat) (pc : Nat) : Prop :=
  pc = 9205 ∨
    if 14 ≤ warp then 180 ≤ pc ∧ pc ≤ 1901 else
    if warp = 13 then 2770 ≤ pc ∧ pc ≤ 3099 else
    if warp = 12 then 1908 ≤ pc ∧ pc < 2768 else
    if warp < 8 then 3103 ≤ pc ∧ pc ≤ 7742 else
      7747 ≤ pc ∧ pc ≤ 9205

/-- Every event after the first register request lies in the issuing warp's decoded role. -/
theorem roleBodyEventPcs (warp : Fin 16)
    (hs : At s (registerHintPc warp + 1) [(1062, b32 warp.val), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, roleBodyPc warp.val e.pc := by
  by_cases hL : 14 ≤ warp.val
  · let w : Fin 2 := ⟨warp.val - 14, by have := warp.isLt; omega⟩
    have hW : 14 + w.val = warp.val := Nat.add_sub_of_le hL
    have hAt : At s 180 [(1062, b32 (14 + w.val)), (2535, b32 l.sharedBase)] := by
      simpa only [registerHintPc, dispatchParamPc, ite_eq_left hL, hW] using hs
    exact loaderEventPcs w hAt hw
      (fun pc hl hh => by simpa [roleBodyPc, hL] using Or.inr ⟨hl, hh⟩) (.inl rfl)
  by_cases hE : warp.val = 13
  · have hp : registerHintPc warp + 1 = 2770 := by
      simp [registerHintPc, dispatchParamPc, hE]
    have hAt : At s (BranchBody 0).1 [(1062, b32 13), (2535, b32 l.sharedBase)] := by
      change At s 2770 [(1062, b32 13), (2535, b32 l.sharedBase)]
      simpa only [hp, hE] using hs
    refine branchBodyEventPcs 0 hAt hw ?_ (.inl rfl)
      (fun h hf hWarp => epilogueCommonExit h hf (.inr rfl) hWarp)
    intro pc hl hh
    exact .inr (by simpa [BranchBody, hL, hE] using And.intro hl hh)
  by_cases hM : warp.val = 12
  · have hp : registerHintPc warp + 1 = 1908 := by
      simp [registerHintPc, dispatchParamPc, hM]
    have hAt : At s 1908 [(1062, b32 12), (2535, b32 l.sharedBase)] := by
      simpa only [hp, hM] using hs
    refine mmaEventPcs hAt hw ?_ (.inl rfl)
    intro pc hl hh
    exact .inr (by simpa [hL, hE, hM] using And.intro hl hh)
  by_cases hS : warp.val < 8
  · let w : Fin 8 := ⟨warp.val, hS⟩
    have hAt : At s (BranchBody 1).1 [(1062, b32 w.val), (2535, b32 l.sharedBase)] := by
      simpa only [registerHintPc, dispatchParamPc, ite_eq_right hL, ite_eq_right hE,
        ite_eq_right hM, ite_eq_left hS, BranchBody] using hs
    refine branchBodyEventPcs 1 hAt hw ?_ (.inl rfl) ?_
    · intro pc hl hh
      exact .inr (by simpa [BranchBody, hL, hE, hM, hS] using And.intro hl hh)
    · intro t h hf hWarp
      obtain ⟨u, hu, hp, ho⟩ := softExitRun (g := g) w h hf hWarp
      exact ⟨u, hp, run_rtg hu, ho⟩
  · have hAt : At s (BranchBody 2).1 [(1062, b32 warp.val), (2535, b32 l.sharedBase)] := by
      simpa only [registerHintPc, dispatchParamPc, ite_eq_right hL, ite_eq_right hE,
        ite_eq_right hM, ite_eq_right hS, BranchBody] using hs
    refine branchBodyEventPcs 2 hAt hw ?_ (.inl rfl) ?_
    · intro pc hl hh
      exact .inr (by simpa [BranchBody, hL, hE, hM, hS] using And.intro hl hh)
    · intro t h hf _
      change t.pc = 9205 at h
      have hOut : out kernel Assumptions.all l g t = .ev .exit := by
        rw [out, hf, h, Flow.code_9205]
        rfl
      exact ⟨t, h, .refl, hOut⟩

/-- No role can reach another register hint after its first accepted request. -/
theorem noRegisterHintAfterFirst (warp : Fin 16)
    (hs : At s (registerHintPc warp + 1) [(1062, b32 warp.val), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, e.pc ∉ registerHintSites := by
  intro e hm
  obtain h | h := roleBodyEventPcs warp hs hw e hm
  · rw [h]; decide
  · simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    split_ifs at h <;> omega
end


/-- An actual post-startup event outside the register hints belongs to its issuing warp's
role range. This applies to arbitrary execution prefixes. -/
theorem roleBodyPcOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLate : 173 < e.pc) (hHint : e.pc ∉ registerHintSites) :
    roleBodyPc (warpIndex l g) e.pc := by
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨pos, t, o, hPos, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg he hLate
  have hIndex : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hSuffix : (X.tr g).drop pos ≠ [] :=
    fun h => (Nat.not_le_of_lt hIndex) ((List.drop_eq_nil_iff.mp h).trans hPos)
  obtain ⟨u, inst, hReq, hu, hTail⟩ := firstRegisterHintFromCommon hp hg warp ht hr hSuffix
  rcases Nat.eq_or_lt_of_le hPos with rfl | hLt
  · have hEq := Option.some.inj (he.symm.trans hReq)
    have hPc := congrArg Event.pc hEq
    exact (hHint (hPc.symm ▸ registerRequestSite hX (i := (g, pos)) hReq)).elim
  · obtain ⟨_, hWalk⟩ := walkFromRun hTail
    have hm : e ∈ (X.tr g).drop (pos + 1) := by
      apply List.mem_of_getElem? (i := index - (pos + 1))
      rw [List.getElem?_drop, Nat.add_sub_of_le hLt]
      exact he
    exact roleBodyEventPcs warp hu hWalk e hm

end
end PTX.Kernels.TmlFa4Fwd
