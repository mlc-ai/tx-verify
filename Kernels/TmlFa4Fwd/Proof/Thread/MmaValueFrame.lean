-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheBroadcasts
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueReadyProjection
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.MmaPvEntry
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.MmaValuePackedPrefix
public import Kernels.TmlFa4Fwd.Proof.MmaPvShape
import Lemmas.Flow.TcMmaTs
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
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
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.TauFrame
import Lemmas.Flow.Final
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

noncomputable section

def valueBroadcast (steady : Bool) : Nat := (valueDescriptorSite steady).prepare+8

private def valueLive (steady : Bool) (pos : Nat) : Prop :=
  valueBroadcast steady < pos ∧ pos ≤ if steady then 2533 else 2646

private instance (steady : Bool) (pos : Nat) : Decidable (valueLive steady pos) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A real V descriptor broadcast supplies the current odd cache use to its lane. -/
def ValueDescriptorUse (l : Launch) (X : Execution) (i : EvId)
    (steady : Bool) (use : Nat) : Prop :=
  (∃ sent ok, X.get i = some
    ⟨valueBroadcast steady, .shfl .idx sent 0 31 (b32 (valueDescriptorLow l use)) ok⟩) ∧
  (let ready := Mma.atPrefix l X i.1 i.2
   use = ready.kvAcquires 0 + ready.kvAcquires 1 + ready.kvAcquires 2 - 1) ∧ use % 2 = 1

/-- Both V ready gates have the same per-site acquisition count from
descriptor receipt through its consuming PV work. -/
def ValueReadyCursorStable (X : Execution) (g broadcast index : Nat) : Prop :=
  ∀ gate : Fin 4, gate = 1 ∨ gate = 3 →
    ((X.tr g).take broadcast).countP (readyAtSite gate) =
      ((X.tr g).take index).countP (readyAtSite gate)

private theorem valueReadyMarkQuiet {e : Event} (hPc : e.pc ≠ 2294 ∧ e.pc ≠ 2545)
    (gate : Fin 4) (hGate : gate = 1 ∨ gate = 3) : readyAtSite gate e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> try rfl
  case wait _ _ ok _ _ =>
    cases ok
    · rfl
    · rcases hGate with rfl | rfl
      · exact beq_eq_false_iff_ne.mpr hPc.1
      · exact beq_eq_false_iff_ne.mpr hPc.2

private theorem pvPackBetweenValueGates (block : Fin 4) (step : Fin 8) :
    (2294 < valueIdSite block ∧ pvPc block step ≤ 2545) ∨ 2545 < valueIdSite block := by
  fin_cases block <;> fin_cases step <;> decide

private theorem valueCursorQuietStep {X : Execution} {g begin index : Nat} {e : Event}
    (hFrame : ValueReadyCursorStable X g begin index) (he : X.get (g,index) = some e)
    (hQuiet : e.pc ≠ 2294 ∧ e.pc ≠ 2545) : ValueReadyCursorStable X g begin (index+1) := by
  intro gate hGate
  rw [List.take_add_one, show (X.tr g)[index]? = some e from he]
  simp [List.countP_append, valueReadyMarkQuiet hQuiet gate hGate, hFrame gate hGate]

private def valueCarries (l : Launch) (X : Execution) (g : Nat) (steady : Bool)
    (pos : Nat) (s : TState) : Prop :=
  valueLive steady s.pc → ∃ use j, j < pos ∧ ValueDescriptorUse l X (g,j) steady use ∧
    s.regs (valueDescriptorSite steady).output = some (b32 (valueDescriptorLow l use)) ∧
    ValueReadyCursorStable X g j pos

private theorem valueSlotLow (l : Launch) (use : Nat) :
    valueDescriptorLow l (readyStage use).val = valueDescriptorLow l use := by
  have hSlot : kvSlot (readyStage use).val = kvSlot use := by
    change (use % 3) % 3 = use % 3
    omega
  simp only [valueDescriptorLow, kvStart, hSlot]

private def valuePreservedEdge (steady : Bool) (pos dst : Nat) : Bool :=
  !decide (valueLive steady dst) || decide (valueLive steady pos)

private def valueCarryCode (steady : Bool) (pos : Nat) (ins : Instr) : Bool :=
  pos == valueBroadcast steady ||
    ((!(mmaWrites ins.op).contains (valueDescriptorSite steady).output &&
      valuePreservedEdge steady pos (pos+1)) &&
      match ins.op with
      | .bra dst _ => valuePreservedEdge steady pos dst
      | .brx .. => false
      | _ => true)

set_option maxRecDepth 100000 in
private theorem valueCarryAudit (steady : Bool) :
    (((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907).all
      (fun (ins,pos) => valueCarryCode steady pos ins) = true := by cases steady <;> kernel_rfl

private theorem valueCarryCheck (steady : Bool) {pos : Nat} {ins : Instr}
    (hLo : 1907 ≤ pos) (hHi : pos < 2768) (hOrd : pos ≠ valueBroadcast steady)
    (hc : kernel.code[pos]? = some ins) :
    (mmaWrites ins.op).contains (valueDescriptorSite steady).output = false ∧
      valuePreservedEdge steady pos (pos+1) = true ∧
      (match ins.op with
      | .bra dst _ => valuePreservedEdge steady pos dst
      | .brx .. => false
      | _ => true) = true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have hmem : (ins,pos) ∈ code := by
    apply List.mem_of_getElem? (i := pos-1907)
    dsimp only [code]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hc]
    rfl
  have h := List.all_eq_true.mp (valueCarryAudit steady) (ins,pos) hmem
  simp only [valueCarryCode,beq_eq_false_iff_ne.mpr hOrd,Bool.false_or,Bool.and_eq_true,
    Bool.not_eq_true'] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

private theorem ordinaryValueCarry {l : Launch} {X : Execution} {g pos : Nat}
    {s u : TState} {ev : Option Event}
    (steady : Bool) (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hExcept : s.pc ≠ valueBroadcast steady) (hs : valueCarries l X g steady pos s)
    (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    valueCarries l X g steady (pos + if ev.isSome then 1 else 0) u := by
  intro hLive
  have hCheck {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :=
    valueCarryCheck steady hLo hHi hExcept hc
  have hKeep : u.regs (valueDescriptorSite steady).output =
      s.regs (valueDescriptorSite steady).output := by
    apply mmaStepReg (by omega) hHi _ hw
    intro ins hc
    simpa using (hCheck hc).1
  have hCore := out_eq_core (show 1904 ≤ s.pc by omega) hHi (l := l) (g := g) (t := s)
  have hEdge : valuePreservedEdge steady s.pc u.pc = true := by
    rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
    · have hTau : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← hCore]
      obtain ⟨ins,hGet⟩ := tau_core_has_code hTau
      rcases tau_core_frame hGet hTau with rfl | h
      · exact (hCheck hGet).2.1
      have hPc := h.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra dst uni => simpa only [hOp,hPc] using (hCheck hGet).2.2
      case brx =>
        have hNo := (hCheck hGet).2.2
        simp only [hOp,Bool.false_eq_true] at hNo
      all_goals exact hPc.symm ▸ (hCheck hGet).2.1
    · obtain ⟨ins,hGet,_,_⟩ := estep_event_source he
      have heCore : EStep kernel [] l g s e (some u) := by
        obtain ⟨tm,hOut,hFire⟩ := he
        exact ⟨tm,hCore ▸ hOut,hFire⟩
      rcases (estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
      · rw [h]
        simp [valuePreservedEdge]
      · exact h.symm ▸ (hCheck hGet).2.1
  have hSource : valueLive steady s.pc := by
    simpa [valuePreservedEdge,hLive] using hEdge
  obtain ⟨use, j, hj, hMark, hReg, hCursor⟩ := hs hSource
  refine ⟨use, j, by omega, hMark, hKeep.trans hReg, ?_⟩
  rcases hw with ⟨rfl, _⟩ | ⟨e, rfl, hStep⟩
  · simpa using hCursor
  apply valueCursorQuietStep hCursor (hActual e rfl)
  rw [estep_source_pc hStep]
  cases steady
  · change 2559 < s.pc ∧ s.pc ≤ 2646 at hSource
    omega
  · change 2308 < s.pc ∧ s.pc ≤ 2533 at hSource
    omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem valueBroadcastStep (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (steady : Bool) {g index : Nat} (hWarp : warpIndex l g = 12) {s u : TState} {ev : Option Event}
    (hPc : s.pc = valueBroadcast steady) (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,index) = some e) :
    valueCarries l X g steady (index + if ev.isSome then 1 else 0) u := by
  let site := valueDescriptorSite steady
  have hc : kernel.code[s.pc]? = some ⟨none,
      .warp ⟨.shfl .idx,some (.int .b 32),[some site.output],
        [.reg site.input,.imm 0,.imm 31],some (.imm (-1))⟩⟩ := by
    rw [hPc]
    cases steady
    · exact Flow.code_2559
    · exact Flow.code_2308
  have hCore := out_eq_core (show 1904 ≤ s.pc by rw [hPc]; cases steady <;> decide)
    (show s.pc < 2768 by rw [hPc]; cases steady <;> decide) (l := l) (g := g) (t := s)
  rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · unfold Tau at ht
    rw [hCore] at ht
    exact (tau_core_not_event hc rfl ht).elim
  · obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hCode.symm.trans hc)
    obtain ⟨sent,b,c,recv,ok,rfl,rfl⟩ := fires_shfl (p := none) hFire
    have hGet := hActual _ rfl
    rw [hPc] at hGet
    obtain ⟨_, rfl, rfl, _⟩ :=
      Mma.actualValueDescriptorSentForReadyUse hp hX steady hWarp hGet
    obtain ⟨hValue, hOdd⟩ := Mma.actualValueDescriptorReceivedForReadyUse hp hX steady hWarp hGet
    let ready := Mma.atPrefix l X g index
    let use := ready.kvAcquires 0 + ready.kvAcquires 1 + ready.kvAcquires 2 - 1
    exact fun _ => ⟨use, index, by simp, ⟨⟨sent, ok, hValue ▸ hGet⟩, rfl, hOdd⟩,
      (Function.update_self _ _ _).trans (congrArg some hValue),
      valueCursorQuietStep (fun _ _ => rfl) hGet (by
        change valueBroadcast steady ≠ 2294 ∧ valueBroadcast steady ≠ 2545
        cases steady <;> decide)⟩

set_option maxRecDepth 100000 in
private theorem valueFrameExitFloor :
    (kernel.code.drop 2768).all (fun i => staysPastEvent 2768 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem valueFrameExitSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2768 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem valueFrameInWalk (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (steady : Bool) {g : Nat} (hWarp : warpIndex l g = 12) {s : TState} {events : List Event}
    {visits : List Visit} (hBounds : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) {base : Nat}
    (hF : valueCarries l X g steady base s) (hw : Walk kernel Assumptions.all l g s events visits)
    (hSuffix : events = (X.tr g).drop base) {e : Event} (he : e ∈ events) (hEarly : e.pc < 2768) :
    ∃ pos t o, t.pc = e.pc ∧ valueCarries l X g steady pos t ∧
      EStep kernel Assumptions.all l g t e o := by
  have advance {s u : TState} {events : List Event} {visits : List Visit}
      {r : Option Event} {pos : Nat} (hBounds : 1907 ≤ s.pc ∧ s.pc < 2768)
      (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) (hFr : valueCarries l X g steady pos s)
      (hStep : WStep kernel Assumptions.all l g s r u)
      (hWall : Walk kernel Assumptions.all l g u events visits) (hMem : e ∈ events)
      (hGet : ∀ f, r = some f → X.get (g,pos) = some f) :
      (1907 ≤ u.pc ∧ u.pc < 2768) ∧ (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧
        valueCarries l X g steady (pos + if r.isSome then 1 else 0) u := by
    obtain ⟨hNext,hShape⟩ := mmaCutStep hBounds.1 hBounds.2 hStep hs
    rcases hNext with hIn | ⟨hOut,_⟩
    swap
    · simp only [List.mem_singleton] at hOut
      exact (Nat.not_le_of_lt hEarly (eventTailEvents valueFrameExitFloor
        valueFrameExitSegments hWall (show 2768 ≤ u.pc by omega) e hMem)).elim
    refine ⟨hIn,hShape,?_⟩
    by_cases hAt : s.pc = valueBroadcast steady
    · exact valueBroadcastStep hp hX steady hWarp hAt hStep hGet
    · exact ordinaryValueCarry steady hBounds.1 hBounds.2 hAt hFr hStep hGet
  induction hw generalizing base with
  | stop => cases he
  | @tau s u events visits ht hw ih =>
    obtain ⟨hPc,hShape,hFrame⟩ := advance (pos := base) hBounds hs hF (.inl ⟨rfl,ht⟩) hw he
      (fun _ h => by cases h)
    exact ih hPc hShape hFrame hSuffix he
  | @ev s u first events visits hFirst hWalk ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨base,s,some u,(estep_source_pc hFirst).symm,hF,hFirst⟩
    have hGet : X.get (g,base) = some first := by
      change (X.tr g)[base]? = _
      rw [← Nat.add_zero base,← List.getElem?_drop,← hSuffix,List.getElem?_cons_zero]
    obtain ⟨hPc,hShape,hFrame⟩ := advance hBounds hs hF (.inr ⟨first,rfl,hFirst⟩) hWalk he
      (fun f h => Option.some.inj h ▸ hGet)
    have hDrop : events = (X.tr g).drop (base+1) := by
      rw [← List.drop_drop,← hSuffix]
      rfl
    exact ih hPc hShape hFrame hDrop he
  | last hLast =>
    obtain rfl := List.mem_singleton.mp he
    exact ⟨base,_,none,(estep_source_pc hLast).symm,hF,hLast⟩

private theorem pvRoleStart (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {block : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hGet : X.get (g,index) = some ⟨pvPc block step,.tc (.mma d op accum mask)⟩) :
    ∃ s visits, warpIndex l g = 12 ∧
      At s 1908 [(1062,b32 12),(2535,b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop 6) visits ∧ 6 ≤ index ∧
      ⟨pvPc block step,.tc (.mma d op accum mask)⟩ ∈ (X.tr g).drop 6 := by
  let ev : Event := ⟨pvPc block step,.tc (.mma d op accum mask)⟩
  change X.get (g,index) = some ev at hGet
  have hBounds : 1907 < ev.pc ∧ ev.pc < 2768 := by
    change 1907 < pvPc block step ∧ pvPc block step < 2768
    fin_cases block <;> fin_cases step <;> decide
  have hHint : ev.pc ∉ registerHintSites := by
    change pvPc block step ∉ registerHintSites
    fin_cases block <;> fin_cases step <;> decide
  have hRole := roleBodyPcOfEvent hp hX hGet (by omega) hHint
  have hWarp : warpIndex l g = 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  obtain ⟨s,visits,hIndex,hs,hw,_,_,_⟩ :=
    mmaRoleWalkOfDemand hp hX hGet hWarp (.inl hBounds.1)
  have hMem : ev ∈ (X.tr g).drop 6 := by
    apply List.mem_of_getElem? (i := index-6)
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  exact ⟨s,visits,hWarp,hs,hw,hIndex,hMem⟩
end

/-- Each actual PV contraction retains the V word returned by the lane-zero
broadcast in its current loop or tail visit. -/
theorem PvInstruction.valueWordAtIssue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {block : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hIssue : PvInstruction X issue block step d op accum mask) :
    ∃ (slot : Fin 3) (t u : TState),
      t.regs (pvSrcRegs block).2.2 = some (b32 (valueDescriptorLow l slot.val)) ∧
      EStep kernel Assumptions.all l issue.1 t
        ⟨pvPc block step,.tc (.mma d op accum mask)⟩ (some u) := by
  obtain ⟨g,index⟩ := issue
  let ev : Event := ⟨pvPc block step,.tc (.mma d op accum mask)⟩
  let steady : Bool := decide (block.val < 2)
  have hGet : X.get (g,index) = some ev := hIssue.decoded
  have hBounds : 1907 < ev.pc ∧ ev.pc < 2768 := by
    change 1907 < pvPc block step ∧ pvPc block step < 2768
    fin_cases block <;> fin_cases step <;> decide
  have hLive : valueLive steady ev.pc := by
    change valueLive steady (pvPc block step)
    fin_cases block <;> fin_cases step <;> decide
  obtain ⟨s,visits,hWarp,hs,hw,_,hMem⟩ := pvRoleStart hp hX hGet
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ by decide,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  have hInit : valueCarries l X g steady 6 s := by
    intro h
    rw [hs.1] at h
    have hNo : ¬ valueLive steady 1908 := by fin_cases block <;> decide
    exact (hNo h).elim
  obtain ⟨_,t,o,hPc,hCarrier,hEStep⟩ := valueFrameInWalk hp hX steady hWarp
    (by rw [hs.1]; decide) hShape hInit hw rfl hMem hBounds.2
  have hUse : (valueDescriptorSite steady).output = (pvSrcRegs block).2.2 := by
    fin_cases block <;> rfl
  obtain ⟨use, _, _, _, hWord, _⟩ := hCarrier (hPc.symm ▸ hLive)
  rw [hUse, ← valueSlotLow] at hWord
  cases o with
  | none =>
    obtain ⟨tm,_,hFires⟩ := hEStep
    rcases fires_none_ends hFires with ⟨_,h⟩ | h <;> cases h
  | some u => exact ⟨readyStage use,t,u,hWord,hEStep⟩

private def outsideValuePack (block : Fin 4) (step : Fin 8) (pos : Nat) : Prop :=
  pos ≤ valueIdSite block ∨ pvPc block step < pos

private instance (block : Fin 4) (step : Fin 8) (pos : Nat) :
    Decidable (outsideValuePack block step pos) := inferInstanceAs (Decidable (_ ∨ _))

private def valuePackSiteCode (block : Fin 4) (step : Fin 8) (pos : Nat) (i : Instr) : Bool :=
  !decide (outsideValuePack block step pos) || pos == valueIdSite block ||
    (decide (outsideValuePack block step (pos+1)) &&
      match i.op with
      | .bra dst _ => decide (outsideValuePack block step dst)
      | .brx .. => false
      | _ => true)

set_option maxRecDepth 100000 in
private theorem packSiteAudit (block : Fin 4) (step : Fin 8) :
    (((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907).all
      (fun (i,pos) => valuePackSiteCode block step pos i) = true := by
  fin_cases block <;> fin_cases step <;> kernel_rfl

private theorem packSiteCheck (block : Fin 4) (step : Fin 8) {pos : Nat} {i : Instr}
    (hLo : 1907 ≤ pos) (hHi : pos < 2768) (hOutside : outsideValuePack block step pos)
    (hSkip : pos ≠ valueIdSite block) (hCode : kernel.code[pos]? = some i) :
    outsideValuePack block step (pos+1) ∧
      (match i.op with
      | .bra dst _ => decide (outsideValuePack block step dst)
      | .brx .. => false
      | _ => true) = true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have hMem : (i,pos) ∈ code := by
    apply List.mem_of_getElem? (i := pos-1907)
    dsimp only [code]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hCode]
    rfl
  have h := List.all_eq_true.mp (packSiteAudit block step) (i,pos) hMem
  simpa only [valuePackSiteCode,decide_eq_true hOutside,Bool.not_true,
    beq_eq_false_iff_ne.mpr hSkip,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq] using h

private theorem ordinaryPackCursor {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (block : Fin 4) (step : Fin 8) (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hs : outsideValuePack block step s.pc) (hSkip : s.pc ≠ valueIdSite block)
    (hw : WStep kernel Assumptions.all l g s e u) : outsideValuePack block step u.pc := by
  have hAudit {i : Instr} (hc : kernel.code[s.pc]? = some i) :=
    packSiteCheck block step hLo hHi hs hSkip hc
  have hCore := out_eq_core (show 1904 ≤ s.pc by omega) hHi (l := l) (g := g) (t := s)
  rcases hw with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
  · have htCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← hCore]
    obtain ⟨i,hCode⟩ := tau_core_has_code htCore
    rcases tau_core_frame hCode htCore with rfl | hFrame
    · exact (hAudit hCode).1
    have hPc := hFrame.pc
    cases hOp : i.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
    case bra dst uni =>
      rw [hPc]
      exact of_decide_eq_true (by simpa only [hOp] using (hAudit hCode).2)
    case brx =>
      have h := (hAudit hCode).2
      simp only [hOp,Bool.false_eq_true] at h
    all_goals exact hPc.symm ▸ (hAudit hCode).1
  · have heCore : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm,hOut,hFire⟩ := he
      exact ⟨tm,hCore ▸ hOut,hFire⟩
    obtain ⟨i,hCode,_,_⟩ := estep_event_source he
    rcases (estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h.symm ▸ hs
    · exact h.symm ▸ (hAudit hCode).1

private theorem leavesValueIssue {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (block : Fin 4) (step : Fin 8) (hPc : s.pc = pvPc block step)
    (hw : WStep kernel Assumptions.all l g s e u) : outsideValuePack block step u.pc := by
  have hc : kernel.code[s.pc]? = some _ := hPc.symm ▸ pvCode block step
  right
  rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hRange : 1904 ≤ pvPc block step ∧ pvPc block step < 2768 := by
      fin_cases block <;> fin_cases step <;> decide
    have hCore := out_eq_core (hPc.symm ▸ hRange.1) (hPc.symm ▸ hRange.2)
      (l := l) (g := g) (t := s)
    unfold Tau at ht
    rw [hCore] at ht
    rcases tau_core_frame hc ht with rfl | hFrame
    · exact hPc.symm ▸ Nat.lt_succ_self _
    · have h := hFrame.pc
      change u.pc = s.pc+1 ∨ False at h
      rw [h.resolve_right id,hPc]
      exact Nat.lt_succ_self _
  · obtain ⟨i,hCode,_,hFire⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hCode.symm.trans hc)
    rw [fires_tcMmaTs hFire]
    exact hPc.symm ▸ Nat.lt_succ_self _

private theorem valuePackedInWalk {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (block : Fin 4) (step : Fin 8)
    {g : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 12)
    {s : TState} {es : List Event} {vs : List Visit}
    (hs : 1907 ≤ s.pc ∧ s.pc < 2768) (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hOutside : outsideValuePack block step s.pc)
    {base index : Nat} (hF : valueCarries l X g (decide (block.val < 2)) base s)
    (hw : Walk kernel Assumptions.all l g s es vs) (hSuffix : es = (X.tr g).drop base)
    (hBefore : base ≤ index)
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hActual : X.get (g,index) = some ⟨pvPc block step,.tc (.mma d op accum mask)⟩) :
    ∃ use j, j < index ∧ ValueDescriptorUse l X (g,j) (decide (block.val < 2)) use ∧
      op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 ∧ PvShape l g op ∧
      ValueReadyCursorStable X g j index := by
  let steady : Bool := decide (block.val < 2)
  let target : Event := ⟨pvPc block step,.tc (.mma d op accum mask)⟩
  let start := valueIdSite block
  have hDemand {atIndex : Nat} (hi : atIndex ≤ index) :
      ((X.tr g).drop atIndex)[index - atIndex]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hi]
    exact hActual
  have hMember {atIndex : Nat} {rest : List Event} (hRest : rest = (X.tr g).drop atIndex)
      (hi : atIndex ≤ index) : target ∈ rest := hRest.symm ▸ List.mem_of_getElem? (hDemand hi)
  have hTarget : target.pc < 2768 := by
    change pvPc block step < 2768
    fin_cases block <;> fin_cases step <;> decide
  have hSetup : 1909 < start ∧ start < target.pc := by
    change 1909 < valueIdSite block ∧ valueIdSite block < pvPc block step
    fin_cases block <;> fin_cases step <;> decide
  have hLive : valueLive steady start ∧ valueLive steady target.pc := by
    change valueLive steady (valueIdSite block) ∧ valueLive steady (pvPc block step)
    fin_cases block <;> fin_cases step <;> decide
  have hRegister : (valueDescriptorSite steady).output = (pvSrcRegs block).2.2 := by
    fin_cases block <;> rfl
  have hWord (use : Nat) : sharedDescriptorWord (kvStart l use+pvFragment step) 16384 =
      pvLow l use step+2^32*0x40004040 := by unfold sharedDescriptorWord pvLow pvFragment; omega
  generalize hCount : vs.length = fuel
  induction fuel using Nat.strong_induction_on generalizing s es vs base with
  | h fuel ih =>
    have next {v u : TState} {ev : Option Event} {rest : List Event} {post : List Visit}
        {pos : Nat} (hShort : post.length < fuel)
        (hv : 1907 ≤ v.pc ∧ v.pc < 2768) (hRole : RoleShape v ∧ v.regs 1062 = some (b32 12))
        (hFr : valueCarries l X g steady pos v) (hPermit : outsideValuePack block step u.pc)
        (hStep : WStep kernel Assumptions.all l g v ev u)
        (hWalk : Walk kernel Assumptions.all l g u rest post)
        (hBound : pos + (if ev.isSome then 1 else 0) ≤ index)
        (hGet : ∀ e, ev = some e → X.get (g,pos) = some e)
        (hRest : rest = (X.tr g).drop (pos+if ev.isSome then 1 else 0)) :
        ∃ use j, j < index ∧ ValueDescriptorUse l X (g,j) steady use ∧
          op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 ∧ PvShape l g op ∧
          ValueReadyCursorStable X g j index := by
      obtain ⟨hBounds,hShape⟩ := mmaCutStep hv.1 hv.2 hStep hRole
      rcases hBounds with hIn | ⟨hExit,_⟩
      · have hNew : valueCarries l X g steady (pos + if ev.isSome then 1 else 0) u := by
          by_cases h : v.pc = valueBroadcast steady
          · exact valueBroadcastStep hp hX steady hWarp h hStep hGet
          · exact ordinaryValueCarry steady hv.1 hv.2 h hFr hStep hGet
        exact ih post.length hShort hIn hShape hPermit hNew hWalk hRest hBound rfl
      · simp only [List.mem_singleton] at hExit
        exact (Nat.not_le_of_lt hTarget (eventTailEvents valueFrameExitFloor
          valueFrameExitSegments hWalk (show 2768 ≤ u.pc by omega) target
          (hMember hRest hBound))).elim
    have hMem := hMember hSuffix hBefore
    by_cases hStart : s.pc = start
    · obtain ⟨use, j, hj, hDescriptor, hSlot, hCursor⟩ := hF (hStart.symm ▸ hLive.1)
      rw [hRegister] at hSlot
      have hAt : At s (valueIdSite block)
          [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12)] :=
        ⟨hStart,hShape.1.2.2 (by rw [hStart]; omega),hShape.1.2.1,
          normalBeforeLaterEvent hw hMem (by rw [hStart]; exact hSetup.2),
          hSlot,hShape.2,trivial⟩
      obtain ⟨v,pre,rest,post,hSplit,hLen,hPacked,hWalk,hFound,hEarlier⟩ :=
        valuePackedPrefixRanged hp block use step hAt hw hMem le_rfl (by intro f h; cases h)
      let pos := base+pre.length
      have hRest : rest = (X.tr g).drop pos := by
        rw [← List.drop_drop,← hSuffix,hSplit,List.drop_append_length]
      have hIndex : pos ≤ index := by
        by_contra! h
        have hLength : index - base < pre.length := by dsimp [pos] at h; omega
        have hAtIndex := hDemand hBefore
        rw [← hSuffix, hSplit, List.getElem?_append_left hLength] at hAtIndex
        have hBad := hEarlier target (List.mem_of_getElem? hAtIndex)
        exact (Nat.lt_irrefl _ hBad.2)
      have hV : 1907 ≤ v.pc ∧ v.pc < 2768 := by
        rw [hPacked.1]
        change 1907 ≤ target.pc ∧ target.pc < 2768
        omega
      have hReg : v.regs (pvSite block).b =
          some (b64 (sharedDescriptorWord (kvStart l use+pvFragment step) 16384)) :=
        (hWord use).symm ▸ hPacked.2.2.2.2.1
      have hFront : (X.tr g).take pos = (X.tr g).take base ++ pre := by
        have hBase : ((X.tr g).take base).length = base := by
          rw [List.length_take, Nat.min_eq_left]
          exact hBefore.trans (len_of_get hActual).le
        conv_lhs => rw [← List.take_append_drop base (X.tr g), ← hSuffix, hSplit]
        simp only [List.take_append, hBase, pos, Nat.add_sub_cancel_left,
          List.take_append_of_le_length (show pre.length ≤ pre.length by rfl), List.take_length]
        rw [List.take_of_length_le (by rw [hBase]; omega)]
      have hNewCursor : ValueReadyCursorStable X g j pos := by
        intro gate hGate
        rw [hFront, List.countP_append, ← hCursor gate hGate]
        have hQuiet : pre.countP (readyAtSite gate) = 0 := by
          apply List.countP_eq_zero.mpr
          intro ev he
          obtain ⟨hLo, hHi⟩ := hEarlier ev he
          apply Bool.eq_false_iff.mp
          apply valueReadyMarkQuiet _ gate hGate
          rcases pvPackBetweenValueGates block step with h | h <;> omega
        rw [hQuiet, Nat.add_zero]
      have hKeep : valueCarries l X g steady pos v := by
        intro _
        refine ⟨use, j, by dsimp [pos]; omega, hDescriptor, ?_, hNewCursor⟩
        rw [hRegister]
        apply holds_mem hPacked.2.2.2.2
        simp [packedValueFrame,packedValueCarry]
      have hRole : RoleShape v ∧ v.regs 1062 = some (b32 12) := by
        refine ⟨⟨hPacked.2.1.symm ▸ by decide,hPacked.2.2.1,fun _ => hPacked.2.1⟩,?_⟩
        apply holds_mem hPacked.2.2.2.2
        simp [packedValueFrame,packedValueCarry]
      cases hWalk with
      | stop => cases hFound
      | tau ht hW =>
        have hStep : WStep kernel Assumptions.all l g _ none _ := .inl ⟨rfl,ht⟩
        exact next (pos := pos) (by simp at hLen; omega) hV hRole hKeep
          (leavesValueIssue block step hPacked.1 hStep) hStep hW (by simpa using hIndex)
          (fun _ h => by cases h) (by simpa using hRest)
      | @ev t u e tail visits he hW =>
        have hGet : X.get (g,pos) = some e := by
          change (X.tr g)[pos]? = _
          rw [← Nat.add_zero pos,← List.getElem?_drop,← hRest,List.getElem?_cons_zero]
        by_cases hThis : pos = index
        · have heq : e = target := Option.some.inj (hGet.symm.trans (hThis.symm ▸ hActual))
          subst e
          have hId := holds_mem hPacked.2.2.2.2 (show
            ((pvSite block).id,b32 0x8210490) ∈ packedValueFrame l block use step by
              simp [packedValueFrame,packedValueCarry])
          exact ⟨use, j, hj.trans_le hBefore, hDescriptor, pvIssueBOfRegister hp block step use
            hReg he, pvIssueShapeOfId hp hg hId he, hThis ▸ hNewCursor⟩
        have hTail : tail = (X.tr g).drop (pos+1) := by
          rw [← List.drop_drop,← hRest]
          rfl
        have hStep : WStep kernel Assumptions.all l g _ (some e) _ := .inr ⟨e,rfl,he⟩
        exact next (by simp at hLen; omega) hV hRole hKeep
          (leavesValueIssue block step hPacked.1 hStep) hStep hW (by simp; omega)
          (fun f h => Option.some.inj h ▸ hGet) hTail
      | last he =>
        obtain rfl := List.mem_singleton.mp hFound
        obtain ⟨tm,_,hFires⟩ := he
        rcases fires_none_ends hFires with ⟨_,h⟩ | h <;> cases h
    · have hSkip : s.pc ≠ target.pc := by
        change s.pc ≤ start ∨ target.pc < s.pc at hOutside
        omega
      cases hw with
      | stop => cases hMem
      | tau ht hW =>
        have hStep : WStep kernel Assumptions.all l g _ none _ := .inl ⟨rfl,ht⟩
        exact next (pos := base) (by simp at hCount; omega) hs hShape hF
          (ordinaryPackCursor block step hs.1 hs.2 hOutside hStart hStep) hStep hW
          (by simpa using hBefore) (fun _ h => by cases h) (by simpa using hSuffix)
      | @ev t u e tail visits he hW =>
        have hGet : X.get (g,base) = some e := by
          change (X.tr g)[base]? = _
          rw [← Nat.add_zero base,← List.getElem?_drop,← hSuffix,List.getElem?_cons_zero]
        have hIndex : base < index := by
          by_contra! h
          have hEq : base = index := by omega
          have hEv : e = target := Option.some.inj (hGet.symm.trans (hEq.symm ▸ hActual))
          exact hSkip (by rw [← hEv]; exact (estep_source_pc he).symm)
        have hTail : tail = (X.tr g).drop (base+1) := by
          rw [← List.drop_drop,← hSuffix]
          rfl
        have hStep : WStep kernel Assumptions.all l g _ (some e) _ := .inr ⟨e,rfl,he⟩
        exact next (by simp at hCount; omega) hs hShape hF
          (ordinaryPackCursor block step hs.1 hs.2 hOutside hStart hStep) hStep hW (by simp; omega)
          (fun f h => Option.some.inj h ▸ hGet) hTail
      | last he =>
        obtain rfl := List.mem_singleton.mp hMem
        exact (hSkip (estep_source_pc he).symm).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {issue : EvId} {block : Fin 4} {step : Fin 8}
include hp hX

/-- The actual B descriptor uses the V broadcast and ready ordinal of this fragment visit. -/
theorem PvInstruction.valueOperandUseAndReadyCursor {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hIssue : PvInstruction X issue block step d op accum mask) :
    ∃ use j, j < issue.2 ∧
      ValueDescriptorUse l X (issue.1,j) (decide (block.val < 2)) use ∧
      op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 ∧ PvShape l issue.1 op ∧
      ValueReadyCursorStable X issue.1 j issue.2 := by
  obtain ⟨g,index⟩ := issue
  obtain ⟨s,visits,hWarp,hs,hw,hBound,_⟩ := pvRoleStart hp hX hIssue.decoded
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ by decide,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  have hOutside : outsideValuePack block step s.pc := by
    rw [hs.1]
    left
    fin_cases block <;> decide
  have hInit : valueCarries l X g (decide (block.val < 2)) 6 s := by
    intro h
    rw [hs.1] at h
    have hNo : ¬ valueLive (decide (block.val < 2)) 1908 := by fin_cases block <;> decide
    exact (hNo h).elim
  exact valuePackedInWalk hp hX block step (event_thread_lt hX hIssue.decoded)
    hWarp (by rw [hs.1]; decide) hShape
    hOutside hInit hw rfl hBound hIssue.decoded

/-- The actual B descriptor retains the successful use of its value broadcast. -/
theorem PvInstruction.valueOperandUse {d : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hIssue : PvInstruction X issue block step d op accum mask) :
    ∃ use j, j < issue.2 ∧
      ValueDescriptorUse l X (issue.1,j) (decide (block.val < 2)) use ∧
      op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 ∧ PvShape l issue.1 op := by
  obtain ⟨use, j, hj, hDescriptor, hByte, hShape, _⟩ :=
    hIssue.valueOperandUseAndReadyCursor hp hX
  exact ⟨use, j, hj, hDescriptor, hByte, hShape⟩

omit hp hX in
/-- The ready acquire of a V descriptor is the acquire at its exact cache-use index. -/
theorem ValueDescriptorUse.readyBefore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index use : Nat} {steady : Bool} (hWarp : warpIndex l g = 12)
    (hUse : ValueDescriptorUse l X (g,index) steady use) :
    ∃ j, Mma.ReadyPoll l X g j (readyStage use) (readyWord use) true .cta ∧
      (((X.tr g).take j).filterMap readyEvent).length = use ∧
      TraceBefore X (g,j) (g,index) := by
  obtain ⟨⟨sent, valid, hEvent⟩, hUse, hOdd⟩ := hUse
  have hg := event_thread_lt hX hEvent
  have hCount := Mma.readyUsesAtPrefix hp hX hg hWarp index
  have hUsePos : 0 < use := by
    by_contra! hZero
    obtain rfl : use = 0 := Nat.eq_zero_of_le_zero hZero
    cases hOdd
  let count := (((X.tr g).take index).filterMap readyEvent).length
  have hUse' : use = count - 1 := hUse.trans (congrArg (· - 1) hCount.symm)
  have hBefore : use < count := by omega
  obtain ⟨j, hLt, hPoll, hRank⟩ := Mma.readyPollAtOrdinalBefore hp hX hg hWarp hBefore
  exact ⟨j, hPoll, hRank, rfl, hLt, len_of_get hEvent⟩

/-- The B descriptor addresses the physical V slot of its actual visit. -/
theorem PvInstruction.valueOperand {d : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hIssue : PvInstruction X issue block step d op accum mask) :
    ∃ slot : Fin 3, op.b = sharedDescriptor (kvStart l slot.val + pvFragment step) 16384 ∧
      PvShape l issue.1 op := by
  obtain ⟨use, _, _, _, hB, hShape⟩ := hIssue.valueOperandUse hp hX
  have hSlot : kvSlot (readyStage use).val = kvSlot use := by
    change (use % 3) % 3 = use % 3
    omega
  exact ⟨readyStage use, by simpa only [kvStart, hSlot] using hB, hShape⟩

/-- Every shared B byte of an actual PV fragment is inside its own CTA's V bank. -/
theorem PvInstruction.valueByteBank {d index : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} {loc : Loc} (hIssue : PvInstruction X issue block step d op accum mask)
    (hByte : op.byteLoc .b index = some loc) :
    SharedOperandRange l issue.1 loc ∧ l.sharedBase + 68608 ≤ loc.addr := by
  obtain ⟨slot,hB,hDescriptor,hLow,hHigh⟩ := hIssue.valueOperand hp hX
  have hSame : op.byteLoc .b index = (pvOperands l issue.1 block step slot.val).byteLoc .b index :=
    by simp only [TcMma.OperandSpec.byteLoc,pvOperands,hB,hDescriptor,hLow,hHigh,reduceCtorEq,
      false_and,↓reduceIte]; rfl
  exact pvOperandBankRange hp issue.1 block step slot.val (hSame.symm.trans hByte)

/-- The actual value byte lies within its CTA data banks. -/
theorem PvInstruction.valueByteRange {d index : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} {loc : Loc} (hIssue : PvInstruction X issue block step d op accum mask)
    (hByte : op.byteLoc .b index = some loc) : SharedOperandRange l issue.1 loc :=
  (hIssue.valueByteBank hp hX hByte).1

end
end PTX.Kernels.TmlFa4Fwd.Thread
