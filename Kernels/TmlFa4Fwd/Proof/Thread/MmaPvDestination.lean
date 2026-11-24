-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveRanks
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRoleReplay
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Flow.NotShfl
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

private def outSource (stage : Fin 2) : Nat := if stage = 0 then 2583 else 2598

private def outReply (stage : Fin 2) : Nat := if stage = 0 then 2570 else 2596

private def outCopy (stage : Fin 2) : Nat := steadyOutputShuffleSite stage+3

private abbrev steadyBlock (stage : Fin 2) : Fin 4 := firstPvBlock true stage

def mmaKeepsLiveEdge (lo hi src dest : Nat) : Bool :=
  !decide (lo ≤ dest ∧ dest ≤ hi) || decide (lo ≤ src ∧ src ≤ hi)

def mmaLiveRegCode (lo hi reg pos : Nat) (ins : Instr) : Bool :=
  pos+1 == lo ||
    (!(mmaWrites ins.op).contains reg && mmaKeepsLiveEdge lo hi pos (pos+1) &&
      match ins.op with
      | .bra dest _ => mmaKeepsLiveEdge lo hi pos dest
      | .brx .. => false
      | _ => true)

/-- The decoded role preserves the register on edges entering its live interval. -/
def MmaLiveRegAudit (lo hi reg : Nat) : Prop :=
  (((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907).all
    (fun (ins,pos) => mmaLiveRegCode lo hi reg pos ins) = true

private theorem liveRegCheck {lo hi reg pos : Nat} {ins : Instr}
    (audit : MmaLiveRegAudit lo hi reg) (hLo : 1907 ≤ pos) (hHi : pos < 2768)
    (hOrd : pos+1 ≠ lo) (hc : kernel.code[pos]? = some ins) :
    (mmaWrites ins.op).contains reg = false ∧ mmaKeepsLiveEdge lo hi pos (pos+1) = true ∧
      (match ins.op with
      | .bra dest _ => mmaKeepsLiveEdge lo hi pos dest
      | .brx .. => false
      | _ => true) = true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have hMem : (ins,pos) ∈ code := by
    apply List.mem_of_getElem? (i := pos-1907)
    dsimp only [code]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hc]
    rfl
  have h := List.all_eq_true.mp audit (ins,pos) hMem
  simp only [mmaLiveRegCode,beq_eq_false_iff_ne.mpr hOrd,Bool.false_or,Bool.and_eq_true,
    Bool.not_eq_true'] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

/-- The register has the given value throughout this live interval. -/
def MmaLiveReg (lo hi reg : Nat) (word : Value) (s : TState) : Prop :=
  lo ≤ s.pc → s.pc ≤ hi → s.regs reg = some word

section
variable {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}

/-- An entered live interval is reached through its defining instruction or from within it. -/
theorem mmaRoleLiveSource {lo hi reg : Nat} (audit : MmaLiveRegAudit lo hi reg) (hLo : 1907 ≤ s.pc)
    (hHi : s.pc < 2768) (hOrd : s.pc+1 ≠ lo) (hw : WStep kernel Assumptions.all l g s ev u)
    (hLow : lo ≤ u.pc) (hHigh : u.pc ≤ hi) : lo ≤ s.pc ∧ s.pc ≤ hi := by
  have hCheck {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :=
    liveRegCheck audit hLo hHi hOrd hc
  have hCore := out_eq_core (show 1904 ≤ s.pc by omega) hHi (l := l) (g := g) (t := s)
  have hEdge : mmaKeepsLiveEdge lo hi s.pc u.pc = true := by
    rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
    · have hTau : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← hCore]
      obtain ⟨ins,hGet⟩ := tau_core_has_code hTau
      rcases tau_core_frame hGet hTau with rfl | h
      · exact (hCheck hGet).2.1
      have hPc := h.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra dest uni => simpa only [hOp,hPc] using (hCheck hGet).2.2
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
        simp [mmaKeepsLiveEdge]
        omega
      · exact h.symm ▸ (hCheck hGet).2.1
  simpa [mmaKeepsLiveEdge,hLow,hHigh] using hEdge

/-- An ordinary returning step preserves a live register after its defining instruction. -/
theorem mmaRoleLiveRegStep {lo hi reg : Nat} {word : Value} (audit : MmaLiveRegAudit lo hi reg)
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768) (hOrd : s.pc+1 ≠ lo) (hs : MmaLiveReg lo hi reg word s)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    MmaLiveReg lo hi reg word u := by
  intro hLow hHigh
  have hCheck {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :=
    liveRegCheck audit hLo hHi hOrd hc
  have hKeep : u.regs reg = s.regs reg := by
    apply mmaStepReg (by omega) hHi _ hw
    intro ins hc
    simpa using (hCheck hc).1
  obtain ⟨hLeft,hRight⟩ := mmaRoleLiveSource audit hLo hHi hOrd hw hLow hHigh
  exact hKeep.trans (hs hLeft hRight)

/-- Returning MMA role steps originate in states that can execute an instruction. -/
theorem mmaRoleReturningNormal (hLo : 1904 ≤ s.pc) (hHi : s.pc < 2768)
    (hw : WStep kernel Assumptions.all l g s ev u) : s.fault = none := by
  cases hf : s.fault with
  | none => rfl
  | some f =>
    have hc := out_eq_core hLo hHi (l := l) (g := g) (t := s)
    have ho : out kernel Assumptions.all l g s = .ev (.ub f) := by rw [hc]; simp [out,hf]
    rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,tm,hOut,hFire⟩
    · exact False.elim (Out.noConfusion (ho.symm.trans ht))
    · obtain rfl := Out.ev.inj (ho.symm.trans hOut)
      cases hFire.2

/-- A returning step agrees with its verified one-instruction local segment. -/
theorem mmaRoleLocalStepAt {pc : Nat} {facts output : List (Nat × Value)} (hLo : 1904 ≤ pc)
    (hHi : pc+1 ≤ 2768) (hSeg : Seg kernel [] l g 1 pc facts (pc+1) output) (hs : At s pc facts)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    ev = none ∧ At u (pc+1) output := by
  obtain ⟨t,hr,ht⟩ := hSeg s hs
  have hTau := tauStep_iff.mp (by
    simpa [run] using localRun hLo hHi hs.1 rfl hr :
      tauStep kernel Assumptions.all l g s = some t)
  rcases hw with ⟨rfl,hu⟩ | ⟨e,rfl,hu⟩
  · obtain rfl := Out.tau.inj (hTau.symm.trans hu)
    exact ⟨rfl,ht⟩
  · exact (not_tau_of_stops (stops_of_estep hu) hTau).elim

private theorem regAfterLocal {pos r : Nat} {facts : List (Nat × Value)} {value : Value}
    (hLo : 1904 ≤ pos) (hHi : pos+1 ≤ 2768)
    (hSeg : Seg kernel [] l g 1 pos facts (pos+1) [(r,value)]) (hs : At s pos facts)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    u.regs r = some value := by
  exact (mmaRoleLocalStepAt hLo hHi hSeg hs hw).2.2.2.2.2.1
end

set_option maxRecDepth 100000 in
private theorem sourceAudit (stage : Fin 2) :
    MmaLiveRegAudit (steadyOutputShuffleSite stage) (steadyOutputShuffleSite stage)
      (outSource stage) := by fin_cases stage <;> kernel_rfl

private theorem sourceLocal (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel [] l g 1 (steadyOutputShuffleSite stage-1) []
      (steadyOutputShuffleSite stage-1+1) [(outSource stage,b32 (outputColumn stage))] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

private theorem sourceStep {l : Launch} {g : Nat} (stage : Fin 2)
    {s u : TState} {ev : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hs : MmaLiveReg (steadyOutputShuffleSite stage) (steadyOutputShuffleSite stage)
      (outSource stage) (b32 (outputColumn stage)) s)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    MmaLiveReg (steadyOutputShuffleSite stage) (steadyOutputShuffleSite stage)
      (outSource stage) (b32 (outputColumn stage)) u := by
  by_cases hPos : s.pc+1 = steadyOutputShuffleSite stage
  · have hp : s.pc = steadyOutputShuffleSite stage-1 := by omega
    have hAt : At s (steadyOutputShuffleSite stage-1) [] :=
      ⟨hp,hShape.1.2.2 (by rw [hp]; fin_cases stage <;> decide),
        hShape.1.2.1,mmaRoleReturningNormal (by omega) hHi hw,trivial⟩
    exact fun _ _ => regAfterLocal (by fin_cases stage <;> decide)
      (by fin_cases stage <;> decide) (sourceLocal l g stage) hAt hw
  · exact mmaRoleLiveRegStep (sourceAudit stage) hLo hHi hPos hs hw

private theorem outputShuffleCode (stage : Fin 2) :
    kernel.code[steadyOutputShuffleSite stage]? = some ⟨none,
      .warp ⟨.shfl .idx,some (.int .b 32),[some (outReply stage)],
        [.reg (outSource stage),.imm 0,.imm 31],some (.imm (-1))⟩⟩ := by
  fin_cases stage
  · exact Flow.code_2310
  · exact Flow.code_2425

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The observed event belongs to the MMA warp given its decoded role instruction. -/
theorem mmaRoleEventWarp (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e) (hLo : 1907 < e.pc)
    (hHi : e.pc < 2768) (hHint : e.pc ∉ registerHintSites) :
    warpIndex l g = 12 := by
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  unfold roleBodyPc at hRole
  rcases hRole with hExit | hBody
  · omega
  · split_ifs at hBody <;> omega

/-- Replay a frame from the actual warp-12 entry to the exact observed event. -/
theorem mmaRoleReplayOfEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e) (hWarp : warpIndex l g = 12)
    (hLo : 1907 < e.pc) (hHi : e.pc < 2768) (Inv : Nat → TState → Prop)
    (hInit : ∀ s, s.pc = 1908 → Inv 6 s)
    (hStep : ∀ {s u : TState} {ev : Option Event} {pos : Nat},
      1907 ≤ s.pc → s.pc < 2768 → (RoleShape s ∧ s.regs 1062 = some (b32 12)) →
      Inv pos s → WStep kernel Assumptions.all l g s ev u →
      (∀ e', ev = some e' → X.get (g,pos) = some e') →
      Inv (pos+ev.toList.length) u) :
    ∃ t u, Inv index t ∧ EStep kernel Assumptions.all l g t e u := by
  obtain ⟨s,visits,hIndex,hs,hw,_,_,_⟩ := mmaRoleWalkOfDemand hp hX he hWarp (.inl hLo)
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ by decide,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  exact mmaRoleReplayAt Inv hStep (by rw [hs.1]; decide) hShape (hInit s hs.1) hw hIndex he hHi

private theorem sourceAtShuffle (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index : Nat} {sent recv : Value} {a b : Nat} {ok : Bool}
    (he : X.get (g,index) = some ⟨steadyOutputShuffleSite stage,.shfl .idx sent a b recv ok⟩) :
    sent = b32 (outputColumn stage) := by
  have hBounds : 1907 < steadyOutputShuffleSite stage ∧ steadyOutputShuffleSite stage < 2768 ∧
      steadyOutputShuffleSite stage ∉ registerHintSites := by fin_cases stage <;> decide
  obtain ⟨t,u,ht,hFire⟩ := mmaRoleReplayOfEvent hp hX he
    (mmaRoleEventWarp hp hX he hBounds.1 hBounds.2.1 hBounds.2.2) hBounds.1 hBounds.2.1
    (fun _ => MmaLiveReg (steadyOutputShuffleSite stage) (steadyOutputShuffleSite stage)
      (outSource stage) (b32 (outputColumn stage)))
    (by
      intro s hs hlo
      rw [hs] at hlo
      have hNot : ¬ steadyOutputShuffleSite stage ≤ 1908 := by fin_cases stage <;> decide
      exact (hNot hlo).elim)
    (fun hlo hhi hShape hReg hw _ => sourceStep stage hlo hhi hShape hReg hw)
  have hPc : t.pc = steadyOutputShuffleSite stage := (estep_source_pc hFire).symm
  obtain ⟨ins,hCode,hf⟩ := mmaRoleEventSource hFire (by intro f h; contradiction)
  rw [hPc,outputShuffleCode stage] at hCode
  obtain rfl := Option.some.inj hCode
  obtain ⟨received,valid,hEq⟩ := fires_shfl_idx (p := none)
    (ht hPc.ge hPc.le) hf rfl
  exact (Kind.shfl.inj (congrArg Event.kind hEq)).2.1


set_option maxRecDepth 100000 in
private theorem replyAudit (stage : Fin 2) :
    MmaLiveRegAudit (steadyOutputShuffleSite stage+1) (outCopy stage) (outReply stage) := by
  fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem destinationAudit (stage : Fin 2) :
    MmaLiveRegAudit (outCopy stage+1) (pvPc (steadyBlock stage) 7)
      (pvSite (steadyBlock stage)).dst := by fin_cases stage <;> kernel_rfl

private theorem replyAtStep (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index : Nat} (hWarp : warpIndex l g = 12) {s u : TState} {ev : Option Event}
    (hs : s.pc = steadyOutputShuffleSite stage)
    (hSent : s.regs (outSource stage) = some (b32 (outputColumn stage)))
    (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,index) = some e) :
    u.regs (outReply stage) = some (b32 (outputColumn stage)) := by
  have hCode := hs.symm ▸ outputShuffleCode stage
  have hLo : 1904 ≤ s.pc := by rw [hs]; fin_cases stage <;> decide
  have hHi : s.pc < 2768 := by rw [hs]; fin_cases stage <;> decide
  rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · unfold Tau at ht
    rw [out_eq_core hLo hHi] at ht
    exact (tau_core_not_event hCode rfl ht).elim
  · obtain ⟨ins,hc,_,hFire⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hCode)
    obtain ⟨sent,a,b,recv,ok,rfl,rfl⟩ := fires_shfl (p := none) hFire
    have hGet := hActual _ rfl
    rw [hs] at hGet
    have hRecv : X.get (g,index) =
        some ⟨steadyOutputShuffleSite stage,.shfl .idx sent 0 31 recv ok⟩ := by
      obtain ⟨res,valid,hEvent⟩ := fires_shfl_idx (p := none) hSent hFire rfl
      obtain ⟨_,_,ha,hb,_,_⟩ := Kind.shfl.inj (congrArg Event.kind hEvent)
      simpa only [ha,hb] using hGet
    let ordinal := ((X.tr g).take index).countP Execution.isShfl
    have hRank : X.ShflK (g,index) ordinal := ⟨⟨_,_,_,_,_,_,_,hRecv⟩,rfl⟩
    obtain ⟨j,a',b',reply,valid,_,hPeer⟩ :=
      steadyOutputShuffleSource hp hX stage hWarp hRecv hRank
    exact (Function.update_self _ _ _).trans (congrArg some (sourceAtShuffle hp hX stage hPeer))

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem destinationLocal (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel [] l g 1 (outCopy stage) [(outReply stage,b32 (outputColumn stage))]
      (outCopy stage+1) [((pvSite (steadyBlock stage)).dst,b32 (outputColumn stage))] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

private theorem destinationAtIssue (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index d : Nat} {step : Fin 8} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat}
    (he : X.get (g,index) = some ⟨pvPc (steadyBlock stage) step,.tc (.mma d op accum mask)⟩) :
    d = outputColumn stage := by
  let block := steadyBlock stage
  let shuffle := steadyOutputShuffleSite stage
  let col := b32 (outputColumn stage)
  have hBounds : 1907 < pvPc block step ∧ pvPc block step < 2768 ∧
      pvPc block step ∉ registerHintSites := by fin_cases stage <;> fin_cases step <;> decide
  have hWarp := mmaRoleEventWarp hp hX he hBounds.1 hBounds.2.1 hBounds.2.2
  let source := MmaLiveReg shuffle shuffle (outSource stage) col
  let reply := MmaLiveReg (shuffle+1) (outCopy stage) (outReply stage) col
  let stored := MmaLiveReg (outCopy stage+1) (pvPc block 7) (pvSite block).dst col
  let Inv := fun (_ : Nat) (s : TState) => source s ∧ reply s ∧ stored s
  obtain ⟨t,u,hInv,hFire⟩ := mmaRoleReplayOfEvent hp hX he hWarp hBounds.1 hBounds.2.1 Inv
    (by
      intro s hs
      change source s ∧ reply s ∧ stored s
      have hBefore : 1908 < shuffle ∧ 1908 < outCopy stage := by fin_cases stage <;> decide
      refine ⟨fun h _ => ?_,fun h _ => ?_,fun h _ => ?_⟩ <;>
        rw [hs] at h <;> omega)
    (by
      intro s u ev pos hLo hHi hShape hFrame hw hActual
      change source s ∧ reply s ∧ stored s at hFrame
      change source u ∧ reply u ∧ stored u
      refine ⟨sourceStep stage hLo hHi hShape hFrame.1 hw,?_,?_⟩
      · by_cases hs : s.pc = shuffle
        · exact fun _ _ => replyAtStep hp hX stage hWarp hs (hFrame.1 hs.ge hs.le) hw hActual
        · exact mmaRoleLiveRegStep (replyAudit stage) hLo hHi (by omega) hFrame.2.1 hw
      · by_cases hs : s.pc = outCopy stage
        · have hLower : shuffle+1 ≤ s.pc := by rw [hs]; fin_cases stage <;> decide
          have hAt : At s (outCopy stage) [(outReply stage,col)] :=
            ⟨hs,hShape.1.2.2 (by rw [hs]; fin_cases stage <;> decide),hShape.1.2.1,
              mmaRoleReturningNormal (by omega) hHi hw,⟨hFrame.2.1 hLower hs.le,trivial⟩⟩
          exact fun _ _ => regAfterLocal (by fin_cases stage <;> decide)
            (by fin_cases stage <;> decide) (destinationLocal l g stage) hAt hw
        · exact mmaRoleLiveRegStep (destinationAudit stage) hLo hHi
            (Nat.succ_ne_succ_iff.mpr hs) hFrame.2.2 hw)
  have ht : t.pc = pvPc block step := (estep_source_pc hFire).symm
  have hLive : outCopy stage+1 ≤ pvPc block step ∧ pvPc block step ≤ pvPc block 7 := by
    fin_cases stage <;> fin_cases step <;> decide
  exact pvDestinationOfRegister (event_thread_lt hX he) block step
    (by fin_cases stage <;> decide) (hInv.2.2 (ht.symm ▸ hLive.1) (ht.symm ▸ hLive.2)) hFire

/-- Every PV stage writes the same output column in each steady and tail visit. -/
theorem PvInstruction.outputDestination (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {issue : EvId} {block : Fin 4} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : PvInstruction X issue block step d op accum mask) :
    d = outputColumn (pvSite block).stage := by
  fin_cases block
  · exact destinationAtIssue hp hX 0 hIssue.decoded
  · exact destinationAtIssue hp hX 1 hIssue.decoded
  · exact hIssue.tailOutputDestination hp hX 0
  · exact hIssue.tailOutputDestination hp hX 1

/-- The physical result layout of each actual PV fragment, with the issuing CTA and stage. -/
theorem PvInstruction.outputCell (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {block : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hIssue : PvInstruction X issue block step d op accum mask)
    (row col : Fin 128) : TcMma.resultCell op d row.val col.val =
      some ⟨issue.1/l.block,row.val,outputColumn (pvSite block).stage+col.val⟩ := by
  obtain ⟨_,_,hShape,hCta,_⟩ := hIssue.valueOperand hp hX
  rw [hIssue.outputDestination hp hX, pvResultCell hShape, hCta]

end PTX.Kernels.TmlFa4Fwd.Thread
