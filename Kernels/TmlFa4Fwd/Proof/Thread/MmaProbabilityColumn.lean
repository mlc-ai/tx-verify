-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveRanks
import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailDestination
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Lemmas.Flow.NotShfl
import Lemmas.Flow.TcTmpl
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

private def aSource (stage : Fin 2) : Nat := if stage = 0 then 2626 else 2628

private def aReply (stage : Fin 2) : Nat := if stage = 0 then 2611 else 2616

private def aCopy (stage : Fin 2) : Nat := if stage = 0 then 2565 else 2605

private abbrev tailBlock (stage : Fin 2) : Fin 4 := firstPvBlock false stage

private def aTemplate (col : Nat) : Tmpl → Prop
  | .tc (.mma _ op _ _) _ => op.aTmem = some col
  | .ub _ => True
  | _ => False

private theorem probabilityTemplate {l : Launch} {g d ta rb ri : Nat} {s : TState}
    {off : Int} {base col : Nat} {en : Opnd} (hg : g < l.threads) (hBase : base < 2^32)
    (hOffset : tmemOffset base off = .ok col) (hReg : s.regs ta = some (b32 base)) :
    aTemplate col (eventTmpl Assumptions.all l g s
      (.tcMma (.dense .one false .f16 d (.tmem ta off) (.reg rb) (.reg ri)
        (List.replicate 4 (.imm 0)) en))) := by
  have hRead := readBits_b32 (L := l) (g := g) hReg hBase
  have hNat := toNat_ofNat_lt (show base < 2^64 by omega)
  have hExec {r : Exec Tmpl} (h : AllOk (aTemplate col) r) : aTemplate col (ofExec r) := by
    cases r
    · trivial
    · exact h
  have hBind {α β : Type} (a : α) (f : α → Exec β) :
      (Except.ok a : Exec α) >>= f = f a := rfl
  simp only [eventTmpl,tcTmpl_tcMma_tmem (.inr (.inl rfl)),mmaTmemTmpl,hg,↓reduceIte]
  apply hExec
  apply allOk_bind
  intro dst
  simp only [hRead,hBind,hNat,hOffset]
  apply allOk_bind (r := readBits l g s 64 (.reg rb))
  intro b
  apply allOk_bind (r := readBits l g s 32 (.reg ri))
  intro id
  simp only [List.length_replicate,CtaGroup.size,Nat.reduceMul,↓reduceIte]
  apply allOk_bind (r := (List.replicate 4 (.imm 0 : Opnd)).mapM (readBits l g s 32))
  intro masks
  apply allOk_bind (r := mmaEnable s en)
  intro useAcc
  apply allOk_bind (r := zeroColumnMaskOk l g s none)
  intro zcm
  cases TcShared.decode b.toNat with
  | none => trivial
  | some dB =>
    cases TcMma.decode .one false .f16 id.toNat with
    | none => trivial
    | some desc =>
      simp only
      split
      · trivial
      · cases TcMma.makeOperands l (g/l.block) desc dB dB <;> simp only <;> trivial

private theorem firedProbabilityAddress {pc col d : Nat} {t : Tmpl} {u : Option TState}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : aTemplate col t) (hf : Fires pc t ⟨pc,.tc (.mma d op accum mask)⟩ u) :
    op.aTmem = some col := by
  cases t <;> simp only [aTemplate] at h
  case tc k _ =>
    cases k <;> try contradiction
    cases congrArg Event.kind hf.1
    exact h
  case ub => cases congrArg Event.kind hf.1

/-- The actual A operand includes the fragment displacement applied to its column register. -/
theorem pvProbabilityAddressOfRegister {l : Launch} {g : Nat} (hg : g < l.threads)
    (block : Fin 4) (step : Fin 8) {t : TState} {u : Option TState} {d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hReg : t.regs (pvSite block).a = some (b32 (probabilityColumn (pvSite block).stage)))
    (hStep : EStep kernel Assumptions.all l g t
      ⟨pvPc block step,.tc (.mma d op accum mask)⟩ u) :
    op.aTmem = some (probabilityColumn (pvSite block).stage+8*step.val) := by
  have hPc : t.pc = pvPc block step := (estep_source_pc hStep).symm
  obtain ⟨ins,hCode,hFires⟩ := mmaRoleEventSource hStep (by intro f h; contradiction)
  rw [hPc,pvCode block step] at hCode
  obtain rfl := Option.some.inj hCode
  rw [hPc] at hFires
  have hBase : probabilityColumn (pvSite block).stage < 2^32 := by fin_cases block <;> decide
  have hOffset : tmemOffset (probabilityColumn (pvSite block).stage) (8*(step.val : Int)) =
      .ok (probabilityColumn (pvSite block).stage+8*step.val) := pvAOffset (pvSite block).stage step
  exact firedProbabilityAddress (probabilityTemplate hg hBase hOffset hReg) hFires

private theorem regAfterLocal {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    {pos r : Nat} {facts : List (Nat × Value)} {value : Value}
    (hLo : 1904 ≤ pos) (hHi : pos+1 ≤ 2768)
    (hSeg : Seg kernel [] l g 1 pos facts (pos+1) [(r,value)])
    (hs : At s pos facts) (hw : WStep kernel Assumptions.all l g s ev u) :
    u.regs r = some value := by
  exact (mmaRoleLocalStepAt hLo hHi hSeg hs hw).2.2.2.2.2.1

set_option maxRecDepth 100000 in
private theorem sourceAudit (stage : Fin 2) :
    MmaLiveRegAudit (tailProbabilityColumnShuffleSite stage)
      (tailProbabilityColumnShuffleSite stage) (aSource stage) := by fin_cases stage <;> kernel_rfl

private theorem sourceLocal (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel [] l g 1 (tailProbabilityColumnShuffleSite stage-1) []
      (tailProbabilityColumnShuffleSite stage-1+1)
      [(aSource stage,b32 (probabilityColumn stage))] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

private theorem sourceStep {l : Launch} {g : Nat} (stage : Fin 2)
    {s u : TState} {ev : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hs : MmaLiveReg (tailProbabilityColumnShuffleSite stage)
      (tailProbabilityColumnShuffleSite stage) (aSource stage) (b32 (probabilityColumn stage)) s)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    MmaLiveReg (tailProbabilityColumnShuffleSite stage) (tailProbabilityColumnShuffleSite stage)
      (aSource stage) (b32 (probabilityColumn stage)) u := by
  by_cases hPos : s.pc+1 = tailProbabilityColumnShuffleSite stage
  · have hp : s.pc = tailProbabilityColumnShuffleSite stage-1 := by omega
    have hAt : At s (tailProbabilityColumnShuffleSite stage-1) [] :=
      ⟨hp,hShape.1.2.2 (by rw [hp]; fin_cases stage <;> decide),
        hShape.1.2.1,mmaRoleReturningNormal (by omega) hHi hw,trivial⟩
    exact fun _ _ => regAfterLocal (by fin_cases stage <;> decide)
      (by fin_cases stage <;> decide) (sourceLocal l g stage) hAt hw
  · exact mmaRoleLiveRegStep (sourceAudit stage) hLo hHi hPos hs hw

private theorem probabilityShuffleCode (stage : Fin 2) :
    kernel.code[tailProbabilityColumnShuffleSite stage]? = some ⟨none,
      .warp ⟨.shfl .idx,some (.int .b 32),[some (aReply stage)],
        [.reg (aSource stage),.imm 0,.imm 31],some (.imm (-1))⟩⟩ := by
  fin_cases stage
  · exact Flow.code_2558
  · exact Flow.code_2599

private theorem sourceAtShuffle {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {g index : Nat} {sent recv : Value} {a b : Nat} {ok : Bool}
    (he : X.get (g,index) =
      some ⟨tailProbabilityColumnShuffleSite stage,.shfl .idx sent a b recv ok⟩) :
    sent = b32 (probabilityColumn stage) := by
  have hBounds : 1907 < tailProbabilityColumnShuffleSite stage ∧
      tailProbabilityColumnShuffleSite stage < 2768 ∧
      tailProbabilityColumnShuffleSite stage ∉ registerHintSites := by fin_cases stage <;> decide
  obtain ⟨t,u,ht,hFire⟩ := mmaRoleReplayOfEvent hp hX he
    (mmaRoleEventWarp hp hX he hBounds.1 hBounds.2.1 hBounds.2.2) hBounds.1 hBounds.2.1
    (fun _ => MmaLiveReg (tailProbabilityColumnShuffleSite stage)
      (tailProbabilityColumnShuffleSite stage) (aSource stage) (b32 (probabilityColumn stage)))
    (by
      intro s hs hlo
      rw [hs] at hlo
      have hNot : ¬ tailProbabilityColumnShuffleSite stage ≤ 1908 := by fin_cases stage <;> decide
      exact (hNot hlo).elim)
    (fun hlo hhi hShape hReg hw _ => sourceStep stage hlo hhi hShape hReg hw)
  have hPc : t.pc = tailProbabilityColumnShuffleSite stage := (estep_source_pc hFire).symm
  obtain ⟨ins,hCode,hf⟩ := mmaRoleEventSource hFire (by intro f h; contradiction)
  rw [hPc,probabilityShuffleCode stage] at hCode
  obtain rfl := Option.some.inj hCode
  obtain ⟨received,valid,hEq⟩ := fires_shfl_idx (p := none)
    (ht hPc.ge hPc.le) hf rfl
  exact (Kind.shfl.inj (congrArg Event.kind hEq)).2.1


set_option maxRecDepth 100000 in
private theorem replyAudit (stage : Fin 2) :
    MmaLiveRegAudit (tailProbabilityColumnShuffleSite stage+1) (aCopy stage) (aReply stage) := by
  fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem aRegisterAudit (stage : Fin 2) :
    MmaLiveRegAudit (aCopy stage+1) (pvPc (tailBlock stage) 7)
      (pvSite (tailBlock stage)).a := by fin_cases stage <;> kernel_rfl

private theorem replyAtStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {g index : Nat} (hWarp : warpIndex l g = 12) {s u : TState} {ev : Option Event}
    (hs : s.pc = tailProbabilityColumnShuffleSite stage)
    (hSent : s.regs (aSource stage) = some (b32 (probabilityColumn stage)))
    (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,index) = some e) :
    u.regs (aReply stage) = some (b32 (probabilityColumn stage)) := by
  have hCode := hs.symm ▸ probabilityShuffleCode stage
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
        some ⟨tailProbabilityColumnShuffleSite stage,.shfl .idx sent 0 31 recv ok⟩ := by
      obtain ⟨res,valid,hEvent⟩ := fires_shfl_idx (p := none) hSent hFire rfl
      obtain ⟨_,_,ha,hb,_,_⟩ := Kind.shfl.inj (congrArg Event.kind hEvent)
      simpa only [ha,hb] using hGet
    let ordinal := ((X.tr g).take index).countP Execution.isShfl
    have hRank : X.ShflK (g,index) ordinal := ⟨⟨_,_,_,_,_,_,_,hRecv⟩,rfl⟩
    obtain ⟨j,a',b',reply,valid,_,hPeer⟩ :=
      tailProbabilityColumnShuffleSource hp hX stage hWarp hRecv hRank
    exact (Function.update_self _ _ _).trans (congrArg some (sourceAtShuffle hp hX stage hPeer))

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem aRegisterLocal (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel [] l g 1 (aCopy stage) [(aReply stage,b32 (probabilityColumn stage))]
      (aCopy stage+1) [((pvSite (tailBlock stage)).a,b32 (probabilityColumn stage))] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

private theorem aAtIssue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {g index d : Nat} {step : Fin 8} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (he : X.get (g,index) = some ⟨pvPc (tailBlock stage) step,.tc (.mma d op accum mask)⟩) :
    op.aTmem = some (probabilityColumn stage+8*step.val) := by
  let block := tailBlock stage
  let shuffle := tailProbabilityColumnShuffleSite stage
  let col := b32 (probabilityColumn stage)
  have hBounds : 1907 < pvPc block step ∧ pvPc block step < 2768 ∧
      pvPc block step ∉ registerHintSites := by fin_cases stage <;> fin_cases step <;> decide
  have hWarp := mmaRoleEventWarp hp hX he hBounds.1 hBounds.2.1 hBounds.2.2
  let source := MmaLiveReg shuffle shuffle (aSource stage) col
  let reply := MmaLiveReg (shuffle+1) (aCopy stage) (aReply stage) col
  let stored := MmaLiveReg (aCopy stage+1) (pvPc block 7) (pvSite block).a col
  let Inv := fun (_ : Nat) (s : TState) => source s ∧ reply s ∧ stored s
  obtain ⟨t,u,hInv,hFire⟩ := mmaRoleReplayOfEvent hp hX he hWarp hBounds.1 hBounds.2.1 Inv
    (by
      intro s hs
      change source s ∧ reply s ∧ stored s
      have hBefore : 1908 < shuffle ∧ 1908 < aCopy stage := by fin_cases stage <;> decide
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
      · by_cases hs : s.pc = aCopy stage
        · have hLower : shuffle+1 ≤ s.pc := by rw [hs]; fin_cases stage <;> decide
          have hAt : At s (aCopy stage) [(aReply stage,col)] :=
            ⟨hs,hShape.1.2.2 (by rw [hs]; fin_cases stage <;> decide),hShape.1.2.1,
              mmaRoleReturningNormal (by omega) hHi hw,⟨hFrame.2.1 hLower hs.le,trivial⟩⟩
          exact fun _ _ => regAfterLocal (by fin_cases stage <;> decide)
            (by fin_cases stage <;> decide) (aRegisterLocal l g stage) hAt hw
        · exact mmaRoleLiveRegStep (aRegisterAudit stage) hLo hHi
            (Nat.succ_ne_succ_iff.mpr hs) hFrame.2.2 hw)
  have ht : t.pc = pvPc block step := (estep_source_pc hFire).symm
  have hLive : aCopy stage+1 ≤ pvPc block step ∧ pvPc block step ≤ pvPc block 7 := by
    fin_cases stage <;> fin_cases step <;> decide
  have hStage : (pvSite block).stage = stage := by fin_cases stage <;> rfl
  have hReg := hInv.2.2 (ht.symm ▸ hLive.1) (ht.symm ▸ hLive.2)
  have hColumn := pvProbabilityAddressOfRegister (event_thread_lt hX he) block step
    (hStage.symm ▸ hReg) hFire
  simpa only [hStage] using hColumn


/-- An actual tail PV fragment selects its eight probability columns in Tensor Memory. -/
theorem PvInstruction.tailProbabilityAddress {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {i : EvId} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat}
    (hIssue : PvInstruction X i (firstPvBlock false stage) step d op accum mask) :
    op.aTmem = some (probabilityColumn stage+8*step.val) :=
  aAtIssue hp hX stage hIssue.decoded

end PTX.Kernels.TmlFa4Fwd.Thread
