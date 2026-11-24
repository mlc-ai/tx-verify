-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityColumn
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveRanks
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleExit
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Lemmas.Flow.NotShfl
import Lemmas.Flow.Next
import Lemmas.Flow.PollRendezvous

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

private structure ProbabilitySend where
  pc : Nat
  source : Nat
  reply : Nat
  alignPc : Nat
  alignSource : Nat
  alignReply : Nat
  copyPc : Nat

private def steadyProbabilitySend : Fin 2 → ProbabilitySend
  | 0 => ⟨2307,2582,2569,2308,2581,2595,2314⟩
  | _ => ⟨2423,2597,2594,2425,2598,2596,2429⟩

private def shflIdxOp (src dst : Nat) : Op := .warp
  ⟨.shfl .idx,some (.int .b 32),[some dst],[.reg src,.imm 0,.imm 31],some (.imm (-1))⟩

private theorem probabilitySendCode (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    kernel.code[site.pc]? = some ⟨none,shflIdxOp site.source site.reply⟩ := by
  fin_cases stage
  · exact Flow.code_2307
  · exact Flow.code_2423

private theorem probabilityAlignCode (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    kernel.code[site.alignPc]? = some ⟨none,shflIdxOp site.alignSource site.alignReply⟩ := by
  fin_cases stage
  · exact Flow.code_2308
  · exact Flow.code_2425

private theorem firesFixedIdx {l : Launch} {g : Nat} {s u : TState} {pc src dst : Nat}
    {e : Event}
    (hf : Fires pc (eventTmpl Assumptions.all l g s (shflIdxOp src dst)) e (some u)) :
    ∃ sent recv ok, e = ⟨pc,.shfl .idx sent 0 31 recv ok⟩ ∧ u = next (setReg s dst recv) := by
  obtain ⟨sent,b,c,recv,ok,hGet,hu⟩ := fires_shfl (p := none) hf
  have hReg : ∃ v, s.regs src = some v := by
    cases hz : s.regs src with
    | some v => exact ⟨v,rfl⟩
    | none =>
      have hf' := hf
      simp only [shflIdxOp,eventTmpl] at hf'
      rcases warpTmpl_shfl (L := l) (g := g) (t := s)
        (mode := .idx) (ty := some (.int .b 32)) (d := dst)
        (ps := []) (a := .reg src) (b := .imm 0) (c := .imm 31) (mask := .imm (-1))
        with hRun | hUb
      · rw [hRun] at hf'
        simp [shflTmpl,readValue,readReg,hz] at hf'
        have hThrow : (throw .uninitialized : Exec Value) = .error .uninitialized := rfl
        rw [hThrow] at hf'
        cases hm : readBits l g s 32 (.imm (-1)) <;> simp [hm,Fires] at hf'
      · rw [hUb] at hf'
        cases hf'.2
  obtain ⟨v,hv⟩ := hReg
  obtain ⟨rv,valid,hCode⟩ := fires_shfl_idx (p := none) hv hf (hGet ▸ rfl)
  obtain ⟨_,_,hb,hc,_,_⟩ := Kind.shfl.inj (congrArg Event.kind (hGet.symm.trans hCode))
  exact ⟨sent,recv,ok,by simpa only [hb,hc] using hGet,hu⟩

set_option maxRecDepth 100000 in
private theorem probabilitySendAudit (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    MmaLiveRegAudit site.pc site.pc site.source := by fin_cases stage <;> kernel_rfl

private theorem probabilityLiteral (l : Launch) (g : Nat) (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    Seg kernel [] l g 1 (site.pc-1) [] (site.pc-1+1)
      [(site.source,b32 (probabilityColumn stage))] := by
  dsimp only
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

private theorem literalStep {l : Launch} {g : Nat} (stage : Fin 2)
    {s u : TState} {ev : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hShape : RoleShape s)
    (hs : let site := steadyProbabilitySend stage
      MmaLiveReg site.pc site.pc site.source (b32 (probabilityColumn stage)) s)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    let site := steadyProbabilitySend stage
    MmaLiveReg site.pc site.pc site.source (b32 (probabilityColumn stage)) u := by
  let site := steadyProbabilitySend stage
  change MmaLiveReg site.pc site.pc site.source (b32 (probabilityColumn stage)) u
  by_cases hPc : s.pc+1 = site.pc
  · have hAtPc : s.pc = site.pc-1 := by omega
    have hLate : 1909 < site.pc-1 := by fin_cases stage <;> decide
    have hAt : At s (site.pc-1) [] :=
      ⟨hAtPc,hShape.2.2 (by omega),hShape.2.1,
        mmaRoleReturningNormal (by omega) hHi hw,trivial⟩
    have hLocal := mmaRoleLocalStepAt (by fin_cases stage <;> decide)
      (by fin_cases stage <;> decide) (probabilityLiteral l g stage) hAt hw
    exact fun _ _ => hLocal.2.2.2.2.2.1
  · exact mmaRoleLiveRegStep (probabilitySendAudit stage) hLo hHi hPc hs hw

private def BeforeAnchor (X : Execution) (g pos : Nat) (stage : Fin 2) (s : TState) : Prop :=
  let site := steadyProbabilitySend stage
  site.pc+1 ≤ s.pc → s.pc ≤ site.alignPc → ∃ j recv val,
    j+1 = pos ∧ s.regs site.reply = some recv ∧ X.get (g,j) =
      some ⟨site.pc,.shfl .idx (b32 (probabilityColumn stage)) 0 31 recv val⟩

set_option maxRecDepth 100000 in
private theorem beforeAnchorAudit (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    MmaLiveRegAudit (site.pc+1) site.alignPc site.reply := by fin_cases stage <;> kernel_rfl

private theorem beforeAnchorStep {l : Launch} {X : Execution} {g pos : Nat} (stage : Fin 2)
    {s u : TState} {ev : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hs : BeforeAnchor X g pos stage s)
    (hSent : let site := steadyProbabilitySend stage
      MmaLiveReg site.pc site.pc site.source (b32 (probabilityColumn stage)) s)
    (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    BeforeAnchor X g (pos+ev.toList.length) stage u := by
  let site := steadyProbabilitySend stage
  intro hLow hHigh
  by_cases hp : s.pc = site.pc
  · have hCode := probabilitySendCode stage
    change kernel.code[site.pc]? = some _ at hCode
    rw [← hp] at hCode
    rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
    · unfold Tau at ht
      rw [out_eq_core (by omega) hHi] at ht
      exact (tau_core_not_event hCode rfl ht).elim
    · obtain ⟨ins,hc,_,hf⟩ := estep_event_source he
      obtain rfl := Option.some.inj (hc.symm.trans hCode)
      obtain ⟨sent,recv,ok,rfl,rfl⟩ := firesFixedIdx hf
      obtain ⟨rv,valid,hEq⟩ := fires_shfl_idx (p := none) (hSent hp.ge hp.le) hf rfl
      obtain ⟨_,hWord,_,_,_,_⟩ := Kind.shfl.inj (congrArg Event.kind hEq)
      have hGet := hActual _ rfl
      rw [hp,hWord] at hGet
      exact ⟨pos,recv,ok,rfl,Function.update_self _ _ _,hGet⟩
  · have hNot := Nat.succ_ne_succ_iff.mpr hp
    obtain ⟨hOld,hUpper⟩ := mmaRoleLiveSource (beforeAnchorAudit stage) hLo hHi hNot hw hLow hHigh
    obtain ⟨j,recv,ok,hJ,hReg,hGet⟩ := hs hOld hUpper
    have hWord := mmaRoleLiveRegStep (beforeAnchorAudit stage) hLo hHi hNot
      (fun _ _ => hReg) hw hLow hHigh
    have hSilent : ev = none := by
      rcases hw with ⟨h,_⟩ | ⟨e,rfl,he⟩
      · exact h
      · have hSite : s.pc = site.alignPc ∨ s.pc = 2424 := by
          fin_cases stage
          · left
            exact Nat.le_antisymm hUpper hOld
          · change 2424 ≤ s.pc at hOld
            change s.pc ≤ 2425 at hUpper
            change s.pc = 2425 ∨ s.pc = 2424
            omega
        obtain ⟨ins,hc,hNonlocal,hf⟩ := estep_event_source he
        rcases hSite with hAlign | hMove
        · have hCode := probabilityAlignCode stage
          change kernel.code[site.alignPc]? = some _ at hCode
          rw [hAlign,hCode] at hc
          obtain rfl := Option.some.inj hc
          obtain ⟨sent,r,valid,_,rfl⟩ := firesFixedIdx hf
          change s.pc+1 ≤ site.alignPc at hHigh
          omega
        · rw [hMove,Flow.code_2424] at hc
          obtain rfl := Option.some.inj hc
          cases hNonlocal
    rw [hSilent]
    exact ⟨j,recv,ok,hJ,hWord,hGet⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem probabilityBeforeAnchor (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g pos : Nat} {e : Event}
    (hGet : X.get (g,pos) = some e) (hPc : e.pc = (steadyProbabilitySend stage).alignPc) :
    ∃ j recv ok, j+1 = pos ∧ X.get (g,j) =
      some ⟨(steadyProbabilitySend stage).pc,.shfl .idx (b32 (probabilityColumn stage))
        0 31 recv ok⟩ := by
  let site := steadyProbabilitySend stage
  have hBounds : 1907 < e.pc ∧ e.pc < 2768 ∧ e.pc ∉ registerHintSites := by
    rw [hPc]
    fin_cases stage <;> decide
  have hWarp := mmaRoleEventWarp hp hX hGet hBounds.1 hBounds.2.1 hBounds.2.2
  let Inv := fun i s =>
    MmaLiveReg site.pc site.pc site.source (b32 (probabilityColumn stage)) s ∧
      BeforeAnchor X g i stage s
  obtain ⟨t,o,hFrame,hFire⟩ := mmaRoleReplayOfEvent hp hX hGet hWarp hBounds.1 hBounds.2.1 Inv
    (by
      intro s hs
      have hStart : 1908 < site.pc := by fin_cases stage <;> decide
      refine ⟨fun h _ => ?_,fun h _ => ?_⟩
      · rw [hs] at h
        omega
      · change site.pc+1 ≤ s.pc at h
        rw [hs] at h
        omega)
    (by
      intro s u ev i hLo hHi hShape hs hw hActual
      exact ⟨literalStep stage hLo hHi hShape.1 hs.1 hw,
        beforeAnchorStep stage hLo hHi hs.2 hs.1 hw hActual⟩)
  have hAt : t.pc = site.alignPc := (estep_source_pc hFire).symm.trans hPc
  have hLower : site.pc+1 ≤ site.alignPc := by fin_cases stage <;> decide
  obtain ⟨j,recv,ok,hNext,_,hPrev⟩ := hFrame.2 (hAt.symm ▸ hLower) hAt.le
  exact ⟨j,recv,ok,hNext,hPrev⟩

private theorem matchedAnchorSender (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index n : Nat} {sent recv : Value} {ok : Bool} (hWarp : warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨(steadyProbabilitySend stage).alignPc,
      .shfl .idx sent 0 31 recv ok⟩) (hRank : X.ShflK (g,index) n) :
    ∃ j a b reply valid, X.ShflK (g-laneOf l g,j) n ∧ X.get (g-laneOf l g,j) =
      some ⟨(steadyProbabilitySend stage).alignPc,.shfl .idx recv a b reply valid⟩ := by
  fin_cases stage
  · exact cacheDescriptorShuffleSource hp hX 0 hWarp he hRank
  · exact steadyOutputShuffleSource hp hX 1 hWarp he hRank

private theorem probabilityReceivedAtAnchor (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index j : Nat}
    {sent recv pRecv : Value} {ok pValid : Bool} (hWarp : warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨(steadyProbabilitySend stage).alignPc,
      .shfl .idx sent 0 31 recv ok⟩) (hAdjacent : j+1 = index)
    (hProb : X.get (g,j) = some ⟨(steadyProbabilitySend stage).pc,
      .shfl .idx (b32 (probabilityColumn stage)) 0 31 pRecv pValid⟩) :
    pRecv = b32 (probabilityColumn stage) := by
  let site := steadyProbabilitySend stage
  let peer := g-laneOf l g
  let n := ((X.tr g).take index).countP Execution.isShfl
  have hRank : X.ShflK (g,index) n := ⟨⟨_,_,_,_,_,_,_,he⟩,rfl⟩
  obtain ⟨i,a,b,reply,valid,hPeerRank,hPeer⟩ := matchedAnchorSender hp hX stage hWarp he hRank
  obtain ⟨k,pr,v,hNext,hPeerProb⟩ := probabilityBeforeAnchor hp hX stage hPeer rfl
  let rank := ((X.tr g).take j).countP Execution.isShfl
  let peerRank := ((X.tr peer).take k).countP Execution.isShfl
  have hLeft : X.ShflK (g,j) rank := ⟨⟨_,_,_,_,_,_,_,hProb⟩,rfl⟩
  have hRight : X.ShflK (peer,k) peerRank := ⟨⟨_,_,_,_,_,_,_,hPeerProb⟩,rfl⟩
  have hL := shfl_count_succ hLeft
  have hR := shfl_count_succ hRight
  rw [hAdjacent,hRank.2] at hL
  rw [hNext,hPeerRank.2] at hR
  have hSame : rank = peerRank := by omega
  have hSite : site.pc < 2763 := by fin_cases stage <;> decide
  obtain ⟨hit,snd,a',b',ret,rv,hOrd,hSent⟩ :=
    mmaLaneZeroShuffleSource hp hX hWarp hProb hLeft hSite
  have hMatch : hit = k := ShflK.eq_of_ord hOrd (hSame.symm ▸ hRight)
  subst hit
  have hKind := congrArg Event.kind (Option.some.inj (hSent.symm.trans hPeerProb))
  exact (Kind.shfl.inj hKind).2.1

set_option maxRecDepth 100000 in
private theorem alignmentCursorAudit (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    MmaLiveRegAudit (site.alignPc+1) site.copyPc 1062 := by fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem probabilityReplyAudit (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    MmaLiveRegAudit (site.pc+1) site.copyPc site.reply := by fin_cases stage <;> kernel_rfl

private def AlignedProbability (stage : Fin 2) (s : TState) : Prop :=
  let site := steadyProbabilitySend stage
  MmaLiveReg (site.alignPc+1) site.copyPc site.reply (b32 (probabilityColumn stage)) s

private theorem alignedProbabilityStep (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g pos : Nat}
    (hWarp : warpIndex l g = 12) {s u : TState} {ev : Option Event} (hLo : 1907 ≤ s.pc)
    (hHi : s.pc < 2768) (hs : AlignedProbability stage s) (hRaw : BeforeAnchor X g pos stage s)
    (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) : AlignedProbability stage u := by
  let site := steadyProbabilitySend stage
  have hGap : site.pc+1 ≤ site.alignPc := by fin_cases stage <;> decide
  have hAfter : site.alignPc ≤ site.copyPc := by fin_cases stage <;> decide
  intro hlo hhi
  change site.alignPc+1 ≤ u.pc at hlo
  change u.pc ≤ site.copyPc at hhi
  have hOrdinary (hIn : site.pc+1 ≤ s.pc)
      (hWord : s.regs site.reply = some (b32 (probabilityColumn stage))) :
      u.regs site.reply = some (b32 (probabilityColumn stage)) := by
    exact mmaRoleLiveRegStep (probabilityReplyAudit stage) hLo hHi
      (by change s.pc+1 ≠ site.pc+1; omega)
      (fun _ _ => hWord) hw (by change site.pc+1 ≤ u.pc; omega) hhi
  by_cases hAt : s.pc = site.alignPc
  · obtain ⟨j,pRecv,pValid,hAdjacent,hReg,hReceived⟩ := hRaw (hAt.symm ▸ hGap) hAt.le
    have hCode := probabilityAlignCode stage
    change kernel.code[site.alignPc]? = some _ at hCode
    rw [← hAt] at hCode
    have hRecv : pRecv = b32 (probabilityColumn stage) := by
      rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
      · unfold Tau at ht
        rw [out_eq_core (by omega) hHi] at ht
        exact (tau_core_not_event hCode rfl ht).elim
      · obtain ⟨ins,hc,_,hf⟩ := estep_event_source he
        obtain rfl := Option.some.inj (hc.symm.trans hCode)
        obtain ⟨sent,recv,ok,rfl,_⟩ := firesFixedIdx hf
        have hGet := hActual _ rfl
        rw [hAt] at hGet
        exact probabilityReceivedAtAnchor hp hX stage hWarp hGet hAdjacent hReceived
    exact hOrdinary (hAt.symm ▸ hGap) (hRecv ▸ hReg)
  · obtain ⟨hPrev,hUpper⟩ := mmaRoleLiveSource (alignmentCursorAudit stage) hLo hHi
      (Nat.succ_ne_succ_iff.mpr hAt) hw hlo hhi
    change site.alignPc+1 ≤ s.pc at hPrev
    exact hOrdinary (by omega) (hs hPrev hUpper)

private abbrev steadyBlock (stage : Fin 2) : Fin 4 := firstPvBlock true stage

set_option maxRecDepth 100000 in
private theorem probabilityActualRegisterAudit (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    let block := steadyBlock stage
    MmaLiveRegAudit (site.copyPc+1) (pvPc block 7) (pvSite block).a := by
  fin_cases stage <;> kernel_rfl

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem probabilityCopyLocal (l : Launch) (g : Nat) (stage : Fin 2) :
    let site := steadyProbabilitySend stage
    Seg kernel [] l g 1 site.copyPc [(site.reply,b32 (probabilityColumn stage))]
      (site.copyPc+1) [((pvSite (steadyBlock stage)).a,b32 (probabilityColumn stage))] := by
  dsimp only
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

/-- Every steady-visit PV fragment uses its stage's physical probability address. -/
theorem PvInstruction.steadyProbabilityAddress (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {i : EvId} {frag : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : PvInstruction X i (firstPvBlock true stage) frag d op acc mask) :
    op.aTmem = some (probabilityColumn stage+8*frag.val) := by
  obtain ⟨g,index⟩ := i
  let site := steadyProbabilitySend stage
  let block := steadyBlock stage
  let target : Event := ⟨pvPc block frag,.tc (.mma d op acc mask)⟩
  have he : X.get (g,index) = some target := hi.decoded
  have hBounds : 1907 < target.pc ∧ target.pc < 2768 ∧ target.pc ∉ registerHintSites := by
    change 1907 < pvPc block frag ∧ pvPc block frag < 2768 ∧ pvPc block frag ∉ registerHintSites
    fin_cases stage <;> fin_cases frag <;> decide
  have hWarp := mmaRoleEventWarp hp hX he hBounds.1 hBounds.2.1 hBounds.2.2
  let word := b32 (probabilityColumn stage)
  let stored := MmaLiveReg (site.copyPc+1) (pvPc block 7) (pvSite block).a word
  let Inv := fun pos s => MmaLiveReg site.pc site.pc site.source word s ∧
    BeforeAnchor X g pos stage s ∧ AlignedProbability stage s ∧ stored s
  obtain ⟨t,o,hRegs,hFire⟩ := mmaRoleReplayOfEvent hp hX he hWarp hBounds.1 hBounds.2.1 Inv
    (by
      intro s hs
      have hStart : 1908 < site.pc ∧ 1908 < site.alignPc ∧ 1908 < site.copyPc := by
        fin_cases stage <;> decide
      refine ⟨fun h _ => ?_,fun h _ => ?_,fun h _ => ?_,fun h _ => ?_⟩
      · rw [hs] at h
        omega
      · change site.pc+1 ≤ s.pc at h
        rw [hs] at h
        omega
      · change site.alignPc+1 ≤ s.pc at h
        rw [hs] at h
        omega
      · rw [hs] at h
        omega)
    (by
      intro s u ev pos hLo hHi hShape hs hw hActual
      refine ⟨literalStep stage hLo hHi hShape.1 hs.1 hw,
        beforeAnchorStep stage hLo hHi hs.2.1 hs.1 hw hActual,
        alignedProbabilityStep hp hX stage hWarp hLo hHi hs.2.2.1 hs.2.1 hw hActual,?_⟩
      by_cases hc : s.pc = site.copyPc
      · have hC : site.alignPc+1 ≤ site.copyPc := by fin_cases stage <;> decide
        have hAt : At s site.copyPc [(site.reply,word)] :=
          ⟨hc,hShape.1.2.2 (by rw [hc]; fin_cases stage <;> decide),hShape.1.2.1,
            mmaRoleReturningNormal (by omega) hHi hw,⟨hs.2.2.1 (hc.symm ▸ hC) hc.le,trivial⟩⟩
        obtain ⟨_,hLocal⟩ := mmaRoleLocalStepAt (by fin_cases stage <;> decide)
          (by fin_cases stage <;> decide) (probabilityCopyLocal l g stage) hAt hw
        exact fun _ _ => hLocal.2.2.2.2.1
      · exact mmaRoleLiveRegStep (probabilityActualRegisterAudit stage) hLo hHi
          (Nat.succ_ne_succ_iff.mpr hc) hs.2.2.2 hw)
  have hPc : t.pc = pvPc block frag := (estep_source_pc hFire).symm
  have hLive : site.copyPc+1 ≤ pvPc block frag ∧ pvPc block frag ≤ pvPc block 7 := by
    fin_cases stage <;> fin_cases frag <;> decide
  have hWord := hRegs.2.2.2 (hPc.symm ▸ hLive.1) (hPc.symm ▸ hLive.2)
  have hStage : (pvSite block).stage = stage := by fin_cases stage <;> rfl
  change t.regs (pvSite block).a = some (b32 (probabilityColumn stage)) at hWord
  rw [← hStage] at hWord ⊢
  exact pvProbabilityAddressOfRegister (event_thread_lt hX he) block frag hWord hFire

/-- The actual PV A address in every steady and tail visit. -/
theorem PvInstruction.probabilityAddress (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {block : Fin 4} {frag : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : PvInstruction X i block frag d op acc mask) :
    op.aTmem = some (probabilityColumn (pvSite block).stage+8*frag.val) := by
  fin_cases block
  · exact hi.steadyProbabilityAddress hp hX 0
  · exact hi.steadyProbabilityAddress hp hX 1
  · exact hi.tailProbabilityAddress hp hX 0
  · exact hi.tailProbabilityAddress hp hX 1

end PTX.Kernels.TmlFa4Fwd.Thread
