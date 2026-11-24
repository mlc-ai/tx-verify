-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailOutputBase
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpPvPacket
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpPollProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondScoreIssue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Epilogue Prologue

/-- Operands retained between the tail packets and the terminal commits. -/
def terminalPvFrame (l : Launch) : List (Nat × Value) :=
  [(2612,b32 (valueDescriptorLow l 1)),(2615,b32 (l.sharedBase+104)),
   (2618,b32 (l.sharedBase+120)),(7205,b32 0),(7206,b32 0),
   (1194,b32 (l.sharedBase+8)),(2535,b32 l.sharedBase),(6495,b32 (l.sharedBase+144))]

private theorem terminalPvFrameOfFirst {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {ends : Nat → Option TState} (c : OpeningTailFirstPvElected l X g shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2563
      (fun lane => pvElectedFrame l g 2 1 0 false (terminalPvFrame l) lane c.leader)
      shuffles votes ends) := by
  apply c.cursor.advanceLocal
  intro lane hl
  have ht := c.cursor.checkpoint lane hl
  have hEntry := (holds_append ..).mp ht.2.2.2.2.2
  have hBase := c.outputBase hp hMax hg hw lane hl
  refine ⟨c.cursor.state lane,.refl,ht.mono ⟨ht.2.2.2.2.1,(holds_append ..).mpr ⟨hEntry.1,?_⟩⟩⟩
  have mem (pair : Nat × Value) (h : pair ∈ tailValueWaitFrame l) :=
    holds_mem hEntry.2 h
  refine ⟨hEntry.1.2.2.1,mem (2615,_) ?_,mem (2618,_) ?_,mem (7205,_) ?_,
    mem (7206,_) ?_,mem (1194,_) ?_,mem (2535,_) ?_,hBase,trivial⟩ <;>
    simp [tailValueWaitFrame,tailValueCommitFrame,b32]

private theorem terminalPvSetup (l : Launch) (which : Fin 2) :
    ((kernel.code.drop ((electSite (pvElection (if which = 0 then 2 else 3))).pc+1)).take 7).all
      (fun ins => ((terminalPvFrame l).map Prod.fst).all (fun r => !(writesRegs ins.op).contains r))
      = true := by
  simp only [terminalPvFrame,List.map]
  set_option maxRecDepth 100000 in
  fin_cases which <;> kernel_rfl

private theorem terminalPvExtra (l : Launch) (which : Fin 2) :
    let block : Fin 4 := if which = 0 then 2 else 3
    ∀ pair ∈ terminalPvFrame l, pair.1 ≠ (pvSite block).b-2 ∧ pair.1 ≠ (pvSite block).b ∧
      pair.1 ≠ (waitSite (pvTailWait block)).result := by
  intro block pair hm
  have hm' := List.mem_map_of_mem (f := Prod.fst) hm
  have hChecked : ∀ r ∈ [2612,2615,2618,7205,7206,1194,2535,6495],
      r ≠ (pvSite block).b-2 ∧ r ≠ (pvSite block).b ∧
      r ≠ (waitSite (pvTailWait block)).result := by
    fin_cases which <;> dsimp [block] <;> decide
  exact hChecked _ hm'

private def secondBroadcast (stage : Bool) : Nat × Nat × Nat × Nat :=
  match stage with
  | false => (2598,2628,2616,192)
  | true => (2600,2629,2617,384)

private theorem secondBroadcastCode (stage : Bool) :
    let (pc,tmp,dst,value) := secondBroadcast stage
    kernel.code[pc]? = some ⟨none,.move ⟨.scalar,.int .b 32,[some tmp],[.imm value]⟩⟩ ∧
    kernel.code[pc+1]? = some ⟨none,.warp ⟨.shfl .idx,some (.int .b 32),[some dst],
      [.reg tmp,.imm 0,.imm 31],some (.imm (-1))⟩⟩ := by
  cases stage
  · exact ⟨Flow.code_2598,Flow.code_2599⟩
  · exact ⟨Flow.code_2600,Flow.code_2601⟩

private theorem secondBroadcastProgress {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (stage : Bool)
    {F : List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (secondBroadcast stage).1 (fun _ => F) shuffles votes ends)
    (hTmp : (secondBroadcast stage).2.1 ∉ F.map Prod.fst)
    (hDst : (secondBroadcast stage).2.2.1 ∉ F.map Prod.fst) :
    Nonempty (SchedulerWarpReached l X g ((secondBroadcast stage).1+2)
      (fun _ => ((secondBroadcast stage).2.2.1,b32 (secondBroadcast stage).2.2.2) ::
        ((secondBroadcast stage).2.1,b32 (secondBroadcast stage).2.2.2) :: F)
      (shuffles+1) votes ends) := by
  let pc := (secondBroadcast stage).1
  let tmp := (secondBroadcast stage).2.1
  let dst := (secondBroadcast stage).2.2.1
  let value := (secondBroadcast stage).2.2.2
  have hCode : kernel.code[pc]? = some ⟨none,.move ⟨.scalar,.int .b 32,[some tmp],[.imm value]⟩⟩ ∧
      kernel.code[pc+1]? = some ⟨none,.warp ⟨.shfl .idx,some (.int .b 32),[some dst],
        [.reg tmp,.imm 0,.imm 31],some (.imm (-1))⟩⟩ := by
    cases stage
    · exact secondBroadcastCode false
    · exact secondBroadcastCode true
  have hLo : 1904 ≤ (secondBroadcast stage).1 := by cases stage <;> decide
  have hHi : (secondBroadcast stage).1+1 < 2768 := by cases stage <;> decide
  have hNe : (secondBroadcast stage).2.1 ≠ (secondBroadcast stage).2.2.1 := by
    cases stage <;> decide
  obtain ⟨s⟩ := cur.advanceLocal (pc' := pc+1) (G := fun _ => (tmp,b32 value)::F) (by
    intro lane hl
    have h := cur.checkpoint lane hl
    let u := next (setReg (cur.state lane) tmp (b32 value))
    have hr : run kernel [] l (warpLane l g lane) 1 (cur.state lane) = some u := by
      apply run_local hCode.1 rfl h
      cases stage <;> simp only [tmp,value,secondBroadcast,u] <;> rfl
    have hTau := localRun hLo (Nat.le_of_lt hHi) h.1 rfl hr
    refine ⟨u,run_rtg hTau,h.set ?_⟩
    intro pair hm he
    have hh := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hh
    exact hTmp hh)
  exact s.consumeShuffle (dst := dst) hp hMax hg .idx (fun _ => b32 value)
    (fun _ => 0) (fun _ => 31) (by
      intro _ _ pair hm
      rcases List.mem_cons.mp hm with he | hm
      · rw [he]
        exact hNe
      · intro he
        have hh := List.mem_map_of_mem (f := Prod.fst) hm
        rw [he] at hh
        exact hDst hh) (by
      intro lane hl
      have ht := s.checkpoint lane hl
      have h : (s.state lane).regs tmp = some (b32 value) := ht.2.2.2.2.1
      rw [out_eq_core (by rw [ht.1]; omega) (by rwa [ht.1]),
        out_event ht.2.2.2.1 (by rw [ht.1]; exact hCode.2) rfl rfl]
      change Out.ev (shflTmpl l (warpLane l g lane) (s.state lane) .idx dst none
        (.reg tmp) (.imm 0) (.imm 31) (.imm (-1))) = _
      have hBlock : l.block%32 = 0 := by rw [hp.block]
      simp [shflTmpl,readValue,readReg,h,hBlock,Value.bytes,b32,readBits,pure,Except.pure]
      rfl)

private theorem secondPvElection {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2598 (fun _ => terminalPvFrame l) shuffles votes ends) :
    ∃ leader : Fin 32, Nonempty (SchedulerWarpReached l X g 2603
      (fun lane => pvElectedFrame l g 3 1 0 false (terminalPvFrame l) lane leader)
      (shuffles+2) votes ends) := by
  obtain ⟨a⟩ := secondBroadcastProgress hp hMax hg false cur (by simp [secondBroadcast,
    terminalPvFrame]) (by simp [secondBroadcast,terminalPvFrame])
  obtain ⟨b⟩ := secondBroadcastProgress hp hMax hg true a (by simp [secondBroadcast,
    terminalPvFrame]) (by simp [secondBroadcast,terminalPvFrame])
  let F := pvEntryFacts l 3 1 0 false ++ terminalPvFrame l
  obtain ⟨c⟩ := b.advanceLocal (pc' := 2602) (G := fun _ => F) (by
    intro lane hl
    have ht := b.checkpoint lane hl
    have h := ht.2.2.2.2
    exact ⟨b.state lane,.refl,ht.mono ((holds_append ..).mpr
      ⟨⟨h.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.1, trivial⟩,h.2.2.2.2⟩)⟩)
  have hPred : ∀ pair ∈ F, pair.1 ≠ 9738 := by
    intro pair hm he
    have hReg := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hReg
    exact (of_decide_eq_true rfl : 9738 ∉ F.map Prod.fst) hReg
  obtain ⟨leader,w,_⟩ := c.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (c.state lane) 16)
    (fun lane leader => (9738,.pred (laneOf l (warpLane l g lane) == leader)) :: F)
    (fun lane hl _ hj _ _ _ he =>
      noEarlierMmaElection 16 Flow.code_2602
        (by set_option maxRecDepth 100000 in kernel_rfl) (by kernel_rfl)
        (c.checkpoint lane hl) (c.recorded lane hl) (c.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 16 (c.checkpoint lane hl))
    (fun lane hl leader => electStateFrame 16 (c.checkpoint lane hl) leader hPred
      (by simp [electSite]))
  exact ⟨leader,⟨w⟩⟩

/-- The terminal PV path traverses both real packets, using the second half's actual
main and tail acquires, and reaches the first terminal commit election. -/
theorem terminalPvPacketsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {ends : Nat → Option TState} (c : OpeningTailFirstPvElected l X g shuffles votes ends)
    (hTail0 : let log := X.objects ⟨.shared,g/l.block,l.sharedBase+112⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1)
    (hMain1 : let log := X.objects ⟨.shared,g/l.block,l.sharedBase+104⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1)
    (hTail1 : let log := X.objects ⟨.shared,g/l.block,l.sharedBase+120⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    ∃ lastEnds, Nonempty (SchedulerWarpReached l X g 2635 (fun _ => terminalPvFrame l)
      (shuffles+2) votes lastEnds) ∧ PvPacketIssues l X g 3 1 false := by
  obtain ⟨first⟩ := terminalPvFrameOfFirst hp hMax hg hw c
  obtain ⟨_,⟨q⟩,_⟩ := pvWarpPacketFromElected hp hMax hg 2 1 0 false (by decide) c.leader
    (terminalPvExtra l 0) (terminalPvSetup l 0) first (by
      obtain ⟨s,hs,hp⟩ := hTail0
      exact ⟨s,hs,by simp [hp]⟩)
  have hWidth : l.sharedBase+104 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+104)%8 = 0 := by have := hp.shared.1; omega
  obtain ⟨r,_⟩ := mmaWarpPollOfMaximal hp hMax hg 12 hWidth hAlign (phase := 0) (by decide)
    q (by
      intro lane hl
      refine ⟨?_,?_,?_⟩
      · intro pair hm
        have hm' := List.mem_map_of_mem (f := Prod.fst) hm
        change pair.1 ≠ 9737
        have hCheck : ∀ r ∈ [2612,2615,2618,7205,7206,1194,2535,6495], r ≠ 9737 :=
          by decide
        exact hCheck _ hm'
      · simp [waitSite,terminalPvFrame]
      · simp [waitSite,terminalPvFrame]) (by
        intro _ _ _ _ _ _ _
        obtain ⟨s,hs,hp⟩ := hMain1
        exact ⟨s,hs,by simp [hp]⟩)
  obtain ⟨leader,⟨w⟩⟩ := secondPvElection hp hMax hg r
  exact pvWarpPacketFromElected hp hMax hg 3 1 0 false (by decide) leader
    (terminalPvExtra l 1) (terminalPvSetup l 1) w (by
      obtain ⟨s,hs,hp⟩ := hTail1
      exact ⟨s,hs,by simp [hp]⟩)

end PTX.Kernels.TmlFa4Fwd.Mma
