-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyIteration
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReachedQueryBank
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTailOutputBase
import all Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorAbi
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Epilogue
open Thread (SawScoreGate scoreGate scoreGateStep scoreReplyFloor scoreReplySegments
  scoreReplyAudit initialScoreBroadcastOfElection initialScoreBroadcastFrame scoreBroadcastRegister
  mmaRoleLiveRegStep eventTailStepOfAudit)

noncomputable section

private def startupBankFrame (l : Launch) : List (Nat × Value) :=
  [(1062,b32 12),(2535,b32 l.sharedBase),(6495,b32 (l.sharedBase+144)),(9632,b32 0x8200490)] ++
    qDescriptorFacts l 1

private theorem startupBankFromAbi {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) {s : TState}
    (hs : At s 1917 ((2450,b32 (startupQLow l)) :: entryFacts p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 1935 (startupBankFrame l) := by
  obtain ⟨u,hr,hu⟩ := (startupQRegistersCore hp g).apply
    (hs.mono ⟨holds_mem hs.2.2.2.2 (by simp),trivial⟩)
  have hBase : At s 1917
      [(1062,b32 12),(2535,b32 l.sharedBase),(6495,b32 (l.sharedBase+144))] :=
    hs.mono ⟨holds_mem hs.2.2.2.2 (by simp [entryFacts,startupFacts]),
      holds_mem hs.2.2.2.2 (by simp [entryFacts,startupFacts]),
      holds_mem hs.2.2.2.2 (by simp [entryFacts,startupFacts]),trivial⟩
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep hBase (by decide) (by decide) (by
    change ((kernel.code.drop 1917).take 18).all
      (fun ins => [1062,2535,6495].all fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hr
  exact ⟨u,hPath,hu.mono ⟨hKeep.1,hKeep.2.1,hKeep.2.2.1,hu.2.2.2.2.2.1,hu.2.2.2.2.2.2.2⟩⟩

private theorem openingFloorCode (floor : Nat) (h : floor ∈ [1935,2275]) :
    (kernel.code.drop floor).all (fun i => Thread.staysPastEvent floor i.op) = true := by
  rcases (by simpa using h : floor = 1935 ∨ floor = 2275) with rfl | rfl <;>
    (set_option maxRecDepth 100000 in kernel_rfl)

private theorem openingFloorSegments (floor : Nat) (h : floor ∈ [1935,2275]) :
    Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true := by
  rcases (by simpa using h : floor = 1935 ∨ floor = 2275) with rfl | rfl <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem openingReachedFloor {l : Launch} {g floor : Nat}
    {s t : TState} {es : List Event} (hFloor : floor ∈ [1935,2275])
    (h : TraceReach kernel Assumptions.all l g s es t) (hs : floor ≤ s.pc) : floor ≤ t.pc := by
  have keep {s u : TState} {e : Option Event} (hPc : floor ≤ s.pc)
      (hStep : WStep kernel Assumptions.all l g s e u) : floor ≤ u.pc :=
    eventTailStepOfAudit (openingFloorCode floor hFloor)
      (openingFloorSegments floor hFloor) hPc hStep
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (keep hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (keep hs (.inr ⟨_,rfl,he⟩))

private theorem openingBarrierAtKeyReturn {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s t : TState} {events : List Event}
    (hs : At s 1935 (startupBankFrame l))
    (hr : TraceReach kernel Assumptions.all l g s events t) (ht : t.pc = 2275) :
    t.regs 1188 = some (b32 (l.sharedBase+80)) := by
  have hStart : mmaMbarFrame l s := by
    refine ⟨⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩,
      hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1,?_⟩
    intro f hf hActive
    exfalso
    rw [hs.1] at hActive
    simp only [fixedMmaAdds,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (by decide : ¬ FixedAdd.active _ 1935) hActive
  have fold {a z : TState} {es : List Event}
      (h : TraceReach kernel Assumptions.all l g a es z) :
      (∀ {b : TState} {xs : List Event},
        TraceReach kernel Assumptions.all l g b xs z → b.pc < 2768) →
      1907 ≤ a.pc → mmaMbarFrame l a → mmaMbarFrame l z := by
    induction h with
    | refl => exact fun _ _ h => h
    | tau hu hTail ih =>
      intro hUp hLower hf
      obtain ⟨hNext,hf'⟩ := fixedMmaAddrStep hp hLower
        (hUp (.tau hu hTail)) hf (.inl ⟨rfl,hu⟩)
      exact ih hUp (by rcases hNext with h | h <;> omega) hf'
    | event he hTail ih =>
      intro hUp hLower hf
      obtain ⟨hNext,hf'⟩ := fixedMmaAddrStep hp hLower
        (hUp (.event he hTail)) hf (.inr ⟨_,rfl,he⟩)
      exact ih hUp (by rcases hNext with h | h <;> omega) hf'
  have hUpper {b : TState} {xs : List Event}
      (path : TraceReach kernel Assumptions.all l g b xs t) : b.pc < 2768 :=
    Nat.lt_of_not_ge fun hb => (by rw [ht]; decide : ¬ 2768 ≤ t.pc)
      (upperFloorOfReach path hb)
  exact (fold hr hUpper (by rw [hs.1]; decide) hStart).2.2.2.2
    ⟨2109,2646,1188,80⟩ (by decide) (by rw [ht]; decide)

set_option maxRecDepth 100000 in
private theorem openingScoreElectionOnPath {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {g pos : Nat} {s t : TState} {events : List Event}
    (hr : TraceReach kernel Assumptions.all l g s events t)
    (hLo : 1935 ≤ s.pc) (hHi : t.pc < 2768)
    (hInit : SawScoreGate X g pos stage s)
    (hActual : ∀ {i e}, events[i]? = some e → X.get (g,pos+i) = some e) :
    SawScoreGate X g (pos+events.length) stage t := by
  induction hr generalizing pos with
  | refl => simpa only [List.length_nil,Nat.add_zero] using hInit
  | @tau s u t es hTau hTail ih =>
    have hStep : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,hTau⟩
    have hUpper : s.pc < 2768 := Nat.lt_of_not_ge fun h =>
      (Nat.not_le_of_lt hHi) (upperFloorOfReach (.tau hTau hTail) h)
    have hNext := scoreGateStep hX stage (show 1907 ≤ s.pc by omega) hUpper hInit hStep
      (fun _ h => by cases h)
    have hNextLo := eventTailStepOfAudit (openingFloorCode 1935 (by decide))
      (openingFloorSegments 1935 (by decide)) hLo hStep
    exact ih hNextLo hHi (by simpa only [Option.toList_none,List.length_nil,Nat.add_zero]
      using hNext) hActual
  | @event s u t es e hEvt hTail ih =>
    have hStep : WStep kernel Assumptions.all l g s (some e) u := .inr ⟨_,rfl,hEvt⟩
    have hUpper : s.pc < 2768 := Nat.lt_of_not_ge fun h =>
      (Nat.not_le_of_lt hHi) (upperFloorOfReach (.event hEvt hTail) h)
    have hNext := scoreGateStep hX stage (show 1907 ≤ s.pc by omega) hUpper hInit hStep
      (fun found he => by
        obtain rfl := Option.some.inj he
        simpa only [Nat.add_zero] using hActual (i := 0) rfl)
    have hNextLo := eventTailStepOfAudit (openingFloorCode 1935 (by decide))
      (openingFloorSegments 1935 (by decide)) hLo hStep
    have hActual' {i e'} (h : es[i]? = some e') : X.get (g,pos+1+i) = some e' := by
      have x := hActual (i := i+1) h
      rwa [show pos+(i+1) = pos+1+i by omega] at x
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (pos := pos+1) hNextLo hHi hNext hActual'

private theorem eventOnReturningPath {l : Launch} {g : Nat} {s t : TState}
    {es : List Event} {index : Nat} {e : Event}
    (hr : TraceReach kernel Assumptions.all l g s es t) (he : es[index]? = some e) :
    ∃ a u, EStep kernel Assumptions.all l g a e (some u) ∧
      TraceReach kernel Assumptions.all l g u (es.drop (index+1)) t := by
  induction hr generalizing index with
  | refl => simp at he
  | tau _ _ ih => exact ih he
  | @event s u t es e' h hTail ih =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨s,u,h,hTail⟩
    | succ index => exact ih he

private theorem scoreBroadcastRetained {l : Launch} {g : Nat} (stage : Fin 2)
    {s t : TState} {events : List Event}
    (hr : TraceReach kernel Assumptions.all l g s events t)
    (hBound : t.pc < 2768) (hStart : scoreGate stage ≤ s.pc)
    (hFrame : Thread.MmaLiveReg (scoreGate stage) 2647 (scoreBroadcastRegister stage)
      (b32 (scoreColumn stage)) s) :
    Thread.MmaLiveReg (scoreGate stage) 2647 (scoreBroadcastRegister stage)
      (b32 (scoreColumn stage)) t := by
  have hGateLo : 1907 ≤ scoreGate stage := by fin_cases stage <;> decide
  have step {a b : TState} {ev : Option Event} (hOld : scoreGate stage ≤ a.pc)
      (hUpper : a.pc < 2768) (hStep : WStep kernel Assumptions.all l g a ev b)
      (hFrame : Thread.MmaLiveReg (scoreGate stage) 2647 (scoreBroadcastRegister stage)
        (b32 (scoreColumn stage)) a) :
      scoreGate stage ≤ b.pc ∧ Thread.MmaLiveReg (scoreGate stage) 2647
        (scoreBroadcastRegister stage) (b32 (scoreColumn stage)) b :=
    ⟨eventTailStepOfAudit (scoreReplyFloor stage) (scoreReplySegments stage) hOld hStep,
      mmaRoleLiveRegStep (scoreReplyAudit stage) (hGateLo.trans hOld) hUpper
        (by omega) hFrame hStep⟩
  induction hr with
  | refl => exact hFrame
  | tau ht hTail ih =>
    have hUpper := Nat.lt_of_not_ge fun h =>
      (Nat.not_le_of_lt hBound) (upperFloorOfReach (.tau ht hTail) h)
    obtain ⟨hLow,hF⟩ := step hStart hUpper (.inl ⟨rfl,ht⟩) hFrame
    exact ih hBound hLow hF
  | event he hTail ih =>
    have hUpper := Nat.lt_of_not_ge fun h =>
      (Nat.not_le_of_lt hBound) (upperFloorOfReach (.event he hTail) h)
    obtain ⟨hLow,hF⟩ := step hStart hUpper (.inr ⟨_,rfl,he⟩) hFrame
    exact ih hBound hLow hF

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g trips shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12)
include hp hMax hg hw

/-- An actually returned opening key cursor retains the selected two score columns,
barrier address and assembled Q bank needed by arbitrary later visits. -/
theorem OpeningKeyReturnedWithTrip.steadyRootsAndElections {ends : Nat → Option TState}
    (cur : OpeningKeyReturnedWithTrip l X g trips shuffles votes ends) (lane : Nat) (hl : lane < 32)
    :
    Holds (cur.state lane).regs (steadyIterationRoots l) ∧
    ∀ stage : Fin 2, ∃ idx inst leader, idx < cur.pos lane ∧
      X.Elect (warpLane l g lane,idx) (2153+62*stage.val) (2^32-1) inst leader := by
  let th := warpLane l g lane
  have hSame := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  obtain ⟨s,_,_,he,_,hs,hStart,_⟩ :=
    schedulerAbiAtDescriptorWithOrdinal hp hMax hSame.1.2.1 (hSame.2.symm.trans hw)
  obtain ⟨u,hu,hU⟩ := startupBankFromAbi hp th hs
  let n := descriptorShufflePos (laneOf l th)+1
  have hBound : n ≤ (X.tr th).length := len_of_get he
  have ht := cur.checkpoint lane hl
  obtain ⟨hCut,hPath⟩ := recordedCheckpointsPath hBound (cur.bounded lane hl)
    hStart hu (cur.recorded lane hl) (cur.localSteps lane hl) (by
      intro es hBack
      have hFloor := openingReachedFloor (by decide : 2275 ∈ [1935,2275]) hBack ht.1.ge
      rw [hU.1] at hFloor
      omega)
  have hB := Thread.openingQueryBankAtReturnedPrefix hp
    (hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.2.2.1,hU.2.2.2.2.2.2.2.2⟩) hPath ht.1
  have hBar := openingBarrierAtKeyReturn hp hU hPath ht.1
  let events := ((X.tr th).drop n).take (cur.pos lane-n)
  have hGetIndex {i event} (h : events[i]? = some event) :
      X.get (th,n+i) = some event := by
    have hi : i < events.length := (List.getElem?_eq_some_iff.mp h).1
    have hi' : i < cur.pos lane-n := by
      simp only [events,List.length_take] at hi
      omega
    simp only [events,List.getElem?_take_of_lt hi',List.getElem?_drop] at h
    exact h
  have hLen : n+events.length = cur.pos lane := by
    simp only [events,List.length_take,List.length_drop]
    have hb : cur.pos lane ≤ (X.tr th).length := cur.bounded lane hl
    omega
  have hScores (stage : Fin 2) : (cur.state lane).regs (scoreBroadcastRegister stage) =
      some (b32 (scoreColumn stage)) ∧
      ∃ idx inst leader, idx < cur.pos lane ∧
        X.Elect (th,idx) (scoreGate stage) (2^32-1) inst leader := by
    have hInit : SawScoreGate X th n stage u := by
      intro hOutside _
      have hPos := hU.1
      have hGate : 1935 < scoreGate stage+1 := by fin_cases stage <;> decide
      omega
    have hVotes := openingScoreElectionOnPath hMax.1 stage hPath hU.1.ge
      (by rw [ht.1]; decide) hInit (fun h => hGetIndex h)
    change SawScoreGate X th (n+events.length) stage (cur.state lane) at hVotes
    rw [hLen] at hVotes
    have hGate : scoreGate stage+1 ≤ (cur.state lane).pc := by
      rw [ht.1]
      fin_cases stage <;> decide
    obtain ⟨j,inst,leader,hBefore,hElect⟩ := hVotes hGate (by rw [ht.1]; decide)
    obtain ⟨k,ok,hEvent,hSucc⟩ := initialScoreBroadcastOfElection hp hMax.1 stage hElect
    have hk : k < cur.pos lane := by omega
    have hTrace := (cur.recorded lane hl).returning_reach.append
      (TraceReach.of_local (cur.localSteps lane hl))
    rw [List.append_nil] at hTrace
    obtain ⟨_,after,hStep,hTail⟩ := eventOnReturningPath hTrace (index := k)
      (by rw [List.getElem?_take_of_lt hk]; exact hEvent)
    obtain ⟨afterPc,hWord⟩ := initialScoreBroadcastFrame stage ok hStep
    have hStart : scoreGate stage ≤ after.pc := afterPc.ge
    refine ⟨scoreBroadcastRetained stage hTail (by rw [ht.1]; decide) hStart
      (fun _ _ => hWord) (by omega) (by rw [ht.1]; decide),j,inst,leader,by omega,?_⟩
    exact hElect
  exact ⟨⟨hB.1,(hScores 0).1,(hScores 1).1,hB.2.1,hBar,hB.2.2⟩,fun stage => (hScores stage).2⟩

theorem OpeningKeyReturnedWithTrip.steadyRoots {ends : Nat → Option TState}
    (cur : OpeningKeyReturnedWithTrip l X g trips shuffles votes ends) (lane : Nat) (hl : lane < 32)
    : Holds (cur.state lane).regs (steadyIterationRoots l) := by
  exact (cur.steadyRootsAndElections hp hMax hg hw lane hl).1

/-- A selected multi-visit opening enters the recurring state with its actual trip count
and all invariant QK/PV operands. -/
theorem openingSteadyIterationReachedWithPosition {ends : Nat → Option TState} (hTrips : 2 ≤ trips)
    (hBound : trips < 2^31) (cur : OpeningKeyReturnedWithTrip l X g trips shuffles votes ends) :
    ∃ next : SteadyIterationCursor l X g 0 trips shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨s,hS⟩ := cur.advanceLocalWithPosition (pc' := 2275)
    (G := fun _ => [(1189,b32 trips),(2535,b32 l.sharedBase)] ++ steadyIterationRoots l) (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      exact ⟨_,.refl,ht.mono ((holds_append ..).mpr
        ⟨ht.2.2.2.2,cur.steadyRoots hp hMax hg hw lane hl⟩)⟩)
  obtain ⟨next,hNext⟩ := openingSteadyReachedFramedWithPosition hp hTrips hBound s (by
    intro start count h
    rw [steadyIterationRoots_regs]
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel)
  exact ⟨next,hNext.trans hS⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
