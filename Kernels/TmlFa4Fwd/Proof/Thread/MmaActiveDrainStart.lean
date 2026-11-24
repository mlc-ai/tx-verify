-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalOutputProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaDrainWords
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import Lemmas.Step.ProtectedReadProgress
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.CountTake
import Lemmas.Flow.NthEv
import Kernels.TmlFa4Fwd.Proof.Thread.MmaScanStartProgress
import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Flow.Code.Part041

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue
open Thread.Allocation (drainRoots preserveDrainRoots knownFloors firstGroupScanLaunchFrame
  firstScanCursor)
open Correction (OpeningTripCursor)

set_option maxRecDepth 100000 in
private theorem drainFloor : knownFloors 2647 := ⟨by kernel_rfl,by kernel_rfl⟩
set_option maxRecDepth 100000 in
private theorem startupFloor : knownFloors 1981 := ⟨by kernel_rfl,by kernel_rfl⟩

private theorem lateEvents {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {ending : Option TState}
    (h : Run kernel Assumptions.all l g s events ending) (hPc : 2647 ≤ s.pc) :
    ∀ e ∈ events, 2647 ≤ e.pc := by
  obtain ⟨_,hWalk⟩ := walkFromRun h
  exact Thread.eventTailEvents drainFloor.1 drainFloor.2 hWalk hPc

set_option maxRecDepth 100000 in
private theorem exitFloor : knownFloors 2768 := ⟨by kernel_rfl,by kernel_rfl⟩

private theorem lowerOnReach {floor : Nat} (hFloor : knownFloors floor)
    {l : Launch} {g : Nat} {t u : TState} {es : List Event}
    (h : TraceReach kernel Assumptions.all l g t es u) (ht : floor ≤ t.pc) : floor ≤ u.pc := by
  induction h with
  | refl => exact ht
  | tau hS _ ih => exact ih (Thread.eventTailStepOfAudit hFloor.1 hFloor.2 ht
      (.inl ⟨rfl,hS⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit hFloor.1 hFloor.2 ht
      (.inr ⟨_,rfl,he⟩))

private theorem drainRootsPreserved {p : Params} {l : Launch} {g : Nat} {t u : TState}
    {es : List Event} (h : TraceReach kernel Assumptions.all l g t es u)
    (hLo : 1981 ≤ t.pc) (hHi : u.pc < 2768) (hf : Holds t.regs (drainRoots p l g)) :
    Holds u.regs (drainRoots p l g) := by
  induction h with
  | refl => exact hf
  | @tau a b _ _ he hTail ih =>
    let step : WStep kernel Assumptions.all l g a none b := .inl ⟨rfl,he⟩
    have hBound : a.pc < 2768 := Nat.lt_of_not_ge fun bad =>
      (Nat.not_le_of_lt hHi) (lowerOnReach exitFloor (.tau he hTail) bad)
    exact ih (Thread.eventTailStepOfAudit startupFloor.1 startupFloor.2 hLo step) hHi
      (preserveDrainRoots hLo (by omega) step hf)
  | @event a b _ _ _ he hTail ih =>
    let step := (.inr ⟨_,rfl,he⟩ : WStep kernel Assumptions.all l g a (some _) b)
    have hBound : a.pc < 2768 := Nat.lt_of_not_ge fun bad =>
      (Nat.not_le_of_lt hHi) (lowerOnReach exitFloor (.event he hTail) bad)
    exact ih (Thread.eventTailStepOfAudit startupFloor.1 startupFloor.2 hLo step) hHi
      (preserveDrainRoots hLo (by omega) step hf)

/-- These startup operands are still live when the terminal scheduler scans again. -/
def drainSchedulerCarry (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(337,.pred (!decide (laneHasRequest (laneOf l g) p.batch))),(7139,b32 p.heads)]

def activeDrainRoots (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  drainSchedulerCarry p l g ++ drainRoots p l g

set_option maxRecDepth 100000 in
private theorem firstScanFloor : knownFloors 1960 := ⟨by kernel_rfl,by kernel_rfl⟩

private theorem preserveDrainCarry {p : Params} {l : Launch} {g : Nat} {t u : TState}
    {es : List Event} (h : TraceReach kernel Assumptions.all l g t es u)
    (hLo : 1960 ≤ t.pc) (hHi : u.pc < 2768) (hf : Holds t.regs (drainSchedulerCarry p l g)) :
    Holds u.regs (drainSchedulerCarry p l g) := by
  have step {s v : TState} {e : Option Event} (hl : 1960 ≤ s.pc) (hh : s.pc < 2768)
      (he : WStep kernel Assumptions.all l g s e v)
      (hF : Holds s.regs (drainSchedulerCarry p l g)) :
      Holds v.regs (drainSchedulerCarry p l g) := by
    have hCode : ((kernel.code.drop 1960).take (2768-1960)).all
        (fun i => [337,7139].all (fun r => !(mmaWrites i.op).contains r)) = true := by
      decide +kernel
    apply holdsSchedulerFrame (regs := [337,7139]) hF
    · intro r hr
      apply mmaStepReg (by omega) hh _ he
      intro i hi
      have hI := List.all_eq_true.mp hCode i (by
        apply List.mem_of_getElem? (i := s.pc-1960)
        rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hl])
      simpa using List.all_eq_true.mp hI r hr
    · intro pair hh
      simpa only [drainSchedulerCarry,List.map_cons,List.map_nil] using
        List.mem_map_of_mem (f := Prod.fst) hh
  induction h with
  | refl => exact hf
  | @tau a b _ _ he hTail ih =>
    let he' : WStep kernel Assumptions.all l g a none b := .inl ⟨rfl,he⟩
    have hBound : a.pc < 2768 := Nat.lt_of_not_ge fun bad =>
      (Nat.not_le_of_lt hHi) (lowerOnReach exitFloor (.tau he hTail) bad)
    exact ih (lowerOnReach firstScanFloor (.tau he (.refl _)) hLo) hHi (step hLo hBound he' hf)
  | @event a b _ _ _ he hTail ih =>
    let he' := (.inr ⟨_,rfl,he⟩ : WStep kernel Assumptions.all l g a (some _) b)
    have hBound : a.pc < 2768 := Nat.lt_of_not_ge fun bad =>
      (Nat.not_le_of_lt hHi) (lowerOnReach exitFloor (.event he hTail) bad)
    exact ih (lowerOnReach firstScanFloor (.event he (.refl _)) hLo) hHi (step hLo hBound he' hf)

/-- The returned output commit cursor retains its protected scheduler base and lane indices. -/
theorem drainRootsAtOutputCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (c : SchedulerWarpReached l X g 2647 F shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    Holds (c.state lane).regs (activeDrainRoots p l (warpLane l g lane)) := by
  let th := warpLane l g lane
  have hSame := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  obtain ⟨j,e,t,_,he,hJ,_,_,ht,hPrefix,_⟩ :=
    firstGroupScanLaunchFrame hp hMax hSame.1.2.1 (hSame.2.symm.trans hw) hCuQ
  have hOrder : j < c.pos lane := by
    by_contra! hLe
    have hGet : ((X.tr th).drop (c.pos lane))[j-c.pos lane]? = some e := by
      rw [List.getElem?_drop,Nat.add_sub_of_le hLe]
      exact he
    have hMore : (X.tr th).drop (c.pos lane) ≠ [] := by intro h; simp [h] at hGet
    have hSuffix := (c.continuation lane hl).after_local_nonempty (c.localSteps lane hl) hMore
    have hBound := lateEvents hSuffix (c.checkpoint lane hl).1.ge _ (List.mem_of_getElem? hGet)
    omega
  let events := (X.tr th).take (c.pos lane)
  have hSplit := List.take_append_drop (j+1) events
  have hTake : events.take (j+1) = (X.tr th).take (j+1) := by
    simp only [events,List.take_take,Nat.min_eq_left (by omega : j+1 ≤ c.pos lane)]
  rw [hTake] at hSplit
  have hFull : Run kernel Assumptions.all l th {} events (some (c.before lane)) :=
    c.recorded lane hl
  rw [← hSplit] at hFull
  have hPast := (hPrefix.after_returned_prefix hFull).returning_reach.append
    (TraceReach.of_local (c.localSteps lane hl))
  have hExit : (c.state lane).pc < 2768 := by rw [(c.checkpoint lane hl).1]; decide
  have hRoots := drainRootsPreserved hPast ht.1.ge hExit
    (show Holds t.regs (drainRoots p l th) from
      ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,
        holds_lookup ht.2.2.2.2 rfl,trivial⟩)
  obtain ⟨_,u,_,_,hCount,_,hu,hFirst,hLocal,_⟩ :=
    firstScanCursor hp hMax hSame.1.2.1 (hSame.2.symm.trans hw) hCuQ
  let first := firstSchedulerPos p (laneOf l th)+1
  have hEarly : first ≤ j := by
    by_contra! hBefore
    have hLe := countP_take_mono Execution.isShfl (X.tr th) (show j ≤ first by omega)
    have hJ' : ((X.tr th).take j).countP Execution.isShfl = 10 := hJ.2
    have hc : ((X.tr th).take first).countP Execution.isShfl = 5 := hCount
    rw [hJ',hc] at hLe
    omega
  have hCut := List.take_append_drop first events
  have hTake' : events.take first = (X.tr th).take first := by
    simp only [events,List.take_take,Nat.min_eq_left (by omega : first ≤ c.pos lane)]
  rw [hTake'] at hCut
  have hFull' := c.recorded lane hl
  change Run kernel Assumptions.all l th {} events (some (c.before lane)) at hFull'
  rw [← hCut] at hFull'
  have hNonempty : events.drop first ≠ [] :=
    fun hh => (show ¬ events.length ≤ first by
      have hB : c.pos lane ≤ (X.tr th).length := c.bounded lane hl
      simp only [events,List.length_take,Nat.min_eq_left hB]
      omega) (List.drop_eq_nil_iff.mp hh)
  have hPath := ((hFirst.after_returned_prefix hFull').after_local_nonempty hLocal
    hNonempty).returning_reach.append (TraceReach.of_local (c.localSteps lane hl))
  exact (holds_append _ _ _).mpr ⟨preserveDrainCarry hPath hu.1.ge hExit
    ⟨holds_lookup hu.2.2.2.2 rfl,holds_lookup hu.2.2.2.2 rfl,trivial⟩,hRoots⟩

/-- The first word read by the active MMA drain is the protected CuQ word
of the corresponding lane. An out-of-range lane supplies its initial zero. -/
theorem drainFirstWordOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads)
    (c : OpeningTripCursor l X g 2647 (activeDrainRoots p l g)) :
    ∃ d : OpeningTripCursor l X g 2654
      ((7209,b32 (drainCuQ p (laneOf l g)))::(7149,b32 p.batch)::activeDrainRoots p l g),
      d.ending = c.ending ∧
      ((X.tr g).take d.pos).countP Execution.isShfl =
        ((X.tr g).take c.pos).countP Execution.isShfl ∧
      ((X.tr g).take d.pos).countP isFullWarpVote =
        ((X.tr g).take c.pos).countP isFullWarpVote := by
  have hStart := (holds_append _ _ _).mp c.checkpoint.2.2.2.2
  obtain ⟨t,ht,hFrame⟩ := Thread.Allocation.firstDrainGateWithZero hp (c.checkpoint.mono hStart.2)
  have hEnd : t.pc < 2768 := by rw [hFrame.1]; split <;> decide
  have hCarry := preserveDrainCarry (TraceReach.of_local ht) (by rw [c.checkpoint.1]; decide)
    hEnd hStart.1
  have hRegs := hFrame.2.2.2.2.2
  let F := (7149,b32 p.batch)::activeDrainRoots p l g
  have hSaved : Holds t.regs F :=
    ⟨hRegs.1,(holds_append _ _ _).mpr ⟨hCarry,hRegs.2⟩⟩
  let q := laneOf l g
  by_cases hLane : q ≤ p.batch
  · have hT : At t 2651 F := by
      have hPc : t.pc = 2651 := by
        simpa only [q,ite_eq_right (Nat.not_lt_of_ge hLane)] using hFrame.1
      exact ⟨hPc,hFrame.2.1,hFrame.2.2.1,hFrame.2.2.2.1,hSaved⟩
    obtain ⟨u,hu,hU⟩ := Thread.Allocation.firstDrainAddress hp hLane t
      (hT.mono ((holds_append _ _ _).mp hT.2.2.2.2.2).2)
    have hStraight : ((kernel.code.drop 2651).take 1).all
        (fun ins => schedulerFallsThrough ins.op) = true := by decide +kernel
    have hKeep : ((kernel.code.drop 2651).take 2).all
        (fun ins => [7149,337,7139,1180,7506,1072].all (fun r => !(writesRegs ins.op).contains r)) =
          true := by decide +kernel
    have hRoots := holdsSchedulerFrame (regs := [7149,337,7139,1180,7506,1072]) hT.2.2.2.2
      (fun _ hr => schedulerLocalFrame hKeep hStraight hu hT.1.ge (by rw [hT.1]) hr)
      (fun _ h => by
        simpa only [F,activeDrainRoots,drainSchedulerCarry,drainRoots,List.cons_append,
          List.nil_append,List.map_cons,List.map_nil] using List.mem_map_of_mem (f := Prod.fst) h)
    let a : Acc := {loc := globalLoc (p.cuQBase+4*q),size := 4}
    let word := b32 (p.qOffset q)
    have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hRange
    have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
    have hOut : out kernel Assumptions.all l g u = .ev (.read a (afterLoad u [7209])) := by
      rw [out_eq_core (by rw [hU.1]; decide) (by rw [hU.1]; decide),
        out_event hU.2.2.2.1 (hU.1.symm ▸ Flow.code_2653) rfl rfl]
      change Out.ev (loadTmpl [] l g u .global false 32 [7209] 7884 0) = _
      exact congrArg Out.ev (loadTmpl_global hU.2.1 hU.2.2.2.2.1
        (by omega) (by decide)
        (by change (p.cuQBase+4*q)%4 = 0; omega))
    have hLocal := localRun (pc := 2651) (n := 2) (by decide) (by decide) hT.1 hStraight hu
    let hn : Next kernel Assumptions.all l g c.before u (.read a (afterLoad u [7209])) :=
      ⟨c.localSteps.trans (ht.trans (run_rtg hLocal)),hOut⟩
    obtain ⟨he,hPrefix,hTail⟩ := Step.protected_read_of_maximal hMax hg
      (a := a) (value := word) rfl (hp.cuQ q hLane) (hCuQ q hLane)
      hn c.recorded c.remaining c.positive c.bounded c.released
      (Assumptions.wf_snoc_initial hMax.1)
    have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
    have hRead : afterLoad u [7209] (word.toBytes.map some) = next (setReg u 7209 word) := by
      rw [afterLoad_ok hU.2.1 hU.2.2.1 hRebuild]
      simp [next,setReg,hU.2.1,hU.2.2.1]
    have hReady : At (next (setReg u 7209 word)) 2654 ((7209,word)::F) :=
      (hU.mono hRoots).set (by simp [F,activeDrainRoots,drainSchedulerCarry,drainRoots])
    rw [hRead] at hPrefix hTail
    refine ⟨⟨c.pos+1,_,_,c.ending,Nat.succ_pos _,len_of_get he,
      releasedIfLast he (by intro h; cases h),?_,hPrefix,hTail,.refl⟩,rfl,?_,?_⟩
    · simpa only [drainCuQ,ite_eq_left hLane,q,word] using hReady
    · exact countP_take_succ_false he rfl
    · exact countP_take_succ_false he rfl
  · have hReady : At t 2654 ((7209,b32 (drainCuQ p q))::F) := by
      have ht' := hFrame.mono (show Holds t.regs ((7209,b32 0)::F) from
        ⟨hFrame.2.2.2.2.1,hSaved⟩)
      simpa only [drainCuQ,ite_eq_right hLane,ite_eq_left (Nat.lt_of_not_ge hLane),q] using ht'
    exact ⟨⟨c.pos,c.before,t,c.ending,c.positive,c.bounded,c.released,hReady,
      c.recorded,c.remaining,c.localSteps.trans ht⟩,rfl,rfl,rfl⟩

/-- All lanes reached the protected first CuQ words with matching collective ordinals. -/
structure ActiveDrainWords (p : Params) (l : Launch) (X : Execution) (g : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 2654
    (fun i => (7209,b32 (drainCuQ p (laneOf l (warpLane l g i))))::
      (7149,b32 p.batch)::activeDrainRoots p l (warpLane l g i)) shuffles votes ends

/-- Any returned terminal-output cursor reaches the first actual CuQ drain words. -/
theorem drainWordsAtOutputCursor {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (c : SchedulerWarpReached l X g 2647 F shuffles votes ends) :
    Nonempty (ActiveDrainWords p l X g) := by
  let F i := (7209,b32 (drainCuQ p (laneOf l (warpLane l g i))))::
    (7149,b32 p.batch)::activeDrainRoots p l (warpLane l g i)
  have hLane (i : Nat) (hi : i < 32) :
      ∃ d : OpeningTripCursor l X (warpLane l g i) 2654 (F i),
        d.ending = ends i ∧
        ((X.tr (warpLane l g i)).take d.pos).countP Execution.isShfl = shuffles ∧
        ((X.tr (warpLane l g i)).take d.pos).countP isFullWarpVote = votes := by
    have hSame := (Step.sameWarp_lane (by rw [hp.block]) hg hi).1
    obtain ⟨d,hEnd,hSh,hVote⟩ := drainFirstWordOfMaximal hp hMax hCuQ hSame.1.2.1
      ⟨c.pos i,c.before i,c.state i,ends i,c.positive i hi,c.bounded i hi,c.released i hi,
        (c.checkpoint i hi).mono (drainRootsAtOutputCursor hp hMax hCuQ hg hw c i hi),
        c.recorded i hi,c.continuation i hi,c.localSteps i hi⟩
    exact ⟨d,hEnd,hSh.trans (c.ordinals.shfl i hi),hVote.trans (c.ordinals.vote i hi)⟩
  classical
  let d (i : Nat) (hi : i < 32) := Classical.choose (hLane i hi)
  let pos i := if hi : i < 32 then (d i hi).pos else c.pos i
  let before i := if hi : i < 32 then (d i hi).before else c.before i
  let ready i := if hi : i < 32 then (d i hi).ready else c.state i
  refine ⟨⟨shuffles,votes,ends,⟨⟨pos,before,ready,⟨?_,?_⟩,?_,?_,?_⟩,?_,?_,?_,?_⟩⟩⟩
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (Classical.choose_spec (hLane i hi)).2.1
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (Classical.choose_spec (hLane i hi)).2.2
  · intro i hi
    have hEnd : (d i hi).ending = ends i := (Classical.choose_spec (hLane i hi)).1
    simpa only [before,pos,dite_eq_left hi,hEnd] using (d i hi).remaining
  · intro i hi
    simpa only [before,ready,dite_eq_left hi] using (d i hi).localSteps
  · intro i hi
    simpa only [ready,dite_eq_left hi] using (d i hi).checkpoint
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (d i hi).positive
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (d i hi).bounded
  · intro i hi
    simpa only [pos,dite_eq_left hi] using (d i hi).released
  · intro i hi
    simpa only [before,pos,dite_eq_left hi] using (d i hi).recorded

/-- The returned cursor of the two output commits reaches the first actual
CuQ load or its guarded zero in every lane of the scheduled warp. -/
theorem terminalOutputDrainWordsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2635 (fun _ => terminalPvFrame l) shuffles votes ends) :
    Nonempty (ActiveDrainWords p l X g) := by
  obtain ⟨⟨c⟩,_⟩ := terminalOutputCursor hp hMax hg cur
  exact drainWordsAtOutputCursor hp hMax hCuQ hg hw c

/-- The drain warp has read each lane's neighboring CuQ word in its real shuffle. -/
structure ActiveDrainNeighbors (p : Params) (l : Launch) (X : Execution) (g : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 2655 (fun i =>
    let q := fun j => drainCuQ p (laneOf l (warpLane l g j))
    (2633,b32 (q (shflSource .down i 1 31).1)) ::
      (7209,b32 (q i)) :: (7149,b32 p.batch)::activeDrainRoots p l (warpLane l g i))
      shuffles votes ends

theorem ActiveDrainWords.shuffleOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (c : ActiveDrainWords p l X g) :
    Nonempty (ActiveDrainNeighbors p l X g) := by
  let q i := drainCuQ p (laneOf l (warpLane l g i))
  have hFresh : ∀ i < 32, ∀ item ∈
      (7209,b32 (q i)) :: (7149,b32 p.batch)::activeDrainRoots p l (warpLane l g i),
      item.1 ≠ 2633 := by
    intro i _ item hi
    simp only [activeDrainRoots,drainSchedulerCarry,drainRoots,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hOut (i : Nat) (hi : i < 32) :
      out kernel Assumptions.all l (warpLane l g i) (c.reached.state i) =
        .ev (.shfl .down (b32 (q i)) 1 31
          (fun word _ => next (setReg (c.reached.state i) 2633 word))) := by
    let t := c.reached.state i
    have ht := c.reached.checkpoint i hi
    have hq : t.regs 7209 = some (b32 (q i)) := ht.2.2.2.2.1
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    rw [out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_2654) rfl rfl]
    change Out.ev (shflTmpl l (warpLane l g i) t .down 2633 none
      (.reg 7209) (.imm 1) (.imm 31) (.imm (-1))) = _
    simp [shflTmpl,readValue,readReg,hq,hBlock,b32,Value.bytes,readBits,pure,Except.pure,t]
    rfl
  obtain ⟨d⟩ := c.reached.consumeShuffle hp hMax hg .down
    (fun i => b32 (q i)) (fun _ => 1) (fun _ => 31) hFresh hOut
  exact ⟨⟨c.shuffles+1,c.votes,c.ends,d⟩⟩

end PTX.Kernels.TmlFa4Fwd.Mma
