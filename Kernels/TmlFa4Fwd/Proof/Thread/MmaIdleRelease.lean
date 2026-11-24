-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRendezvous
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationReadProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierExit
import Kernels.TmlFa4Fwd.Proof.MmaTail
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.CountTake
import Lemmas.Step.TmemReady
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationRecordProgress
import Kernels.TmlFa4Fwd.Proof.Epilogue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Thread.Allocation Tmem.Pair

noncomputable section

private theorem deallocNext {p : Params} {l : Launch} {m : Mem0} {g : Nat} {t : TState}
    (hp : Pre p l m) (hPc : t.pc = 2765) (hFault : t.fault = none)
    (hBase : t.regs 1179 = some (b32 0)) (hWarp : t.regs 1062 = some (b32 12)) :
    ∃ u, u.pc = 2766 ∧ u.fault = none ∧ u.regs 1062 = some (b32 12) ∧
      Next kernel Assumptions.all l g t u
      (.tc (.resource .one none (.dealloc 0 512)) (next u)) := by
  let u := next (setReg t 2682 (b32 512))
  have hu : u.pc = 2766 := congrArg (·+1) hPc
  have hRun : run kernel Assumptions.all l g 1 t = some u := by
    have hc : kernel.code[t.pc]? = some _ := hPc.symm ▸ Flow.code_2765
    have hCore := Assumptions.tauStep_all_eq_nil (L := l) (g := g) (by rw [hPc]; decide) hc rfl
    rw [run, hCore]
    have hOut : out kernel [] l g t = .tau u := by
      rw [out, hFault, hc]
      rfl
    simp only [tauStep, hOut, Option.bind_some, run]
  have hOut : out kernel Assumptions.all l g u =
      .ev (.tc (.resource .one none (.dealloc 0 512)) (next u)) := by
    rw [out_eq_core (by rw [hu]; decide) (by rw [hu]; decide),
      out_event (show u.fault = none from hFault) (hu.symm ▸ Flow.code_2766) rfl rfl]
    change Out.ev (tcTmpl l g u (.tcDealloc .one (.reg 1179) (.reg 2682))) = _
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    have hBase' : u.regs 1179 = some (b32 0) := by simpa [u,next,setReg] using hBase
    have hCol := readBits_b32 (L := l) (g := g) hBase' (by decide)
    have hN := readBits_b32 (L := l) (g := g)
      (show u.regs 2682 = some (b32 512) by rfl) (by decide)
    simp [tcTmpl, hBlock, hCol, hN, Tmem.validColumns, ofExec,
      bind, Except.bind, pure, Except.pure]
  exact ⟨u, hu, hFault, by simpa [u,next,setReg] using hWarp, run_rtg hRun, hOut⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An allocator issues deallocation after its actual final rendezvous can release. -/
theorem mmaDeallocationPrefix (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hFinal : MmaFinalAllocationPrefix l X g)
    (hRelease : FinalAllocationArrival X (g,(X.tr g).length-1) .sync →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g) :
    ∃ j t o, X.get (g,j) = some ⟨2766,.tc (.resource .one none (.dealloc 0 512))⟩ ∧
      X.TcK (g,j) 2 ∧ t.pc = 2767 ∧ t.fault = none ∧ t.regs 1062 = some (b32 12) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  obtain ⟨j,t,o,_,hK,hBar,hPc,hFault,hPrefix,hTail⟩ :=
    hFinal
  obtain ⟨a,_,hRead,hA,hOpening,_⟩ := allocatorReadsResultPrefixWithBase hp hMax hg hw
  have hOrder : allocationBarrierPos l g + 2 ≤ j+1 := by
    have hPc : 1911 < (⟨2764,.bar 2 (some 416) .sync⟩ : Event).pc := by decide
    exact (mmaStartAfterAllocation hp hMax.1 hBar hw hPc).1
  have hSplit : (X.tr g).take (allocationBarrierPos l g+2) ++
      ((X.tr g).take (j+2)).drop (allocationBarrierPos l g+2) = (X.tr g).take (j+2) := by
    have hTake : ((X.tr g).take (j+2)).take (allocationBarrierPos l g+2) =
        (X.tr g).take (allocationBarrierPos l g+2) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [← hTake, List.take_append_drop]
  have hReach := (hOpening.after_returned_prefix (hSplit.symm ▸ hPrefix)).returning_reach
  obtain ⟨hWarp,hBase⟩ := mmaAllocationRegistersOfPrefix hReach (by rw [hA.1]) (by rw [hPc]; decide)
    ⟨hA.2.1.symm ▸ Nat.zero_le _, hA.2.2.1, fun _ => hA.2.1⟩ hA.2.2.2.2.2.1 hA.2.2.2.2.1
  obtain ⟨u, hu, huFault, huWarp, hNext⟩ := deallocNext (g := g) hp hPc hFault hBase hWarp
  have hj : j+2 < (X.tr g).length := by
    by_contra! hLe
    have hEq : j+2 = (X.tr g).length := Nat.le_antisymm (len_of_get hBar) hLe
    have hPos : (X.tr g).length-1 = j+1 := by omega
    obtain ⟨Y,hY,hTr,hReady⟩ := hRelease
      (hPos.symm ▸ FinalAllocationArrival.of_decoded (by decide) hBar)
    have hStarted : Y.tr g ≠ [] := by
      rw [hTr]
      intro hNil
      rw [hNil,List.length_nil] at hEq
      omega
    have hFull : Run kernel Assumptions.all l g {} (Y.tr g) (some t) := by
      rw [hTr, ← List.take_of_length_le hLe]
      exact hPrefix
    exact hY.not_grows (Step.tccoll_counted_extension hY.1 hg (.inl hStarted) hReady hFull
      hNext.steps ⟨_,hNext.stop,rfl,rfl⟩ rfl
      (hY.1.tmemPairResult.snoc_not_wr nofun) (hY.1.tcRead_snoc_tc nofun)
      (Assumptions.wfStep.quiet hY.1 le_snoc rfl (Execution.noNewRead_snoc rfl)))
  obtain ⟨_,_,he,⟨rfl,hRet⟩,hRest⟩ := hNext.continuing_at_nonempty (pos := j+2)
    (by rintro _ ⟨_,h⟩; cases h) hTail
    (fun h => (Nat.not_le_of_lt hj) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (j+2+1)) (some (next u)) := by
    rw [List.take_succ_eq_append_getElem hj, (List.getElem?_eq_some_iff.mp he).2]
    exact hPrefix.snoc hNext.steps ⟨_,hNext.stop,rfl,rfl⟩
  have hGet : X.get (g,j+2) = some ⟨2766,.tc (.resource .one none (.dealloc 0 512))⟩ := hu ▸ he
  obtain ⟨⟨kind, hGetRel, hMark⟩, hCount⟩ := hK
  have hRel := countP_take_succ (p := isTcColl) hGetRel hMark
  have hBarCount := countP_take_succ_false (p := isTcColl) hBar rfl
  have hOrdinal : X.TcK (g,j+2) 2 := by
    refine ⟨⟨_,hGet,rfl⟩,?_⟩
    change ((X.tr g).take (j+1+1)).countP isTcColl = 2
    rw [hBarCount,hRel,hCount]
  exact ⟨j+2,next u,o,hGet,hOrdinal,congrArg (·+1) hu,huFault,huWarp,hPast,hRest⟩

/-- The idle allocator issues deallocation after its final named rendezvous can release. -/
theorem idleMmaDeallocationPrefix (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    (hRelease : FinalAllocationArrival X (g,(X.tr g).length-1) .sync →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g) :
    ∃ j t o, X.get (g,j) = some ⟨2766,.tc (.resource .one none (.dealloc 0 512))⟩ ∧
      X.TcK (g,j) 2 ∧ t.pc = 2767 ∧ t.fault = none ∧ t.regs 1062 = some (b32 12) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o :=
  mmaDeallocationPrefix hp hMax hg hw (idleMmaTerminalPrefix hp hMax hg hw hProtected hIdle)
    hRelease

/-- All allocator lanes have recorded their final allocation rendezvous. -/
def MmaWarpAtFinalAllocation (l : Launch) (X : Execution) (cta : Nat) : Prop :=
  ∀ lane < l.threads, warpIndex l lane = 12 → lane/l.block = cta →
    MmaFinalAllocationPrefix l X lane

private theorem deallocationCovered (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g j : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hFinal : MmaWarpAtFinalAllocation l X (g/l.block))
    (hRelease : ∀ lane < l.threads, warpIndex l lane = 12 → lane/l.block = g/l.block →
      FinalAllocationArrival X (lane,(X.tr lane).length-1) .sync →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y lane)
    (hK : X.TcK (g,j) 2) :
    Covered l X (g,j) := by
  let c := g / l.block
  let thread (lane : Fin 32) := c * l.block + 384 + lane.val
  have hc : c < l.grid := NamedBar.cta_lt hg
  have laneFacts (lane : Fin 32) :
      thread lane < l.threads ∧ thread lane / l.block = c ∧ warpIndex l (thread lane) = 12 := by
    have hLane := lane.isLt
    have hWithin : 384 + lane.val < l.block := by rw [hp.block]; omega
    obtain ⟨hCta, hMod⟩ := NamedBar.lane_cta (c := c) (by rw [hp.block]; decide) hWithin
    have hThread : thread lane = c * l.block + (384 + lane.val) := Nat.add_assoc _ _ _
    rw [hThread]
    exact ⟨NamedBar.cta_thread_lt hc hWithin, hCta, by unfold warpIndex; rw [hMod]; omega⟩
  have laneIssue (lane : Fin 32) : ∃ k,
      X.get (thread lane,k) = some ⟨2766,.tc (.resource .one none (.dealloc 0 512))⟩ ∧
      X.TcK (thread lane,k) 2 := by
    obtain ⟨hThread, hCta, hWarp⟩ := laneFacts lane
    obtain ⟨k, _, _, he, hOrdinal, _, _, _, _, _⟩ :=
      mmaDeallocationPrefix hp hMax hThread hWarp (hFinal _ hThread hWarp hCta)
        (hRelease _ hThread hWarp hCta)
    exact ⟨k, he, hOrdinal⟩
  let w : WarpRequest := ⟨c, 12, fun lane => Classical.choose (laneIssue lane),
    2766, none, .dealloc 0 512⟩
  have hValid : w.Valid l X .one := by
    have hBlock : 416 ≤ l.block := by rw [hp.block]; decide
    exact ⟨hc, hBlock, fun lane => (Classical.choose_spec (laneIssue lane)).1,
      2, fun lane => (Classical.choose_spec (laneIssue lane)).2⟩
  have hPart : Participates l w (g,j) := by
    let lane : Fin 32 := ⟨laneOf l g, Nat.mod_lt _ (by decide)⟩
    have hSameThread : thread lane = g := by
      change g / l.block * l.block + 384 + g % l.block % 32 = g
      have h := Nat.div_add_mod g l.block
      have hw' : g % l.block / 32 = 12 := hw
      rw [Nat.mul_comm] at h
      omega
    have hLaneK : X.TcK (thread lane, w.indices lane) 2 :=
      (Classical.choose_spec (laneIssue lane)).2
    rw [hSameThread] at hLaneK
    exact ⟨lane, Prod.ext hSameThread (Execution.TcK.unique hLaneK hK)⟩
  by_cases hRecorded : ∃ r ∈ X.tmemHistory c, r.own = w
  · obtain ⟨r, hHist, hOwn⟩ := hRecorded
    have hEvent := ((hMax.1.tmemPair.1 c).1 r hHist).2.2.2.2.1 0
    rw [hOwn, hValid.2.2.1 0] at hEvent
    have hGroup : r.group = .one := by
      have hKind := (Event.mk.inj (Option.some.inj hEvent)).2
      exact (TcKind.resource.inj (Kind.tc.inj hKind)).1.symm
    exact ⟨[r.own], .inl ⟨c, r, hHist, hGroup, rfl⟩, r.own, List.mem_singleton_self _,
      hOwn ▸ hPart⟩
  · exfalso
    let r : Requests := ⟨w, .one, .dealloc 0 512⟩
    have hReady : Step.EntryReady l X c r := by
      refine ⟨⟨hMax.1.cluster.1, rfl, hValid⟩, ?_, ?_, rfl, ?_⟩
      · intro _ candidate hm earlier group hEarlier hBefore i hi
        obtain rfl := List.mem_singleton.mp hm
        obtain ⟨hCta, hWarp, hBefore⟩ := hBefore
        obtain ⟨lane, rfl⟩ := hi
        obtain ⟨k, hOrdinal⟩ := hEarlier.2.2.2
        have hEarlyK := hOrdinal lane
        have hSameThread : (earlier.event l lane).1 = thread lane := by
          simp only [WarpRequest.event, hCta, hWarp]
          rfl
        change X.TcK ((earlier.event l lane).1, earlier.indices lane) k at hEarlyK
        rw [hSameThread] at hEarlyK
        have hEarlyGet := hEarlier.2.2.1 lane
        change X.get ((earlier.event l lane).1, earlier.indices lane) = _ at hEarlyGet
        rw [hSameThread] at hEarlyGet
        have hStep := countP_take_succ (p := isTcColl) hEarlyGet rfl
        have hCount := countP_take_mono isTcColl (X.tr (thread lane))
          (show earlier.indices lane + 1 ≤ w.indices lane by simpa [r] using hBefore lane)
        have hAt := (Classical.choose_spec (laneIssue lane)).2.2
        change ((X.tr (thread lane)).take (w.indices lane)).countP isTcColl = 2 at hAt
        have hEarlyAt := hEarlyK.2
        change ((X.tr (thread lane)).take (earlier.indices lane)).countP isTcColl = k at hEarlyAt
        change ((X.tr (thread lane)).take (earlier.indices lane+1)).countP isTcColl = _ at hStep
        have hk : k < 2 := by rw [hStep,hEarlyAt,hAt] at hCount; omega
        obtain ⟨hThread, hCta, hW⟩ := laneFacts lane
        change Covered l X ((earlier.event l lane).1, earlier.indices lane)
        rw [hSameThread]
        rcases Nat.eq_zero_or_pos k with hZero | hPos
        · have hOpening := openingCollectiveOrdinal hp hMax hThread hW
          have hEarly : X.TcK (thread lane,earlier.indices lane) 0 := hZero ▸ hEarlyK
          have hIndex : earlier.indices lane = 6 := Execution.TcK.unique hEarly hOpening
          rw [hIndex]
          exact openingCovered hp hMax hThread hW
        · have hOne : k = 1 := by omega
          obtain ⟨i,_,_,hRel,hRelK,_,_,_,_,_⟩ :=
            hFinal _ hThread hW hCta
          have hEarly : X.TcK (thread lane,earlier.indices lane) 1 := hOne ▸ hEarlyK
          have hIndex : earlier.indices lane = i := Execution.TcK.unique hEarly hRelK
          rw [hIndex]
          exact hRel
      · exact fun q hMem hEq => hRecorded ⟨q,hMem,hEq⟩
      · apply run_append_ne_blocked (hMax.1.tmemPair.1 c).2.2
        intro s _
        exact perform_ne_blocked (fun _ _ => by intro h; cases h)
    obtain ⟨Y, hY, hLe, hSize, _⟩ := Step.entry_counted hMax.1 hReady
      (Assumptions.wfStep.quiet hMax.1 le_recordEntry rfl (Execution.noNewRead_of_tr rfl))
    exact hMax.not_grows ⟨Y, hY, hLe, hSize⟩



private theorem terminalExitNext {l : Launch} {g : Nat} {t : TState}
    (hPc : t.pc = 2767) (hFault : t.fault = none)
    (hWarp : t.regs 1062 = some (b32 12)) :
    ∃ u, u.pc = 9205 ∧ Next kernel Assumptions.all l g t u .exit := by
  let v := { t with pc := 3099 }
  have hTau : Tau kernel Assumptions.all l g t v := by
    rw [Tau, out_eq_core (by rw [hPc]; decide) (by rw [hPc]; decide), out, hFault, hPc,
      Flow.code_2767]
    rfl
  have hModel {s : TState} (hs : s.pc ∈ [3099, 3100, 7742, 7743, 7744, 9205]) :
      out kernel Assumptions.all l g s = out kernel [] l g s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    apply epilogue_out_all_eq_nil
    unfold EpiloguePc
    omega
  obtain ⟨u, hu, hSite, hOut⟩ :=
    finishSchedulerOfWarpWith l g v hModel rfl hFault (.inl rfl) hWarp
  exact ⟨u,hSite,.head hTau (run_rtg hu),hOut⟩

private theorem terminalExitSuffix {l : Launch} {g : Nat} {t u : TState}
    {es : List Event} {o : Option TState} (hr : Run kernel Assumptions.all l g t es o)
    (hn : Next kernel Assumptions.all l g t u .exit) (hMore : es ≠ []) :
    es = [⟨u.pc,.exit⟩] := by
  have hs : Stops kernel Assumptions.all l g u := ⟨_,hn.stop⟩
  cases hr with
  | nil => exact (hMore rfl).elim
  | step hLocal he _ =>
    obtain rfl := stop_unique hLocal hn.steps (stops_of_estep he) hs
    obtain ⟨_, hOut, hFire⟩ := he
    rw [hn.stop] at hOut
    obtain rfl := Out.ev.inj hOut
    cases hFire.2
  | last hLocal he =>
    obtain rfl := stop_unique hLocal hn.steps (stops_of_estep he) hs
    obtain ⟨_, hOut, hFire⟩ := he
    rw [hn.stop] at hOut
    obtain rfl := Out.ev.inj hOut
    rw [hFire.1]

/-- The allocator returns from deallocation and exits after the final rendezvous. -/
theorem mmaExitsOfFinalAllocation (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hFinal : MmaWarpAtFinalAllocation l X (g/l.block))
    (hRelease : ∀ lane < l.threads, warpIndex l lane = 12 → lane/l.block = g/l.block →
      FinalAllocationArrival X (lane,(X.tr lane).length-1) .sync →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y lane) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  obtain ⟨j,t,o,he,hK,hPc,hFault,hWarp,hPrefix,hTail⟩ :=
    mmaDeallocationPrefix hp hMax hg hw (hFinal g hg hw rfl) (hRelease g hg hw rfl)
  have hCovered := deallocationCovered hp hMax hg hw hFinal hRelease hK
  obtain ⟨u, hu, hn⟩ := terminalExitNext (l := l) (g := g) hPc hFault hWarp
  have hMore : j+1 < (X.tr g).length := by
    by_contra! hLe
    have hj : j+1 = (X.tr g).length := Nat.le_antisymm (len_of_get he) hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hj; omega
    have hRel : Step.Released l X g := by
      constructor
      intro site kind hGet _
      have hPos : (X.tr g).length - 1 = j := by omega
      rw [hPos] at hGet ⊢
      rw [he] at hGet
      cases hGet
      exact ReturnReady.ready hMax.1.tmemPair he
        ⟨hCovered.performed hMax.1.tmemPair, fun _ => hCovered⟩ fun _ h _ => by cases h
    rw [List.take_of_length_le hLe] at hPrefix
    have hExit : EStep kernel Assumptions.all l g u ⟨u.pc,.exit⟩ none :=
      ⟨_,hn.stop,rfl,rfl⟩
    exact hMax.not_grows (Step.plain_counted_extension hMax.1 hg (.inl hStarted)
      hRel hPrefix hn.steps hExit trivial rfl nofun nofun nofun rfl
      (hMax.1.tmemPairResult.snoc_not_wr nofun)
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl)))
  have hs := terminalExitSuffix hTail hn
    (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
  refine ⟨j+1,⟨u.pc,.exit⟩,?_ ,rfl⟩
  have hGet : ((X.tr g).drop (j+1))[0]? = some ⟨u.pc,.exit⟩ := by rw [hs]; rfl
  rwa [List.getElem?_drop, Nat.add_zero] at hGet


/-- An idle allocator returns from deallocation and records its final exit. -/
theorem idleMmaExits (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    (hRelease : ∀ lane < l.threads, warpIndex l lane = 12 → lane/l.block = g/l.block →
      FinalAllocationArrival X (lane,(X.tr lane).length-1) .sync →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y lane) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit :=
  mmaExitsOfFinalAllocation hp hMax hg hw
    (fun _ hl hw' hc => idleMmaTerminalPrefix hp hMax hl hw' hProtected (hc ▸ hIdle))
    hRelease


end
end PTX.Kernels.TmlFa4Fwd.Mma
