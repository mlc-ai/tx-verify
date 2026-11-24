-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRoute
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierExit
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationRecordProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part043
import Lemmas.Step.TmemReady
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Thread.Allocation Tmem.Pair

noncomputable section

/-- The actual returning prefix of the allocator warp's relinquish issue. -/
def MmaRelinquishPrefix (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ j s o, X.get (g,j) = some ⟨2763,.tc (.resource .one none .relinquish)⟩ ∧
    X.TcK (g,j) 1 ∧ s.pc = 2764 ∧ s.fault = none ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some s) ∧
    Run kernel Assumptions.all l g s ((X.tr g).drop (j+1)) o

/-- Actual relinquish prefixes for all lanes of an allocator warp. -/
def MmaWarpRelinquished (l : Launch) (X : Execution) (cta : Nat) : Prop :=
  ∀ lane < l.threads, warpIndex l lane = 12 → lane/l.block = cta → MmaRelinquishPrefix l X lane

/-- Actual returning prefix reaching the second allocation rendezvous. -/
def MmaFinalAllocationPrefix (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ j s o, Covered l X (g,j) ∧ X.TcK (g,j) 1 ∧
    X.IsBarrier (g,j+1) 2 (some 416) 2764 ∧ s.pc = 2765 ∧ s.fault = none ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (j+2)) (some s) ∧
    Run kernel Assumptions.all l g s ((X.tr g).drop (j+2)) o

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem relinquishCovered {g j : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hLanes : MmaWarpRelinquished l X (g/l.block)) (hK : X.TcK (g,j) 1) :
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
      X.get (thread lane,k) = some ⟨2763,.tc (.resource .one none .relinquish)⟩ ∧
      X.TcK (thread lane,k) 1 := by
    obtain ⟨hThread, hCta, hWarp⟩ := laneFacts lane
    obtain ⟨k, _, _, he, hOrdinal, _, _, _, _⟩ :=
      hLanes _ hThread hWarp hCta
    exact ⟨k, he, hOrdinal⟩
  let w : WarpRequest := ⟨c, 12, fun lane => Classical.choose (laneIssue lane),
    2763, none, .relinquish⟩
  have hValid : w.Valid l X .one := by
    have hBlock : 416 ≤ l.block := by rw [hp.block]; decide
    exact ⟨hc, hBlock, fun lane => (Classical.choose_spec (laneIssue lane)).1,
      1, fun lane => (Classical.choose_spec (laneIssue lane)).2⟩
  have hPart : Participates l w (g,j) := by
    let lane : Fin 32 := ⟨laneOf l g, Nat.mod_lt _ (by decide)⟩
    have hSameThread : thread lane = g := by
      change g / l.block * l.block + 384 + g % l.block % 32 = g
      have h := Nat.div_add_mod g l.block
      have hw' : g % l.block / 32 = 12 := hw
      rw [Nat.mul_comm] at h
      omega
    have hLaneK : X.TcK (thread lane, w.indices lane) 1 :=
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
    let r : Requests := ⟨w, .one, .relinquish⟩
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
        change ((X.tr (thread lane)).take (w.indices lane)).countP isTcColl = 1 at hAt
        have hEarlyAt := hEarlyK.2
        change ((X.tr (thread lane)).take (earlier.indices lane)).countP isTcColl = k at hEarlyAt
        change ((X.tr (thread lane)).take (earlier.indices lane+1)).countP isTcColl = _ at hStep
        have hk : k = 0 := by rw [hStep, hEarlyAt, hAt] at hCount; omega
        obtain ⟨hThread, _, hW⟩ := laneFacts lane
        have hOpening := openingCollectiveOrdinal hp hMax hThread hW
        have hIndex := Execution.TcK.unique (hk ▸ hEarlyK) hOpening
        change Covered l X ((earlier.event l lane).1, earlier.indices lane)
        rw [hSameThread,hIndex]
        exact openingCovered hp hMax hThread hW
      · exact fun q hMem hEq => hRecorded ⟨q,hMem,hEq⟩
      · apply run_append_ne_blocked (hMax.1.tmemPair.1 c).2.2
        intro s _
        exact perform_ne_blocked (fun _ _ => by intro h; cases h)
    obtain ⟨Y, hY, hLe, hSize, _⟩ := Step.entry_counted hMax.1 hReady
      (Assumptions.wfStep.quiet hMax.1 le_recordEntry rfl (Execution.noNewRead_of_tr rfl))
    exact hMax.not_grows ⟨Y, hY, hLe, hSize⟩

/-- The allocator warp completes relinquish and reaches the final allocation rendezvous. -/
theorem mmaFinalAllocationPrefix {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hLanes : MmaWarpRelinquished l X (g/l.block)) : MmaFinalAllocationPrefix l X g := by
  obtain ⟨j, s, o, he, hK, hPc, hFault, hPrefix, hTail⟩ := hLanes g hg hw rfl
  have hCovered := relinquishCovered hp hMax hg hw hLanes hK
  have hOut : out kernel Assumptions.all l g s = .ev (.bar 2 (next s) (some 416) .sync) := by
    rw [out_eq_core (by rw [hPc]; decide) (by rw [hPc]; decide),
      out_event hFault (by rw [hPc]; exact Flow.code_2764) rfl rfl]
    change Out.ev (barTmpl l g s (.imm 2) (some (.imm 416)) .sync) = _
    have hId : readBits l g s 32 (.imm 2) = .ok (BitVec.ofNat 64 2) := rfl
    have hN : readBits l g s 32 (.imm 416) = .ok (BitVec.ofNat 64 416) := rfl
    simp only [barTmpl, hId, hN, hp.block]
    rfl
  have hPos : j + 1 < (X.tr g).length := by
    by_contra! hNo
    have hEq : j + 1 = (X.tr g).length := Nat.le_antisymm (len_of_get he) hNo
    have hStarted : X.tr g ≠ [] := by intro h; rw [h, List.length_nil] at hEq; omega
    have hReleased : Step.Released l X g := by
      constructor
      intro site kind hGet _
      have hLast : (X.tr g).length - 1 = j := by omega
      rw [hLast] at hGet ⊢
      rw [he] at hGet
      cases hGet
      exact ReturnReady.ready hMax.1.tmemPair he
        ⟨hCovered.performed hMax.1.tmemPair, fun _ => hCovered⟩ fun _ h _ => by cases h
    have hRun := hPrefix
    rw [hEq, List.take_length] at hRun
    obtain ⟨Y, hY, hLe, hSize⟩ := Step.bar_counted_extension hMax.1 hg
      (.inl hStarted) hReleased (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl))
      hRun .refl ⟨_, hOut, rfl, rfl⟩
    exact hMax.not_grows ⟨Y, hY, hLe, hSize⟩
  have hn : Next kernel Assumptions.all l g s s (.bar 2 (next s) (some 416) .sync) :=
    ⟨.refl, hOut⟩
  obtain ⟨_, _, hGet, ⟨rfl, hReturn⟩, hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hPos) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hReturn
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1+1)) (some (next s)) := by
    rw [List.take_succ_eq_append_getElem hPos, (List.getElem?_eq_some_iff.mp hGet).2]
    exact hPrefix.snoc .refl ⟨_, hOut, rfl, rfl⟩
  exact ⟨j,next s,o,hCovered,hK,hPc ▸ hGet, congrArg (· + 1) hPc, hFault, hPast, hRest⟩

omit hp hMax in
/-- A terminal allocator prefix records the semantic final allocation arrival. -/
theorem MmaFinalAllocationPrefix.arrived {l : Launch} {X : Execution} {g : Nat}
    (h : MmaFinalAllocationPrefix l X g) :
    ∃ j, FinalAllocationArrival X (g,j) .sync := by
  obtain ⟨j,_,_,_,_,he,_,_,_,_⟩ := h
  exact ⟨j+1,FinalAllocationArrival.of_decoded (by decide) he⟩

/-- The idle allocator reaches the final rendezvous by its scheduler bypass. -/
theorem idleMmaTerminalPrefix {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    MmaFinalAllocationPrefix l X g := by
  apply mmaFinalAllocationPrefix hp hMax hg hw
  intro lane hl hw' hc
  obtain ⟨j,s,o,he,hK,hPc,hFault,hPast,hRest⟩ :=
    idleMmaRelinquishPrefixOfMaximal hp hMax hl hw' hProtected (hc ▸ hIdle)
  exact ⟨j,s,o,he,hK,hPc,hFault,hPast,hRest⟩

/-- The idle MMA warp completes relinquish and issues its terminal allocation rendezvous. -/
theorem idleMmaReachesTerminalRendezvous {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ j, Covered l X (g,j) ∧ X.IsBarrier (g,j+1) 2 (some 416) 2764 := by
  obtain ⟨j, _, _, hCovered, _, he, _, _, _, _⟩ :=
    idleMmaTerminalPrefix hp hMax hg hw hProtected hIdle
  exact ⟨j,hCovered,he⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
