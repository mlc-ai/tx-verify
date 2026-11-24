-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocatorExit
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
import Kernels.TmlFa4Fwd.Proof.MmaResources
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Kernels.TmlFa4Fwd.Flow.Code.Part043
import Lemmas.Tmem.TmemPairOrder
import Lemmas.Tmem.TmemPairRecord

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Mma Prologue Tmem.Pair

private def resourceRank (a : Tmem.Action) : Nat :=
  match a with
  | .alloc .. => 0
  | .relinquish => 1
  | .dealloc .. => 2

private theorem tailReturnsNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t u : TState} {pc : Nat} {group : CtaGroup} {dst : Option Loc}
    {req : Tmem.Request} (hSite : pc = 2763 ∨ pc = 2766)
    (he : EStep kernel Assumptions.all l g t ⟨pc, .tc (.resource group dst req)⟩ (some u)) :
    u.pc = pc + 1 := by
  have hPc : t.pc = pc := (estep_source_pc he).symm
  obtain ⟨ins, hCode, _, hf⟩ := estep_event_source he
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rcases hSite with rfl | rfl
  · rw [hPc, Flow.code_2763] at hCode
    obtain rfl := Option.some.inj hCode
    simp only [eventTmpl, tcTmpl, hBlock, ↓reduceIte, pure, Except.pure, ofExec, Fires] at hf
    rw [Option.some.inj hf.2, next, hPc]
  · rw [hPc, Flow.code_2766] at hCode
    obtain rfl := Option.some.inj hCode
    cases hBase : readBits l g t 32 (.reg 1179) with
    | error f =>
      simp [eventTmpl, tcTmpl, hBlock, hBase, bind, Except.bind, ofExec, Fires] at hf
    | ok base =>
      cases hCount : readBits l g t 32 (.reg 2682) with
      | error f =>
        simp [eventTmpl, tcTmpl, hBlock, hBase, hCount, bind, Except.bind, ofExec, Fires] at hf
      | ok columns =>
        by_cases valid : Tmem.validColumns columns.toNat = true
        · simp only [eventTmpl, tcTmpl, hBlock, ↓reduceIte, hBase, hCount, valid,
            bind, Except.bind, pure, Except.pure, ofExec, Fires] at hf
          rw [Option.some.inj hf.2, next, hPc]
        · simp [eventTmpl, tcTmpl, hBlock, hBase, hCount, valid, bind, Except.bind, throw,
            throwThe, MonadExceptOf.throw, ofExec, Fires] at hf

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A collective at the resource tail cannot precede a return to its own site. -/
theorem tailPrecedesHigherSite {g i j pc : Nat} {group : CtaGroup} {dst : Option Loc}
    {req : Tmem.Request} {e : Event} (he : X.get (g,i) = some ⟨pc, .tc (.resource group dst req)⟩)
    (hLater : X.get (g,j) = some e) (hOrder : i < j) (hSite : pc = 2763 ∨ pc = 2766)
    : pc < e.pc := by
  have hThread := event_thread_lt hX he
  obtain ⟨_, hr⟩ := hX.thr g hThread
  have hLength : j < (X.tr g).length := PTX.len_of_get hLater
  obtain ⟨t, u, hStep, hRun⟩ := hr.after_event he (by omega)
  have hCont := tailReturnsNext hp hSite hStep
  have hGet : ((X.tr g).drop (i+1))[j-(i+1)]? = some e := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
  obtain ⟨v, o, hReach, hEvent⟩ := hRun.before_event hGet
  have hPc := estep_source_pc hEvent
  rcases hSite with rfl | rfl
  · have hFloor := resourceSuffixFloor .relinquish hReach hCont.ge
    change 2764 ≤ v.pc at hFloor
    omega
  · have hFloor := resourceSuffixFloor .release hReach hCont.ge
    change 2767 ≤ v.pc at hFloor
    omega

private theorem laneZeroOfRecord {cta : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta) :
    (r.own.event l 0).1 = cta * l.block + 384 := by
  have hOwner := (hX.tmemPair.1 cta).2.1 r hr
  simp [WarpRequest.event, hOwner, allocatorWarp hp hX hr]

omit hp hX in
private theorem sitesOfRecord {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta) :
    (r.own.pc = 1909 ∧ ∃ base, r.action = .alloc 512 base) ∨
      (r.own.pc = 2763 ∧ r.action = .relinquish) ∨
      (r.own.pc = 2766 ∧ ∃ base, r.action = .dealloc base 512) := by
  have hValid := (hX.tmemPair.1 cta).1 r hr
  have he := hValid.2.2.2.2.1 0
  rcases (actualResourceRequest hX he).2 with ⟨hSite, hReq⟩ | ⟨hSite, hReq⟩ |
      ⟨hSite, base, hReq⟩
  · exact .inl ⟨hSite, Tmem.Action.request_eq_alloc (hValid.2.1.trans hReq)⟩
  · exact .inr (.inl ⟨hSite, Tmem.Action.request_eq_relinquish (hValid.2.1.trans hReq)⟩)
  · exact .inr (.inr ⟨hSite, base, Tmem.Action.request_eq_dealloc (hValid.2.1.trans hReq)⟩)

private theorem rankOfHistory (cta : Nat) :
    (X.tmemHistory cta).Pairwise (fun a b => resourceRank a.action < resourceRank b.action) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hOrder
  let a := (X.tmemHistory cta)[i]
  let b := (X.tmemHistory cta)[j]
  have ha : a ∈ X.tmemHistory cta := List.getElem_mem hi
  have hb : b ∈ X.tmemHistory cta := List.getElem_mem hj
  have va := (hX.tmemPair.1 cta).1 a ha
  have vb := (hX.tmemPair.1 cta).1 b hb
  have sameWarp := (allocatorWarp hp hX ha).trans (allocatorWarp hp hX hb).symm
  have sameCta := ((hX.tmemPair.1 cta).2.1 a ha).trans ((hX.tmemPair.1 cta).2.1 b hb).symm
  have hTrace := (hX.object.warp_ordered (List.getElem?_eq_getElem hi)
    (List.getElem?_eq_getElem hj) hOrder va.2.2 sameCta sameWarp).2.2 0
  change a.own.indices 0 < b.own.indices 0 at hTrace
  let g := cta * l.block + 384
  have hG0 : laneOf l g = 0 := by
    change (cta * l.block + 384) % l.block % 32 = 0
    rw [hp.block]
    omega
  have hea := va.2.2.2.2.1 0
  have heb := vb.2.2.2.2.1 0
  change X.get ((a.own.event l 0).1, a.own.indices 0) = _ at hea
  change X.get ((b.own.event l 0).1, b.own.indices 0) = _ at heb
  rw [laneZeroOfRecord hp hX ha] at hea
  rw [laneZeroOfRecord hp hX hb] at heb
  change resourceRank a.action < resourceRank b.action
  rcases sitesOfRecord hX ha with ⟨hPc, base, hA⟩ | ⟨hPc, hA⟩ | ⟨hPc, base, hA⟩
  · rw [hA]
    rcases sitesOfRecord hX hb with ⟨hPc', base', hB⟩ | ⟨_, hB⟩ | ⟨_, base', hB⟩
    · rw [hPc] at hea
      rw [hPc'] at heb
      have hI := allocatorIssueAtEntry hp hX hea hG0
      have hJ := allocatorIssueAtEntry hp hX heb hG0
      omega
    · simp [hB, resourceRank]
    · simp [hB, resourceRank]
  · have hLater := tailPrecedesHigherSite hp hX hea heb hTrace (.inl hPc)
    change a.own.pc < b.own.pc at hLater
    rcases sitesOfRecord hX hb with ⟨hPc', _, _⟩ | ⟨hPc', _⟩ | ⟨_, _, hB⟩
    · omega
    · omega
    · simp [hA, hB, resourceRank]
  · have hLater := tailPrecedesHigherSite hp hX hea heb hTrace (.inr hPc)
    change a.own.pc < b.own.pc at hLater
    rcases sitesOfRecord hX hb with ⟨hPc', _, _⟩ | ⟨hPc', _⟩ | ⟨hPc', _, _⟩ <;> omega

private theorem allocationRecordedBeforeTail {cta : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta)
    (hLate : 1911 < r.own.pc) :
    ∃ alloc ∈ X.tmemHistory cta, ∃ base, alloc.action = .alloc 512 base := by
  let g := cta * l.block + 384
  have hWarp : warpIndex l g = 12 := by
    unfold warpIndex g
    rw [hp.block]
    omega
  have hZero : laneOf l g = 0 := by
    change (cta * l.block + 384) % l.block % 32 = 0
    rw [hp.block]
    omega
  have hValid := (hX.tmemPair.1 cta).1 r hr
  have hGet := hValid.2.2.2.2.1 0
  change X.get ((r.own.event l 0).1, r.own.indices 0) = _ at hGet
  rw [laneZeroOfRecord hp hX hr] at hGet
  obtain ⟨_, _, _, _, _, hRead, _, _, _⟩ :=
    allocationReadBeforeEvent hp hX hGet hWarp hLate
  have hg := event_thread_lt hX hRead
  obtain ⟨n, _, _, _, hAlloc, hResult⟩ :=
    allocationPrefixAtBarrierReadOrExit hp hX hg hWarp hRead (.inr (.inr rfl))
  obtain ⟨_, _, _, hStore⟩ := hResult hZero
  have hContinued : n + 1 < (X.tr g).length := PTX.len_of_get hStore
  obtain ⟨owner, a, ha, lane, hLane⟩ := hX.tmemPairBlocking.performed hAlloc hContinued
  have hSame := congrArg Prod.fst hLane
  have hOwner := (hX.tmemPair.1 owner).2.1 a ha
  have hWarpA := allocatorWarp hp hX ha
  change a.own.cta * l.block + a.own.warp * 32 + lane.val = cta * l.block + 384 at hSame
  rw [hOwner, hWarpA, hp.block] at hSame
  have hLaneBound := lane.isLt
  have hCta : owner = cta := by omega
  rw [hCta] at ha
  have va := (hX.tmemPair.1 cta).1 a ha
  have hRecord := va.2.2.2.2.1 lane
  rw [hLane, hAlloc] at hRecord
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hRecord
  exact ⟨a, ha, Tmem.Action.request_eq_alloc (va.2.1.trans hRecord.2.2.2.symm)⟩

private theorem actualActions {cta : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta) :
    (∃ base, r.action = .alloc 512 base) ∨
      r.action = .relinquish ∨ r.action = .dealloc 0 512 := by
  have hValid := (hX.tmemPair.1 cta).1 r hr
  have he := hValid.2.2.2.2.1 0
  rcases (actualResourceRequest hX he).2 with ⟨_, hReq⟩ | ⟨_, hReq⟩ | ⟨hPc, base, hReq⟩
  · exact .inl (Tmem.Action.request_eq_alloc (hValid.2.1.trans hReq))
  · exact .inr (.inl (Tmem.Action.request_eq_relinquish (hValid.2.1.trans hReq)))
  · rw [hPc, hReq] at he
    rcases hEvent : r.own.event l 0 with ⟨g, j⟩
    rw [hEvent] at he
    have hZero := mmaDeallocReturnsZero hp hX he
    exact .inr (.inr (Tmem.Action.request_eq_dealloc (hValid.2.1.trans (hZero ▸ hReq))))

private theorem allocatorStartsAtHead {cta : Nat} {first : Requests} {rest : List Requests}
    (hHist : X.tmemHistory cta = first :: rest) : ∃ base, first.action = .alloc 512 base := by
  have hRank := rankOfHistory hp hX cta
  rw [hHist] at hRank
  have hMember : first ∈ X.tmemHistory cta := by rw [hHist]; simp
  rcases sitesOfRecord hX hMember with ⟨_, hAlloc⟩ | hTail
  · exact hAlloc
  · have hLater : 1911 < first.own.pc := by
      rcases hTail with ⟨hPc, _⟩ | ⟨hPc, _⟩ <;> omega
    obtain ⟨a, ha, base, hBase⟩ := allocationRecordedBeforeTail hp hX hMember hLater
    rw [hHist] at ha
    rcases List.mem_cons.mp ha with rfl | hMem
    · exact ⟨base, hBase⟩
    · have hPrior := (List.pairwise_cons.mp hRank).1 a hMem
      rw [hBase] at hPrior
      exact (Nat.not_lt_zero _ hPrior).elim

/-- Any nonempty CTA allocator history starts with the opening allocation at column zero. -/
theorem allocatorHistoryHasOpening {cta : Nat} (hNonempty : X.tmemHistory cta ≠ []) :
    ∃ r ∈ X.tmemHistory cta, r.own.pc = 1909 ∧ r.action = .alloc 512 0 := by
  cases hHist : X.tmemHistory cta with
  | nil => exact (hNonempty hHist).elim
  | cons first rest =>
    have hMember : first ∈ X.tmemHistory cta := by rw [hHist]; simp
    obtain ⟨base, hAction⟩ := allocatorStartsAtHead hp hX hHist
    have hFirst : (X.tmemHistory cta)[0]? = some first := by rw [hHist]; rfl
    have hZero := allocatorInitialBase hX hFirst hAction
    subst base
    refine ⟨first, List.mem_cons_self, ?_, hAction⟩
    rcases sitesOfRecord hX hMember with h | ⟨_, h⟩ | ⟨_, base, h⟩
    · exact h.1
    · rw [hAction] at h
      cases h
    · rw [hAction] at h
      cases h

/-- Any recorded allocation performs the opening full-width allocation at column zero. -/
theorem allocatorRecordedBase {cta base : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta)
    (hAction : r.action = .alloc 512 base) : base = 0 := by
  have hRank := rankOfHistory hp hX cta
  cases hHist : X.tmemHistory cta with
  | nil => rw [hHist] at hr; cases hr
  | cons first rest =>
    rw [hHist] at hr hRank
    rcases List.mem_cons.mp hr with rfl | hMem
    · exact allocatorInitialBase hX (by rw [hHist]; rfl) hAction
    · obtain ⟨_, hFirst⟩ := allocatorStartsAtHead hp hX hHist
      have hLater := (List.pairwise_cons.mp hRank).1 r hMem
      simp only [hFirst, hAction, resourceRank, Nat.lt_irrefl] at hLater

omit hp hX in
private theorem noRecordAfterDealloc {r : Requests} {rest : List Requests}
    (hAction : r.action = .dealloc 0 512)
    (hRank : (r :: rest).Pairwise (fun a b => resourceRank a.action < resourceRank b.action)) :
    rest = [] := by
  cases rest with
  | nil => rfl
  | cons later tail =>
    have hLater := (List.pairwise_cons.mp hRank).1 later (by simp)
    rw [hAction] at hLater
    cases hAct : later.action <;> simp [resourceRank, hAct] at hLater

private theorem actualAllocatorReplay (cta : Nat) :
    ∃ state, runRequests {} (X.tmemHistory cta) = .done state ∧
      (∀ r ∈ X.tmemHistory cta, r.action = .dealloc 0 512 → state.live = []) := by
  have hRank := rankOfHistory hp hX cta
  cases hHist : X.tmemHistory cta with
  | nil => exact ⟨{}, rfl, fun _ _ _ => rfl⟩
  | cons first rest =>
    obtain ⟨base, hAlloc⟩ := allocatorStartsAtHead hp hX hHist
    have hZero := allocatorInitialBase hX (cta := cta)
      (show (X.tmemHistory cta)[0]? = some first by simp [hHist]) hAlloc
    subst base
    rw [hHist] at hRank
    obtain ⟨hAfterFirst, hRest⟩ := List.pairwise_cons.mp hRank
    cases rest with
    | nil =>
      refine ⟨_, by rw [runRequests, hAlloc, tmem_full_allocation]; rfl, ?_⟩
      intro r hr hAction
      obtain rfl := List.mem_singleton.mp hr
      rw [hAlloc] at hAction
      cases hAction
    | cons second tail =>
      have hMember : second ∈ X.tmemHistory cta := by rw [hHist]; simp
      have hAfter := hAfterFirst second (by simp)
      rcases actualActions hp hX hMember with ⟨base, hSecond⟩ | hSecond | hSecond
      · simp [hAlloc, hSecond, resourceRank] at hAfter
      · cases tail with
        | nil =>
          refine ⟨_, by simp only [runRequests, hAlloc, hSecond]; rfl, ?_⟩
          intro r hr hAction
          rcases List.mem_cons.mp hr with rfl | hr
          · rw [hAlloc] at hAction
            cases hAction
          · obtain rfl := List.mem_singleton.mp hr
            rw [hSecond] at hAction
            cases hAction
        | cons third rest =>
          have hMember' : third ∈ X.tmemHistory cta := by rw [hHist]; simp
          obtain ⟨hAfterSecond, hTail⟩ := List.pairwise_cons.mp hRest
          have hNext := hAfterSecond third (by simp)
          rcases actualActions hp hX hMember' with ⟨base, hThird⟩ | hThird | hThird
          · simp [hSecond, hThird, resourceRank] at hNext
          · simp [hSecond, hThird, resourceRank] at hNext
          · obtain rfl := noRecordAfterDealloc hThird hTail
            refine ⟨{permit := false, previousColumns := some 512, nextLifetime := 1},
              ?_, fun _ _ _ => rfl⟩
            simp only [runRequests, hAlloc, hSecond, hThird]
            rfl
      · obtain rfl := noRecordAfterDealloc hSecond hRest
        refine ⟨{previousColumns := some 512, nextLifetime := 1}, ?_, fun _ _ _ => rfl⟩
        simp only [runRequests, hAlloc, hSecond]
        rfl

/-- The kernel's single-CTA allocator histories replay without faults. -/
theorem noAllocatorFault :
    ¬ ResourceUnsafe l X := by
  rintro ⟨cta, ⟨reason, hFault⟩ | ⟨_, _, d, _, hd, _, _, hPaired, _, _, _, _⟩⟩
  · obtain ⟨state, hReplay, _⟩ := actualAllocatorReplay hp hX cta
    rw [hReplay] at hFault
    cases hFault
  · have hMember := List.mem_of_getElem? hd
    have hValid := (hX.tmemPair.1 cta).1 d hMember
    exact CtaGroup.noConfusion
      ((actualResourceRequest hX (hValid.2.2.2.2.1 0)).1.symm.trans hPaired)

private theorem deallocationRecordedAtExit (hExited : Tmem.Pair.Exited l X) {cta : Nat}
    (hCta : cta < l.grid) :
    ∃ r ∈ X.tmemHistory cta, r.action = .dealloc 0 512 := by
  let g := cta * l.block + 384
  have hg : g < l.threads := by
    change cta * l.block + 384 < l.grid * l.block
    rw [hp.block]
    omega
  have hWarp : warpIndex l g = 12 := by
    unfold warpIndex g
    rw [hp.block]
    omega
  obtain ⟨site, hLast⟩ := (hExited g hg).resolve_left (noCanceled hX)
  let index := (X.tr g).length - 1
  have he : X.get (g, index) = some ⟨site, .exit⟩ := by
    change (X.tr g)[index]? = some ⟨site, .exit⟩
    simpa only [List.getLast?_eq_getElem?, index] using hLast
  obtain ⟨j, hj, hf⟩ := mmaDeallocBeforeExit hp hX hWarp he
  have hLength : index < (X.tr g).length := PTX.len_of_get he
  have hContinued : j + 1 < (X.tr g).length := by omega
  obtain ⟨owner, r, hr, lane, hLane⟩ := hX.tmemPairBlocking.performed hf hContinued
  have hG := congrArg Prod.fst hLane
  have hOwner := (hX.tmemPair.1 owner).2.1 r hr
  change r.own.cta * l.block + r.own.warp * 32 + lane.val = cta * l.block + 384 at hG
  rw [hOwner, allocatorWarp hp hX hr, hp.block] at hG
  have hLaneBound := lane.isLt
  have hSame : owner = cta := by omega
  rw [hSame] at hr
  have hValid := (hX.tmemPair.1 cta).1 r hr
  have hRequest := hValid.2.2.2.2.1 lane
  rw [hLane, hf] at hRequest
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hRequest
  exact ⟨r, hr, Tmem.Action.request_eq_dealloc (hValid.2.1.trans hRequest.2.2.2.symm)⟩

/-- Every allocator has released its allocation when the role threads have all exited. -/
theorem allocatorReleasedAtExit (hExit : Tmem.Pair.Exited l X) : Released X := by
  intro cta state hReplay
  by_cases hCta : cta < l.grid
  · obtain ⟨r, hr, hAction⟩ := deallocationRecordedAtExit hp hX hExit hCta
    obtain ⟨s, hState, hReleased⟩ := actualAllocatorReplay hp hX cta
    rw [hReplay] at hState
    obtain rfl := Tmem.Outcome.done.inj hState
    exact hReleased r hr hAction
  · have hEmpty : X.tmemHistory cta = [] := by
      cases hHistory : X.tmemHistory cta with
      | nil => rfl
      | cons first rest =>
        have hMember : first ∈ X.tmemHistory cta := by rw [hHistory]; simp
        have hValid := (hX.tmemPair.1 cta).1 first hMember
        have hc := (hX.tmemPair.1 cta).2.1 first hMember
        exact (hCta (hc ▸ hValid.2.2.1)).elim
    rw [hEmpty, runRequests] at hReplay
    obtain rfl := Tmem.Outcome.done.inj hReplay
    rfl

/-- A finished execution holds no Tensor Memory allocation. -/
theorem noAllocatorReleaseUnsafe :
    ¬ ReleaseUnsafe l X :=
  fun h => h.2.2 (allocatorReleasedAtExit hp hX h.1)

end PTX.Kernels.TmlFa4Fwd.Thread
