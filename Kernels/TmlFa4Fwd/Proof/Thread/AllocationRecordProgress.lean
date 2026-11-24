-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaResourceOrder
import Kernels.TmlFa4Fwd.Proof.MmaResources
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
public import Lemmas.Step.TmemPair
public import Lemmas.Tmem.TmemResourceReady

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue Mma Tmem.Pair

noncomputable section

private theorem earlierAllocatorKinds {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {i : Nat} (hi : i < 6) {e : Event} (he : X.get (g, i) = some e) :
    isTcColl e = false ∧ Execution.isBarId 2 e = false := by
  obtain ⟨hFence, hBar⟩ := nonzeroBarrierArrives hp hMax hg (by omega)
  interval_cases i
  · rw [firstSharedValue hp hMax.1 g hg he]
    exact ⟨rfl, rfl⟩
  · rw [secondWarpValue hp hMax.1 g hg he]
    exact ⟨rfl, rfl⟩
  · rw [thirdWarpValue hp hMax.1 g hg he]
    exact ⟨rfl, rfl⟩
  · rw [Option.some.inj (he.symm.trans hFence)]
    exact ⟨rfl, rfl⟩
  · rw [Option.some.inj (he.symm.trans hBar)]
    exact ⟨rfl, rfl⟩
  · obtain ⟨pos, _, _, q, _, _, _, hGet, hKind, hPos, _, _, _⟩ :=
      Register.requestReturn hp hMax hg
    obtain rfl := hPos (by omega)
    obtain rfl := Option.some.inj (hGet.symm.trans he)
    cases q with
    | mk site k => cases hKind; exact ⟨rfl, rfl⟩

private def openingRequest (l : Launch) (c : Nat) : WarpRequest :=
  ⟨c, 12, fun _ => 6, 1909, some ⟨.shared, c, l.sharedBase + 312⟩, .alloc 512⟩

private theorem openingRequestLane {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {c : Nat} (hc : c < l.grid) (lane : Fin 32) :
    ((openingRequest l c).event l lane).1 < l.threads ∧
      ((openingRequest l c).event l lane).1 / l.block = c ∧
      warpIndex l ((openingRequest l c).event l lane).1 = 12 := by
  have hLane := lane.isLt
  have hBlock : 384 + lane.val < l.block := by rw [hp.block]; omega
  have hMul := NamedBar.cta_thread_lt hc hBlock
  obtain ⟨hCta, hMod⟩ := NamedBar.lane_cta (c := c) (by rw [hp.block]; decide) hBlock
  have hG : ((openingRequest l c).event l lane).1 = c * l.block + (384 + lane.val) := by
    simp [WarpRequest.event, openingRequest, Nat.add_assoc]
  rw [hG]
  exact ⟨hMul, hCta, by unfold warpIndex; rw [hMod]; omega⟩

private theorem openingValid {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {c : Nat} (hc : c < l.grid) :
    (openingRequest l c).Valid l X .one := by
  have hGet (lane : Fin 32) : X.get ((openingRequest l c).event l lane) =
      some ⟨1909, .tc (.resource .one (openingRequest l c).dst (.alloc 512))⟩ := by
    let g := ((openingRequest l c).event l lane).1
    obtain ⟨hg, hCta, hw⟩ := openingRequestLane hp hc lane
    obtain ⟨_, _, _, he, _, _⟩ := allocatorIssues hp hMax hg hw
    have hSlot : allocationSlot l g = ⟨.shared, c, l.sharedBase + 312⟩ := by
      unfold allocationSlot
      rw [hCta]
    change X.get (g, 6) = some ⟨1909, .tc (.resource .one (some _) (.alloc 512))⟩
    rwa [hSlot] at he
  refine ⟨hc, (by change 416 ≤ l.block; rw [hp.block]; decide), hGet, 0, ?_⟩
  intro lane
  refine ⟨⟨_, hGet lane, rfl⟩, List.countP_eq_zero.mpr ?_⟩
  intro e hm hTc
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp hm
  have hi := (List.getElem?_eq_some_iff.mp he).1
  have hBound : i < 6 := by
    change i < (List.take 6 _).length at hi
    simp only [List.length_take] at hi
    omega
  change (List.take 6 _)[i]? = some e at he
  rw [List.getElem?_take_of_lt hBound] at he
  obtain ⟨hg, _, hw⟩ := openingRequestLane hp hc lane
  rw [(earlierAllocatorKinds hp hMax hg hw hBound he).1] at hTc
  cases hTc

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

/-- Maximal prefixes have actually completed the warp's opening allocation. -/
theorem openingCovered (hw : warpIndex l g = 12) :
    Covered l X (g, 6) := by
  let c := g / l.block
  let w := openingRequest l c
  have hc : c < l.grid := NamedBar.cta_lt hg
  have hValid := openingValid hp hMax hc
  have hParticipates : Participates l w (g, 6) := by
    let lane : Fin 32 := ⟨laneOf l g, Nat.mod_lt _ (by decide)⟩
    refine ⟨lane, Prod.ext ?_ rfl⟩
    change g / l.block * l.block + 384 + g % l.block % 32 = g
    have h := Nat.div_add_mod g l.block
    have hw' : g % l.block / 32 = 12 := hw
    rw [Nat.mul_comm] at h
    omega
  by_cases hHist : X.tmemHistory c = []
  · exfalso
    let r : Requests := ⟨w, .one, .alloc 512 0⟩
    have hReady : Step.EntryReady l X c r := by
      refine ⟨⟨hMax.1.cluster.1, rfl, hValid⟩, ?_, ?_, rfl, ?_⟩
      · intro _ wr hm earlier group hEarlier hBefore i hi
        obtain rfl := List.mem_singleton.mp hm
        obtain ⟨hCta, hWarp, hIndex⟩ := hBefore
        have hEv := hEarlier.2.2.1 0
        obtain ⟨hg', _, hw'⟩ := openingRequestLane hp hc 0
        have hThread : (earlier.event l 0).1 = (w.event l 0).1 := by
          simp only [WarpRequest.event, hCta, hWarp]
          rfl
        change X.get ((earlier.event l 0).1, earlier.indices 0) = _ at hEv
        rw [hThread] at hEv
        have hBad := (earlierAllocatorKinds hp hMax hg' hw' (hIndex 0) hEv).1
        cases hBad
      · intro q hMem
        rw [hHist] at hMem
        simp at hMem
      · rw [hHist]
        change runRequests {} [r] ≠ .blocked
        rw [runRequests, show r.action = .alloc 512 0 by rfl, tmem_full_allocation]
        intro h
        cases h
    obtain ⟨Y, hY, hLe, hSize, _⟩ := Step.entry_counted hMax.1 hReady
      (Assumptions.wfStep.quiet hMax.1 le_recordEntry rfl (Execution.noNewRead_of_tr rfl))
    exact hMax.not_grows ⟨Y, hY, hLe, hSize⟩
  · obtain ⟨r, hR, hPc, hAction⟩ := allocatorHistoryHasOpening hp hMax.1 hHist
    have hRValid := (hMax.1.tmemPair.1 c).1 r hR
    have hSource := (hMax.1.tmemPair.1 c).2.1 r hR
    have hWarp := allocatorWarp hp hMax.1 hR
    have hRGet := hRValid.2.2.2.2.1 0
    have hGroup := (actualResourceRequest hMax.1 hRGet).1
    have hLane : (r.own.event l 0).1 = (w.event l 0).1 := by
      simp only [WarpRequest.event, hSource, hWarp, w, openingRequest]

    have hZero : laneOf l ((r.own.event l 0).1) = 0 := by
      rw [hLane]
      change (c * l.block + 384 + 0) % l.block % 32 = 0
      rw [hp.block]
      omega
    have hIdx := allocatorIssueAtEntry hp hMax.1 (hPc ▸ hRGet) hZero
    have hSame : r.own.event l 0 = w.event l 0 := Prod.ext hLane hIdx
    have hEq : r.own = w := hRValid.2.2.ext hValid hSame
    exact ⟨[r.own], .inl ⟨c, r, hR, hGroup, rfl⟩, r.own, List.mem_singleton_self _,
      hEq ▸ hParticipates⟩

private theorem openingReleased (hw : warpIndex l g = 12) (hLen : 7 = (X.tr g).length)
    (he : X.get (g, 6) = some ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩)
    (hResult : laneOf l g ≠ 0 → ∃ store dst, AllocResult l X store (g, 6) dst) :
    Step.Released l X g := by
  have hc := openingCovered hp hMax hg hw
  have hr := ReturnReady.ready hMax.1.tmemPair he ⟨hc.performed hMax.1.tmemPair, fun _ => hc⟩
    fun _ _ hLane => hResult hLane
  constructor
  intro site kind hGet _
  have hPos : (X.tr g).length - 1 = 6 := by omega
  rw [hPos] at hGet ⊢
  exact hr

omit hp hMax hg in
private theorem storeNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 1909 [(2451, b32 512), (1062, b32 12),
      (2535, b32 l.sharedBase)]) :
    Next kernel Assumptions.all l g {t with sub := 1} {t with sub := 1}
      (.tcAllocStore (allocationSlot l g) (next t)) := by
  refine ⟨.refl, ?_⟩
  have hBase : t.regs 2535 = some (b32 l.sharedBase) := ht.2.2.2.2.2.2.1
  have hColumns : t.regs 2451 = some (b32 512) := ht.2.2.2.2.1
  let s := {t with sub := 1}
  have hs : s.sub = 1 := rfl
  have hPc : s.pc = 1909 := ht.1
  change out kernel Assumptions.all l g s = _
  rw [allocationTemplate hp hPc ht.2.2.2.1 hBase hColumns, hs]
  have hEq : { s with pc := s.pc + 1, sub := 0 } = next t := by
    have hz := ht.2.1
    cases t
    simp_all [s, next]
  simp only [Nat.one_ne_zero, ↓reduceIte, hEq]

/-- The allocator leader writes column zero to its CTA result word. -/
theorem allocatorStores (hw : warpIndex l g = 12) (hz : laneOf l g = 0) {t : TState}
    {o : Option TState} (ht : At t 1909 [(2451, b32 512), (1062, b32 12), (2535, b32 l.sharedBase)])
    (he : X.get (g, 6) = some ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take 7) (some {t with sub := 1}))
    (hTail : Run kernel Assumptions.all l g {t with sub := 1} ((X.tr g).drop 7) o) :
    ∃ e, X.get (g, 7) = some e ∧ e.kind =
        .wr {loc := allocationSlot l g, size := 4} (b32 0).toBytes ∧ e.pc = 1909 ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 8) (some (next t)) ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop 8) o := by
  let s := {t with sub := 1}
  let dst : Acc := {loc := allocationSlot l g, size := 4}
  let e0 : Event := ⟨s.pc, .wr dst (b32 0).toBytes⟩
  have hn := storeNext (g := g) hp ht
  have hSize : 7 < (X.tr g).length := by
    by_contra! hLe
    have hLen : 7 = (X.tr g).length := Nat.le_antisymm (len_of_get he) hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h, List.length_nil] at hLen; omega
    have hRel := openingReleased hp hMax hg hw hLen he fun h => (h hz).elim
    rw [List.take_of_length_le hLe] at hPrefix
    have hStep : EStep kernel Assumptions.all l g s e0 (some (next t)) :=
      ⟨_, hn.stop, 0, by decide, rfl, rfl⟩
    have hResults : Tmem.Pair.ResultOk l (X.snoc g e0 (fun _ => none)) := by
      apply hMax.1.tmemPairResult.snoc
      intro site a bs hEq _ site' group address n hGet c r base hr _ hAction
      have hPos : (X.tr g).length - 1 = 6 := by omega
      rw [hPos] at hGet
      have hEvent := congrArg Event.kind (Option.some.inj (he.symm.trans hGet))
      have hColumns := Tmem.Request.alloc.inj (TcKind.resource.inj (Kind.tc.inj hEvent)).2.2
      subst n
      have hBase := allocatorRecordedBase hp hMax.1 hr hAction
      have hBytes := (Kind.wr.inj (congrArg Event.kind hEq)).2
      simpa only [hBase, b32] using hBytes.symm
    exact hMax.not_grows (Step.plain_counted_extension hMax.1 hg (.inl hStarted) hRel
      hPrefix .refl hStep rfl rfl nofun nofun nofun rfl hResults
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl)))
  obtain ⟨e, v, hGet, ⟨col, hCol, hEq, hv⟩, hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hSize) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hv
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take 8) (some (next t)) := by
    rw [List.take_succ_eq_append_getElem hSize]
    have hAt : (X.tr g)[7] = e := by
      change (X.tr g)[7]? = some e at hGet
      rwa [List.getElem?_eq_getElem hSize, Option.some.injEq] at hGet
    rw [hAt]
    exact hPrefix.snoc .refl ⟨_, hn.stop, col, hCol, hEq, rfl⟩
  have hSite : e = ⟨1909, .wr dst (b32 col).toBytes⟩ := ht.1 ▸ hEq
  have hRecord := allocationStoreRecord hp hMax.1 (hSite ▸ hGet)
  obtain ⟨_, _, _, _, _, hBytes⟩ := hRecord
  exact ⟨e, hGet, by rw [hSite]; exact congrArg (Kind.wr dst) hBytes, by rw [hSite], hPast,
    hRest⟩

/-- Every lane of the allocator warp has the result handoff of its leader's address store. -/
theorem allocatorResult (hw : warpIndex l g = 12) :
    ∃ store dst, AllocResult l X store (g, 6) dst := by
  let c := g / l.block
  let w := openingRequest l c
  have hc : c < l.grid := NamedBar.cta_lt hg
  have hValid := openingValid hp hMax hc
  obtain ⟨hg0, hCta0, hw0⟩ := openingRequestLane hp hc 0
  have hz0 : laneOf l ((openingRequest l c).event l 0).1 = 0 := by
    change (c * l.block + 12 * 32 + 0) % l.block % 32 = 0
    rw [hp.block]
    omega
  obtain ⟨t, _, ht, he, hPrefix, hTail⟩ := allocatorIssues hp hMax hg0 hw0
  simp only [hz0, ↓reduceIte] at hPrefix hTail
  obtain ⟨⟨site, kind⟩, hGet, hKind, hPc, _, _⟩ :=
    allocatorStores hp hMax hg0 hw0 hz0 ht he hPrefix hTail
  change kind = _ at hKind
  change site = 1909 at hPc
  subst hKind hPc
  have hSlot : allocationSlot l ((openingRequest l c).event l 0).1 =
      ⟨.shared, c, l.sharedBase + 312⟩ := by
    unfold allocationSlot
    rw [hCta0]
  rw [hSlot] at hGet
  let lane : Fin 32 := ⟨laneOf l g, Nat.mod_lt _ (by decide)⟩
  have hLane : w.event l lane = (g, 6) := by
    refine Prod.ext ?_ rfl
    change g / l.block * l.block + 12 * 32 + g % l.block % 32 = g
    have h := Nat.div_add_mod g l.block
    have hw' : g % l.block / 32 = 12 := hw
    rw [Nat.mul_comm] at h
    omega
  exact ⟨_, _, hLane ▸ AllocResult.of_warpRequest hValid rfl rfl rfl rfl hGet lane⟩

/-- The allocator participant reaches the barrier after publishing the allocated column. -/
theorem allocatorRendezvousPrefix (hw : warpIndex l g = 12) :
    ∃ pos t o, pos = allocationBarrierPos l g ∧ X.IsBarrier (g, pos) 2 (some 416) 1910 ∧
      ((X.tr g).take pos).countP (Execution.isBarId 2) = 0 ∧
      At t 1911 [(2451, b32 512), (1062, b32 12), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (pos + 1)) o := by
  obtain ⟨t, o, ht, he, hPrefix, hTail⟩ := allocatorIssues hp hMax hg hw
  let u := next t
  have hSite : u.pc ∈ allocationEntrySites := by rw [ht.next.1]; decide
  have hAt : At u 1910 [(2451, b32 512), (1062, b32 12), (2535, b32 l.sharedBase)] := ht.next
  have hCursor : ∃ pos, pos = allocationBarrierPos l g ∧ (pos = 7 ∨ pos = 8) ∧
      (pos = 8 → ∃ e, X.get (g, 7) = some e ∧ e.kind =
        .wr {loc := allocationSlot l g, size := 4} (b32 0).toBytes) ∧
      pos ≤ (X.tr g).length ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) o ∧
      (pos = (X.tr g).length → Step.Released l X g) := by
    by_cases hz : laneOf l g = 0
    · simp only [hz, ↓reduceIte] at hPrefix hTail
      obtain ⟨e, hGet, hKind, _, hPast, hRest⟩ :=
        allocatorStores hp hMax hg hw hz ht he hPrefix hTail
      have hReleased (hLen : 8 = (X.tr g).length) : Step.Released l X g :=
        releasedIfLast hGet (by rw [hKind]; intro h; cases h) hLen
      exact ⟨8, (by simp [allocationBarrierPos, hz]), .inr rfl, fun _ => ⟨e, hGet, hKind⟩,
        len_of_get hGet, hPast, hRest, hReleased⟩
    · simp only [hz, ↓reduceIte] at hPrefix hTail
      have hNotEight : (7 : Nat) ≠ 8 := by decide
      exact ⟨7, (by simp [allocationBarrierPos, hz]), .inl rfl, fun h => (hNotEight h).elim,
        len_of_get he,
        hPrefix, hTail, fun hLen => openingReleased hp hMax hg hw hLen he
          fun _ => allocatorResult hp hMax hg hw⟩
  obtain ⟨pos, hCursorPos, hPos, hStore, hLe, hPast, hRest, hRel⟩ := hCursor
  have hBar : X.IsBarrier (g, pos) 2 (some 416) u.pc :=
    requireArrival hp hMax hg (by omega) hLe hSite ht.2.2.2.1 hPast hRest hRel
  have hLt : pos < (X.tr g).length := len_of_get hBar
  have hOut := allocationEntryTemplate (g := g) hp.block hSite ht.2.2.2.1
  have hn : Next kernel Assumptions.all l g u u (.bar 2 (next u) (some 416) .sync) :=
    ⟨.refl, hOut⟩
  obtain ⟨_, _, hGet, ⟨rfl, hv⟩, hAfter⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, h⟩; cases h) hRest
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hv
  have hPrefix' : Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1))
      (some (next u)) := by
    rw [List.take_succ_eq_append_getElem hLt]
    have hEq : (X.tr g)[pos] = ⟨u.pc, .bar 2 (some 416) .sync⟩ := by
      change (X.tr g)[pos]? = some _ at hGet
      rwa [List.getElem?_eq_getElem hLt, Option.some.injEq] at hGet
    rw [hEq]
    exact hPast.snoc .refl ⟨_, hOut, rfl, rfl⟩
  refine ⟨pos, next u, o, hCursorPos, hAt.1 ▸ hBar, List.countP_eq_zero.mpr ?_,
    hAt.next, hPrefix', hAfter⟩
  intro e hm hKind
  obtain ⟨idx, hE⟩ := List.mem_iff_getElem?.mp hm
  have hIx := (List.getElem?_eq_some_iff.mp hE).1
  have hIndex : idx < pos := by simp only [List.length_take] at hIx; omega
  rw [List.getElem?_take_of_lt hIndex] at hE
  by_cases hSix : idx < 6
  · rw [(earlierAllocatorKinds hp hMax hg hw hSix hE).2] at hKind
    cases hKind
  rcases (show idx = 6 ∨ idx = 7 by omega) with rfl | rfl
  · obtain rfl := Option.some.inj (hE.symm.trans he)
    cases hKind
  · obtain ⟨q, hQ, hK⟩ := hStore (by omega)
    obtain rfl := Option.some.inj (hE.symm.trans hQ)
    cases e with
    | mk site k => cases hK; cases hKind

/-- Every participating lane of a maximal prefix reaches the allocation rendezvous. -/
theorem participantsArrive (hw : warpIndex l g < 13) :
    ∃ pos site, site ∈ allocationEntrySites ∧ X.IsBarrier (g, pos) 2 (some 416) site := by
  by_cases hM : warpIndex l g = 12
  · obtain ⟨pos, _, _, _, he, _, _, _, _⟩ := allocatorRendezvousPrefix hp hMax hg hM
    exact ⟨pos, 1910, by decide, he⟩
  · exact directParticipantsArrive hp hMax hg (by omega)

/-- The initial allocation is the first Tensor Memory collective of its lane. -/
theorem openingCollectiveOrdinal (hw : warpIndex l g = 12) :
    X.TcK (g,6) 0 := by
  have hEarly : ((X.tr g).take 6).countP isTcColl = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hm hRed
    obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp hm
    have hi := (List.getElem?_eq_some_iff.mp he).1
    have hBound : i < 6 := hi.trans_le (List.length_take_le ..)
    rw [List.getElem?_take_of_lt hBound] at he
    rw [(earlierAllocatorKinds hp hMax hg hw hBound he).1] at hRed
    cases hRed
  obtain ⟨_, _, _, he, _, _⟩ := allocatorIssues hp hMax hg hw
  exact ⟨⟨_, he, rfl⟩, hEarly⟩

/-- The first allocator rendezvous prefix contains just the opening allocation collective. -/
theorem allocatorRendezvousCollectiveCount (hw : warpIndex l g = 12) :
    ((X.tr g).take (allocationBarrierPos l g + 1)).countP isTcColl = 1 := by
  have hEarly := (openingCollectiveOrdinal hp hMax hg hw).2
  obtain ⟨t, o, ht, he, hPrefix, hTail⟩ := allocatorIssues hp hMax hg hw
  obtain ⟨pos, _, _, hPos, hBar, _, _, _, _⟩ := allocatorRendezvousPrefix hp hMax hg hw
  have hCount : ((X.tr g).take 7).countP isTcColl = 1 := by
    rw [show (7 : Nat) = 6 + 1 by decide, List.take_add_one, show (X.tr g)[6]? = _ from he]
    simp [hEarly, isTcColl]
  subst pos
  by_cases hz : laneOf l g = 0
  · simp only [hz, ↓reduceIte] at hPrefix hTail
    obtain ⟨e, hGet, hK, _, _⟩ := allocatorStores hp hMax hg hw hz ht he hPrefix hTail
    obtain ⟨site, kind⟩ := e
    cases hK
    rw [allocationBarrierPos, ite_eq_left hz] at hBar ⊢
    rw [List.take_add_one, show (X.tr g)[8]? = _ from hBar]
    simp only [Option.toList_some, List.countP_append, List.countP_singleton, isTcColl,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [show (8 : Nat) = 7 + 1 by decide, List.take_add_one, show (X.tr g)[7]? = _ from hGet]
    simpa [isTcColl] using hCount
  · rw [allocationBarrierPos, ite_eq_right hz] at hBar ⊢
    rw [List.take_add_one, show (X.tr g)[7]? = _ from hBar]
    simp [hCount, isTcColl]

end
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
