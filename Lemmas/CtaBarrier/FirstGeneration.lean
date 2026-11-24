-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Order.DependencyWitness
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Step.CtaBarFinishExit
public import Lemmas.Protocol.NamedBarMember

@[expose] public section

namespace PTX.CtaBarrier
open PTX

/-- A lane cannot return from a named barrier and issue a second arrival of its first
generation. Moving the later record before the first would violate object causality. Moving
it after the first makes the later arrival a prerequisite of the already returned wait. -/
theorem not_generationZero_after_sync {l : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent l K A m X)
    {g j n id pc : Nat} {count : Option Nat} (hId : id < 16) (hLt : j < n)
    (hSync : X.IsBarrier (g, j) id count pc)
    (hGen : GenerationOf l.block (X.barriers (g/l.block)) (g, n) id 0) : False := by
  obtain ⟨otherCount, otherPc, mode, hn⟩ := hX.ctaBar.generation_barrier hGen
  have hLength : n < (X.tr g).length := (List.getElem?_eq_some_iff.mp hn).1
  have hPassed : j+1 < (X.tr g).length := by omega
  obtain ⟨key, hWaitKey, hDone⟩ := ctaBarDone_of_returned hX hSync hPassed
  have hg := hWaitKey.1
  have hArr : CtaBarArrivalK l X (g, n) id := by
    simpa only [Nat.mul_zero, Nat.add_zero] using
      CtaBarArrivalK.of_generation hX.ctaBar (e := (g, n)) hg hId hGen
  obtain ⟨waitCount, waitPc, hEvent⟩ := hWaitKey.2.1
  have hKeyId : key % 16 = id := by
    change X.get (g, j) = some ⟨waitPc, .bar (key % 16) waitCount .sync⟩ at hEvent
    rw [hSync] at hEvent
    exact (Kind.bar.inj (congrArg Event.kind (Option.some.inj hEvent))).1.symm
  have hWaitGen : GenerationOf l.block (X.barriers (g/l.block)) (g, j) id (key/16) := by
    simpa only [hKeyId] using hWaitKey.2.2
  obtain ⟨i, s, warp, cnt, lanes, lane, hi, hAt, hMem, hPhase, _⟩ := hGen
  obtain ⟨q, t, warp', cnt', lanes', lane', hq, hAt', hMem', hPhase', _⟩ := hWaitGen
  have hBefore : q ≤ i := by
    by_contra hNo
    have hHist : SyncObjectOrder l X (.ctaBar (g/l.block) ⟨id, hId⟩)
        (.thread (g, n), false) (.thread (g, j), false) := by
      change ObjectOrder l X (.ctaBar (g/l.block) ⟨id, hId⟩)
        (.thread (g, n), false) (.thread (g, j), false)
      exact ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, hn⟩, ⟨_, hSync⟩, i, q, _, _, hi, hq, by omega,
        rfl, rfl, List.mem_map.mpr ⟨(lane, (g, n)), hMem, rfl⟩,
        List.mem_map.mpr ⟨(lane', (g, j)), hMem', rfl⟩⟩
    have hStage : stageCausality l X (.thread (g, j), false) (.thread (g, j), true) :=
      .inl (.inl ⟨rfl, rfl, rfl, ⟨_, hSync⟩⟩)
    have hPo : po X (g, j) (g, n) :=
      po_of_not_access rfl hLt hLength (by rw [hn]; rfl)
    have hLater : stageCausality l X (.thread (g, j), true) (.thread (g, n), false) :=
      .inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, .single (.inl hPo)⟩)
    exact hX.object (.ctaBar (g/l.block) ⟨id, hId⟩) (.thread (g, n), false)
      (((Relation.TransGen.single (.inr hHist)).tail (.inl hStage)).tail (.inl hLater))
  have hAtPrefix : At l.block ((X.barriers (g/l.block)).take i) q t := by
    unfold At at hAt' ⊢
    rwa [List.take_take, Nat.min_eq_left hBefore]
  have hMono := at_generation_mono hAtPrefix hAt id
  rw [hPhase', hPhase] at hMono
  have hKey : key = id := by omega
  subst key
  obtain ⟨c, hComplete⟩ := hDone
  have hWitness : Witness l X (.thread (g, n)) (g, j) :=
    Witness.of_ctaBarCounted hWaitKey hComplete hArr rfl
  have hResume : Resumes K X (g, j) (g, n) :=
    Resumes.of_blocking hSync rfl ⟨rfl, hLt, hLength⟩
  exact hX.dependency.acyclic (.ctaBar (g/l.block) ⟨id % 16, Nat.mod_lt _ (by decide)⟩)
    trivial (.thread (g, n), false)
    ((Relation.TransGen.single (.inl (DepStep.of_witness (K := K) l hWitness))).tail
      (.inl (DepStep.of_resumes l hResume)))

/-- A returned wait establishes completion of generation zero of its named resource. -/
theorem first_generation_released_of_returned {l : Launch} {K : Kernel}
    {A : List Assumption} {m : Mem0} {X : Execution} (hX : Consistent l K A m X)
    {g j id pc : Nat} {count : Option Nat} (hId : id < 16)
    (hSync : X.IsBarrier (g, j) id count pc) (hPassed : j+1 < (X.tr g).length) :
    CtaBarDone l X (g/l.block) id := by
  obtain ⟨key, hKey, hDone⟩ := ctaBarDone_of_returned hX hSync hPassed
  obtain ⟨otherCount, otherPc, hGet⟩ := hKey.2.1
  change X.get (g, j) = some ⟨otherPc, .bar (key % 16) otherCount .sync⟩ at hGet
  rw [hSync] at hGet
  have hKeyId : key % 16 = id :=
    (Kind.bar.inj (congrArg Event.kind (Option.some.inj hGet))).1.symm
  have hRel : Released l.block (X.barriers (g/l.block)) id (key/16) := by
    simpa only [CtaBarDone, hKeyId] using hDone
  obtain ⟨s, hs⟩ := (hX.ctaBar.2 _ (NamedBar.cta_lt hKey.1)).2.2
  have hPos := released_generation_lt hs hRel
  unfold CtaBarDone
  rw [Nat.mod_eq_of_lt hId, Nat.div_eq_of_lt hId]
  exact Step.CtaBar.released_of_generation_lt hs (by omega)

/-- The resource generation is monotone between two positions of the same checked history. -/
theorem generation_mono_between {block i j id : Nat} {xs : List (Record EvId)}
    {s t : State} (hi : At block xs i s) (hj : At block xs j t) (hij : i ≤ j) :
    (s.slots id).generation ≤ (t.slots id).generation := by
  have h : At block (xs.take j) i s := by
    unfold At at hi ⊢
    rwa [List.take_take, Nat.min_eq_left hij]
  exact at_generation_mono h hj id

/-- Generation-zero source classification yields the named-resource protocol up to that
generation's last update. -/
theorem first_generation_protocol {l : Launch} {X : Execution} (hX : CtaBarHistoryOk l X)
    {c last id : Nat} {count : Option Nat} {part : Finset Nat} (hc : c < l.grid)
    {st : State} (hLast : At l.block (X.barriers c) last st)
    (hZero : (st.slots id).generation = 0)
    (hSource : ∀ g j, g < l.threads →
      GenerationOf l.block (X.barriers (g/l.block)) (g,j) id 0 →
      (g%l.block)/32 ∈ part ∧ ∃ pc mode, X.get (g,j) = some ⟨pc, .bar id count mode⟩) :
    NamedBar.Protocol count part id ((X.barriers c).take (last+1)) := by
  obtain ⟨tail, hFull⟩ := (hX.2 c hc).2.2
  intro r hr
  cases r with
  | exit _ _ => trivial
  | arrival slot warp cnt lanes =>
    intro hi
    subst slot
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    have hkFin := (List.getElem?_eq_some_iff.mp hk).1
    simp only [List.length_take] at hkFin
    rw [List.getElem?_take_of_lt (by omega : k < last+1)] at hk
    obtain ⟨before, after, hb, hp⟩ := run_at_record hFull hk
    have hMono := generation_mono_between (id := id) hb hLast (by omega)
    have hGen : (before.slots id).generation = 0 := by omega
    have hArr : arrive l.block before id warp cnt = .ok after := by
      simp only [Record.perform] at hp
      split_ifs at hp
      exact hp
    obtain ⟨_, off, hOff, hLocal, hLive⟩ := arrive_live hArr
    have hBound : off < 32 := Finset.mem_range.mp hOff
    have hWarp : (warp*32+off)/32 = warp := by omega
    have hAll := perform_arrival_lane hp hLocal hWarp hLive
    obtain ⟨⟨localIndex, evt⟩, hEvt, hIndex⟩ := List.mem_map.mp hAll
    change localIndex = warp*32+off at hIndex
    subst localIndex
    have hr := List.mem_of_getElem? hk
    obtain ⟨_, hOwner, pc, mode, he⟩ := ((hX.2 c hc).2.1 _ hr) _ hEvt
    have hg : evt.1 < l.threads := by rw [hOwner]; exact NamedBar.cta_thread_lt hc hLocal
    have hCta : evt.1 / l.block = c :=
      hX.ref_cta hr (List.mem_map.mpr ⟨(warp*32+off, evt), hEvt, rfl⟩)
    have hLane : evt.1 % l.block = warp*32+off := by
      rw [hOwner, Nat.mul_comm c, Nat.mul_add_mod, Nat.mod_eq_of_lt hLocal]
    have hG := generationOf_of_record hk hb hp hEvt
    rw [hGen, ← hCta] at hG
    obtain ⟨g, j⟩ := evt
    obtain ⟨hPart, pc', mode', hReal⟩ := hSource g j hg hG
    change (g % l.block)/32 ∈ part at hPart
    change g % l.block = warp*32+off at hLane
    rw [hLane, hWarp] at hPart
    rw [hReal] at he
    exact ⟨hPart, (Kind.bar.inj (congrArg Event.kind (Option.some.inj he))).2.1.symm⟩

/-- A participating lane of the first generation has an actual arrival. For a lane that
exited before completion, its earlier returned arrival is recorded before the exit. -/
theorem first_generation_member {l : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent l K A m X)
    {g finish id : Nat} {count : Option Nat} {part : Finset Nat} (hg : g < l.threads)
    (hShape : NamedBar.Shape l count part id) (hPart : (g%l.block)/32 ∈ part)
    (hDone : CompletesAt l.block (X.barriers (g/l.block)) finish id 0)
    (hProto : NamedBar.Protocol count part id
      ((X.barriers (g/l.block)).take (finish+1)))
    (hBeforeExit : ∀ k pc, X.get (g,k) = some ⟨pc, .exit⟩ →
      ∃ j < k, ∃ pc cnt, X.IsBarrier (g,j) id cnt pc) :
    ∃ j, GenerationOf l.block (X.barriers (g/l.block)) (g,j) id 0 := by
  let c := g/l.block
  let lane := g%l.block
  have hc := NamedBar.cta_lt hg
  have hLane : lane < l.block := Nat.mod_lt _ (NamedBar.block_pos_of_thread_lt hg)
  have hOwner : c*l.block+lane = g := by
    dsimp [c, lane]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod g l.block
  obtain ⟨record, before, after, hRec, hb, hP, hGen0, hGen1⟩ := hDone
  have hRun : At l.block (X.barriers c) (finish+1) after := by
    unfold At at hb ⊢
    rw [List.take_succ_eq_append_getElem (List.getElem?_eq_some_iff.mp hRec).1,
      (List.getElem?_eq_some_iff.mp hRec).2, run_append, hb]
    simp only [run, hP, Except.bind]
  by_cases hExit : lane ∈ after.exited
  · obtain ⟨ev, he⟩ := NamedBar.run_exited_mem hRun hExit
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
    have hLen := (List.getElem?_eq_some_iff.mp hk).1
    simp only [List.length_take] at hLen
    rw [List.getElem?_take_of_lt (by omega : k < finish+1)] at hk
    obtain ⟨_, hLoc, pc, hExit⟩ := (hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hk)
    have hSame : ev.1 = g := hLoc.trans hOwner
    obtain ⟨e, idx⟩ := ev
    change e = g at hSame
    subst e
    obtain ⟨j, hLt, pc', cnt, hBar⟩ := hBeforeExit idx pc hExit
    have hPassed : j+1 < (X.tr g).length := by
      have hBound : idx < (X.tr g).length := (List.getElem?_eq_some_iff.mp hExit).1
      omega
    obtain ⟨key, hKey, _⟩ := ctaBarDone_of_returned hX hBar hPassed
    obtain ⟨cnt', pc'', hGet⟩ := hKey.2.1
    change X.get (g,j) = some ⟨pc'', .bar (key%16) cnt' .sync⟩ at hGet
    rw [hBar] at hGet
    have hId : key%16 = id := (Kind.bar.inj (congrArg Event.kind (Option.some.inj hGet))).1.symm
    have hG := hKey.2.2
    rw [hId] at hG
    obtain ⟨i, st, w, cnt', lanes, t, hi, hAt, hm, hPhase, hStep⟩ := hG
    have hBefore := hX.ctaBar.arrival_before_exit hi
      (List.mem_map.mpr ⟨(t, (g,j)), hm, rfl⟩) hk rfl
    have hLe := generation_mono_between (id := id) hAt hb (by omega)
    have hZero : (st.slots id).generation = 0 := by omega
    exact ⟨j, i, st, w, cnt', lanes, t, hi, hAt, hm, hZero, hStep⟩
  · have hAfter : 0 < (after.slots id).generation := by omega
    obtain ⟨k, lanes, ev, hGet, hMember, hGen⟩ :=
      NamedBar.completed_participant_record (phase := 0) hProto hShape.pos hShape.target rfl
        hShape.bound hRun hAfter hLane hPart hExit
    have hK := (List.getElem?_eq_some_iff.mp hGet).1
    simp only [List.length_take] at hK
    rw [List.getElem?_take_of_lt (by omega : k < finish+1)] at hGet
    obtain ⟨_, hLoc, _, _⟩ := (hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hGet)
      (lane, ev) hMember
    have hSame : ev.1 = g := hLoc.trans hOwner
    obtain ⟨e, idx⟩ := ev
    change e = g at hSame
    subst e
    change GenerationOf l.block ((X.barriers c).take (finish+1)) (g,idx) id 0 at hGen
    exact ⟨idx, by
      simpa only [List.take_append_drop] using
        hGen.append (ys := (X.barriers c).drop (finish+1))⟩

/-- Once the candidate's ordinal is zero, a recorded arrival on that resource cannot coexist
with the candidate being the last unrecorded event of that lane. -/
private theorem recorded_conflicts_first_last {X : Execution} {c g id i : Nat}
    {count : Option Nat} {pc : Nat} {mode : BarMode}
    (hFirst : ((X.tr g).take ((X.tr g).length-1)).countP (Execution.isBarId id) = 0)
    (hEvent : X.get (g,i) = some ⟨pc, .bar id count mode⟩)
    (hRec : (g,i) ∈ (X.barriers c).flatMap Record.refs)
    (hFresh : (g,(X.tr g).length-1) ∉ (X.barriers c).flatMap Record.refs) : False := by
  have hLen : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hEvent).1
  by_cases hi : i < (X.tr g).length-1
  · have hGet : ((X.tr g).take ((X.tr g).length-1))[i]? = some ⟨pc, .bar id count mode⟩ := by
      rw [List.getElem?_take_of_lt hi]
      exact hEvent
    exact List.countP_eq_zero.mp hFirst _ (List.mem_of_getElem? hGet) (by simp [Execution.isBarId])
  · rw [show i = (X.tr g).length-1 by omega] at hRec
    exact hFresh hRec

/-- Appending a warp's first actual arrival has neither a count mismatch nor a duplicate.
The protocol is needed only until generation zero releases. If already released, the
participant's generation-zero arrival is already recorded. -/
theorem first_generation_no_append_fault {l : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent l K A m X)
    {c w id : Nat} {count : Option Nat} {part : Finset Nat} (hc : c < l.grid)
    (hShape : NamedBar.Shape l count part id) (hw : w ∈ part)
    (hOrdinal : NamedBar.WarpLastOrdinal l X c w id 0)
    (hProtocol : ∀ s, run l.block {} (X.barriers c) = .ok s →
      (s.slots id).generation = 0 → NamedBar.Protocol count part id (X.barriers c))
    (hMember : ∀ g, g < l.threads → g/l.block = c → (g%l.block)/32 ∈ part →
      Released l.block (X.barriers c) id 0 →
      ∃ i, GenerationOf l.block (X.barriers c) (g,i) id 0) :
    ¬ NamedBar.WarpAppendFault l X c w id count := by
  classical
  intro hFault
  obtain ⟨s, err, hs, hSources, hFresh, hFailed, hErr⟩ := hFault
  let g := c*l.block+w*32
  let j := (X.tr g).length-1
  have hLane : w*32 < l.block := by have := hShape.bound w hw; omega
  have hWarp : w*32/32 = w := Nat.mul_div_cancel _ (by decide)
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hLane
  have hOwner := NamedBar.lane_cta (c := c) (NamedBar.block_pos_of_thread_lt hg) hLane
  have hOwn : g / l.block = c := hOwner.1
  have hLocal : g % l.block = w*32 := hOwner.2
  have hP : (g % l.block)/32 ∈ part := by rw [hLocal, hWarp]; exact hw
  have hFirst := hOrdinal (w*32) hLane hWarp
  have hMem : (w*32, (g,j)) ∈ fullLanes l.block w (fun i =>
      (c*l.block+i, (X.tr (c*l.block+i)).length-1)) :=
    mem_fullLanes.mpr ⟨hLane, hWarp, rfl⟩
  obtain ⟨_, _, pc, mode, hGet⟩ := hSources _ hMem
  have hUnrecorded : (g,j) ∉ (X.barriers c).flatMap Record.refs :=
    hFresh _ (List.mem_map.mpr ⟨_, hMem, rfl⟩)
  by_cases hPositive : 0 < (s.slots id).generation
  · have hDone := Step.CtaBar.released_of_generation_lt (phase := 0) hs hPositive
    obtain ⟨i, hGen⟩ := hMember g hg hOwn hP hDone
    have hGen' : GenerationOf l.block (X.barriers (g/l.block)) (g,i) id 0 := by
      simpa only [hOwn] using hGen
    obtain ⟨cnt, pc, mode, he⟩ := hX.ctaBar.generation_barrier hGen'
    obtain ⟨idx, st, warp, cnt', lanes, lane, hRec, _, hIn, _, _⟩ := hGen
    exact recorded_conflicts_first_last hFirst he (List.mem_flatMap.mpr
      ⟨_, List.mem_of_getElem? hRec, List.mem_map.mpr ⟨(lane, (g,i)), hIn, rfl⟩⟩) hUnrecorded
  have hZero : (s.slots id).generation = 0 := by omega
  have hAtEnd : At l.block (X.barriers c) (X.barriers c).length s := by simpa [At] using hs
  have hProto := hProtocol s hs hZero
  have hLedger := hProto.run_ledger hShape.pos hShape.target rfl hShape.bound hs
  have hNoExit (i pc' : Nat) (he : X.get (g,i) = some ⟨pc', .exit⟩) : False := by
    have hn := Execution.exit_last hX hg he
    have hSame : i = j := by dsimp [j]; omega
    rw [hSame, hGet] at he
    exact Kind.noConfusion (congrArg Event.kind (Option.some.inj he))
  have hLive := NamedBar.not_exited_of_noExit hX hc hAtEnd hNoExit
  have hWL : warpLive l.block s.exited w :=
    ⟨0, by decide, by simpa only [Nat.add_zero] using hLane,
      by simpa only [Nat.add_zero] using hLive⟩
  have hNotArrived : w ∉ (s.slots id).arrived := by
    intro hArrived
    have hBalance := hLedger.balance w hw hWL
    rw [hZero, ite_eq_left hArrived] at hBalance
    obtain ⟨r, hr, hTagged⟩ := List.countP_pos_iff.mp
      (show 0 < idArrivals (X.barriers c) id w by omega)
    cases r with
    | exit => cases hTagged
    | arrival slot warp cnt lanes =>
      simp [isWarpIdArrival] at hTagged
      obtain ⟨hSlot, hW⟩ := hTagged
      subst slot
      subst warp
      obtain ⟨idx, hIdx⟩ := List.mem_iff_getElem?.mp hr
      obtain ⟨before, after, hb, ha⟩ := run_at_record hs hIdx
      have hLiveBefore := NamedBar.not_exited_of_noExit hX hc hb hNoExit
      have hWitness := perform_arrival_lane ha hLane hWarp hLiveBefore
      obtain ⟨q, hq, hqLane⟩ := List.mem_map.mp hWitness
      obtain ⟨_, hQOwner, pc', mode', hGet'⟩ := (hX.ctaBar.2 c hc).2.1 _ hr _ hq
      have hQ : q.2.1 = g := by rw [hQOwner, hqLane]
      have hGetAt : X.get (g,q.2.2) = some ⟨pc', .bar id cnt mode'⟩ := by
        rw [← hQ, Prod.eta]
        exact hGet'
      exact recorded_conflicts_first_last hFirst hGetAt
        (List.mem_flatMap.mpr ⟨_, hr, List.mem_map.mpr ⟨q, hq, Prod.ext hQ rfl⟩⟩) hUnrecorded
  simp only [NamedBar.warpRecord, Record.perform] at hFailed
  split_ifs at hFailed
  · have hWarpRange : w < warps l.block := by
      have := hShape.bound w hw
      unfold warps
      omega
    have hValid : w < warps l.block ∧ warpLive l.block s.exited w := ⟨hWarpRange, hWL⟩
    have hExpected := hLedger.expected
    by_cases hNone : (s.slots id).arrived = ∅ <;>
      simp [arrive, hShape.id_lt, hValid, hNotArrived, hShape.target, hExpected, hNone,
        bind, Except.bind, pure, Except.pure] at hFailed
  · have he := Except.error.inj hFailed
    rw [← he] at hErr
    cases hErr

/-- Full participation of the initial generation releases it. Its protocol is needed only if
the final object state has yet to advance to the next generation. -/
theorem first_generation_released_of_recorded {l : Launch} {X : Execution}
    (hX : CtaBarHistoryOk l X) {c id : Nat} {count : Option Nat} {part : Finset Nat}
    (hc : c < l.grid) (hShape : NamedBar.Shape l count part id)
    (hProtocol : ∀ s, run l.block {} (X.barriers c) = .ok s →
      (s.slots id).generation = 0 → NamedBar.Protocol count part id (X.barriers c))
    (hAll : ∀ w ∈ part, ∃ j pc mode,
      X.get (c*l.block+w*32,j) = some ⟨pc, .bar id count mode⟩ ∧
      (c*l.block+w*32,j) ∈ (X.barriers c).flatMap Record.refs) :
    Released l.block (X.barriers c) id 0 := by
  classical
  obtain ⟨u, hu⟩ := (hX.2 c hc).2.2
  by_cases hPos : 0 < (u.slots id).generation
  · exact Step.CtaBar.released_of_generation_lt (phase := 0) hu hPos
  have hZero : (u.slots id).generation = 0 := by omega
  have hAtEnd : At l.block (X.barriers c) (X.barriers c).length u := by simpa [At] using hu
  refine released_of_all_arrived (hProtocol u hu hZero)
    hShape.pos hShape.target rfl hShape.bound hu ?_
  intro w hw
  obtain ⟨j, pc, mode, he, href⟩ := hAll w hw
  obtain ⟨r, hRec, hRef⟩ := List.mem_flatMap.mp href
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hRec
  obtain ⟨s, t, hs, ht⟩ := run_at_record hu hi
  have hSource := (hX.2 c hc).2.1 r hRec
  cases r with
  | exit x y =>
    obtain ⟨_, _, pc', hGet⟩ := hSource
    change _ ∈ [y] at hRef
    rw [← (List.mem_singleton.mp hRef), he] at hGet
    exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hGet))
  | arrival slot warp cnt lanes =>
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hRef
    obtain ⟨_, hq2, pc', mode', hGet⟩ := hSource q hq
    rw [hqe, he] at hGet
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hGet
    obtain ⟨_, rfl, rfl, _⟩ := hGet
    have hLane : q.1 = w*32 := by rw [hqe] at hq2; simp only at hq2; omega
    have hWarp := ((perform_arrival_lanes ht).2.1 q hq).2.1
    rw [hLane, Nat.mul_div_cancel _ (by decide : 0 < 32)] at hWarp
    subst warp
    have hLe := generation_mono_between (id := id) hs hAtEnd
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hi).1)
    exact ⟨i, lanes, s, hi, hs, by omega⟩

end PTX.CtaBarrier
