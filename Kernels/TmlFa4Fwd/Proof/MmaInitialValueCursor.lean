-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadySequence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Reach a checked interval exit when observations remain. -/
theorem requireReadyIntervalWith {α : Type} (mark : Event → Option α) (i : Fin 9)
    (hErase : ∀ e : Event,
      (readyInterval i).lo ≤ e.pc ∧ e.pc < (readyInterval i).hi → mark e = none)
    {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hPc : (readyInterval i).lo ≤ s.pc ∧ s.pc < (readyInterval i).hi)
    (hs : At s s.pc F) (hWarp : (1062, b32 12) ∈ F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ (readyInterval i).keep)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSome : es.filterMap mark ≠ []) :
    ∃ u pre tail post, u.pc ∈ (readyInterval i).exits ∧ At u u.pc F ∧
      es = pre ++ tail ∧ pre.filterMap mark = [] ∧
      Walk kernel Assumptions.all l g u tail post := by
  have hShape : RoleShape s := ⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩
  rcases readyIntervalCutWith mark i hErase hw hPc ⟨hShape, holds_mem hs.2.2.2.2 hWarp⟩
      hs.2.2.2.2 hKeep with hEmpty | ⟨u, pre, tail, post, hE, hP, _, hX, hF, hS, hH, hW⟩
  · exact (hSome hEmpty).elim
  have hNo : ∀ pc ∈ (readyInterval i).exits, pc ≠ 1909 := by
    fin_cases i <;> simp [readyInterval]
  exact ⟨u, pre, tail, post, hX, ⟨rfl, hS.1.2.2 (hNo _ hX), hS.1.2.1, hF, hH⟩,
    hE, hP, hW⟩

/-- A nonempty actual suffix forces the traversal of a checked local segment. -/
theorem requireReadySegmentNonempty {l : Launch} {g pc nextPc n : Nat} {s : TState}
    {F G : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hSeg : Seg kernel Assumptions.all l g n pc F nextPc G) (ht : At s pc F)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSome : es ≠ []) :
    ∃ u post, At u nextPc G ∧ Walk kernel Assumptions.all l g u es post := by
  obtain ⟨u, hr, hu⟩ := hSeg s ht
  rcases advanceWalkLocals hr hw with rfl | ⟨post, _, _, hWalk⟩
  · exact (hSome rfl).elim
  · exact ⟨u, post, hu, hWalk⟩

private theorem requireReadyInterval (i : Fin 9) {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hPc : (readyInterval i).lo ≤ s.pc ∧ s.pc < (readyInterval i).hi)
    (hs : At s s.pc F) (hWarp : (1062, b32 12) ∈ F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ (readyInterval i).keep)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSome : es.filterMap readyEvent ≠ []) :
    ∃ u pre tail post, u.pc ∈ (readyInterval i).exits ∧ At u u.pc F ∧
      es = pre ++ tail ∧ pre.filterMap readyEvent = [] ∧
      Walk kernel Assumptions.all l g u tail post :=
  requireReadyIntervalWith readyEvent i (fun _ => readyEventOutside i) hPc hs hWarp hKeep hw hSome

private theorem requireReadySegment {l : Launch} {g pc nextPc n : Nat} {s : TState}
    {F G : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hSeg : Seg kernel Assumptions.all l g n pc F nextPc G) (ht : At s pc F)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSome : es.filterMap readyEvent ≠ []) :
    ∃ u post, At u nextPc G ∧ Walk kernel Assumptions.all l g u es post :=
  requireReadySegmentNonempty hSeg ht hw (fun h => hSome (by rw [h]; rfl))

private theorem noReadyFromInactive {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {vs : List Visit} (ht : At t 2763 [(1062, b32 12)])
    (hw : Walk kernel Assumptions.all l g t es vs) : es.filterMap readyEvent = [] := by
  by_contra hn
  obtain ⟨u, pre, tail, post, hExit, hu, he, hPre, hWalk⟩ := requireReadyInterval 8
    (by rw [ht.1]; decide) ⟨rfl, ht.2⟩ (by simp) (by decide) hw hn
  have hPc : u.pc = 3099 := by simpa [readyInterval] using hExit
  have hRange := mmaEpilogueExitEvents hPc hu.2.2.2.1 (.inl rfl) hu.2.2.2.2.1 hWalk
  apply hn
  rw [he, List.filterMap_append, hPre, List.nil_append]
  apply List.filterMap_eq_nil_iff.mpr
  intro e hm
  have hLate := hRange e hm
  obtain ⟨pc, kind⟩ := e
  dsimp only at hLate
  subst pc
  cases kind <;> try rfl
  case wait _ _ ok _ _ => cases ok <;> rfl

/-- The first successful ready acquire initializes the actual common K cursor. -/
theorem initialKeyCursor {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 1908 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs)
    (hTwo : 1 < (es.filterMap readyEvent).length) :
    ∃ u pre tail post, es = pre ++ tail ∧ pre.filterMap readyEvent = [readyOperand l g 0] ∧
      At u 2148 (readyFrame l) ∧
      Walk kernel Assumptions.all l g u tail post := by
  have hExists : es.filterMap readyEvent ≠ [] := by
    intro h; rw [h] at hTwo; contradiction
  obtain ⟨u, pre, rest, visits, hExit, hu, hSplit₁, hPre, hWalk⟩ := requireReadyInterval 0
    (by rw [ht.1]; decide) ⟨rfl, ht.2⟩ (by simp [readyFrame])
    (by simp [readyFrame, readyInterval]) hw hExists
  have hProject : es.filterMap readyEvent = rest.filterMap readyEvent := by simp [hSplit₁, hPre]
  have hRest : rest.filterMap readyEvent ≠ [] := hProject ▸ hExists
  have hBranch : u.pc = 2140 ∨ u.pc = 2763 := by simpa [readyInterval] using hExit
  rcases hBranch with hPc | hPc
  · obtain ⟨v, vVisits, hv, hVWalk⟩ :=
      requireReadySegment (readyInitialPhase l g) ⟨hPc, hu.2⟩ hWalk hRest
    obtain ⟨w, pre', source, wVisits, hExit, hwAt, hSplit₂, hPre', hWWalk⟩ := requireReadyInterval 1
      (by rw [hv.1]; decide) ⟨rfl, hv.2⟩ (by simp [readyFrame])
      (by simp [readyFrame, readyInterval]) hVWalk hRest
    have hProj' : rest.filterMap readyEvent = source.filterMap readyEvent := by
      simp [hSplit₂, hPre']
    have hwAt' : At w 2144 ((2536, b32 0) :: readyFrame l) :=
      ⟨by simpa [readyInterval] using hExit, hwAt.2⟩
    obtain ⟨z, zVisits, hz, hzWalk⟩ :=
      requireReadySegment (readyInitialAddress hp g) hwAt' hWWalk (hProj' ▸ hRest)
    have hAddr : l.sharedBase + 32 < 2 ^ 32 := by have := hp.shared.2.1; omega
    have hAlign : (l.sharedBase + 32) % 8 = 0 := by have := hp.shared.1; omega
    let ev := fun ok => Event.mk 2145 (.wait ⟨.shared, g/l.block,l.sharedBase+32⟩ 0 ok true .cta)
    have hMark : readyEvent (ev true) = some (readyOperand l g 0) := by
      have h : (List.finRange 4).any (fun i => readyHead i == 2145) = true := by decide
      simp [ev, readyEvent, h, readyOperand, Loader.readySlot_address, readyStage,
        readyWord, MbarRing.Index.slot, MbarRing.Index.round]
    have hRetries (n : Nat) : (List.replicate n (ev false)).filterMap readyEvent = [] := by
      simp [readyEvent, ev]
    have hCount : 1 < (source.filterMap readyEvent).length := by
      rw [← hProj', ← hProject]
      exact hTwo
    rcases waitWalk 1 hAddr hAlign (show 0 < 2 by decide)
        (by simp [waitSite, readyFrame]) (by simp [waitSite]) (by simp [waitSite]) hz hzWalk with
        ⟨n, hOnly⟩ | ⟨n, tail, hSplit, hAfter⟩
    · change source = List.replicate n (ev false) at hOnly
      rw [hOnly, hRetries] at hCount
      contradiction
    · have hOut : source.filterMap readyEvent =
          readyOperand l g 0 :: tail.filterMap readyEvent := by
        change source = List.replicate n (ev false) ++ ev true :: tail at hSplit
        rw [hSplit, List.filterMap_append, hRetries, List.nil_append, List.filterMap_cons, hMark]
      rcases hAfter with rfl | ⟨f, post, _, hf, hFWalk⟩
      · rw [hOut] at hCount
        simp at hCount
      · change source = List.replicate n (ev false) ++ ev true :: tail at hSplit
        refine ⟨f, pre ++ pre' ++ List.replicate n (ev false) ++ [ev true], tail, post,
          ?_, ?_, ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.2⟩, hFWalk⟩
        · simp [hSplit₁, hSplit₂, hSplit, List.append_assoc]
        · simp [hPre, hPre', hRetries, hMark]
  · have hu' : At u u.pc [(1062, b32 12)] := by at_select hu
    have hi : At u 2763 [(1062, b32 12)] := ⟨hPc, hu'.2⟩
    exact (hRest (noReadyFromInactive hi hWalk)).elim

def initialValueWaitSite (steady : Bool) : Fin 14 := if steady then 3 else 9

def initialValueWaitFacts (l : Launch) (steady : Bool) : List (Nat × Value) :=
  ((waitSite (initialValueWaitSite steady)).base, b32 (readyAddr l 1)) ::
    ringFrame l 7207 7208 1

/-- Both routes to the initial V wait preserve observations and establish the same ring use. -/
theorem initialValueWaitThroughRoute {α : Type} (mark : Event → Option α)
    (hErase : ∀ (i : Fin 3) (e : Event),
      (readyInterval (([2,3,7] : List (Fin 9))[i])).lo ≤ e.pc ∧
        e.pc < (readyInterval (([2,3,7] : List (Fin 9))[i])).hi → mark e = none)
    {l : Launch} {g : Nat} {t : TState}
    {es : List Event} {vs : List Visit} (ht : At t t.pc (readyFrame l))
    (hPc : 2148 ≤ t.pc ∧ t.pc < 2280)
    (hw : Walk kernel Assumptions.all l g t es vs) (hSome : es.filterMap mark ≠ [])
    {p : Params} {m : Mem0} (hp : Pre p l m) :
    ∃ steady u pre tail post, es = pre ++ tail ∧ pre.filterMap mark = [] ∧
      At u (waitSite (initialValueWaitSite steady)).pc (initialValueWaitFacts l steady) ∧
      Walk kernel Assumptions.all l g u tail post := by
  obtain ⟨u, pre, suffix, uVisits, hExit, hu, hSplit, hPre, hUWalk⟩ :=
    requireReadyIntervalWith mark 2 (hErase 0) hPc ht (by simp [readyFrame])
      (by simp [readyFrame, readyInterval]) hw hSome
  have hSuffix : suffix.filterMap mark ≠ [] := by
    simpa [hSplit, hPre] using hSome
  have hu' : At u 2280 (readyFrame l) := ⟨by simpa [readyInterval] using hExit, hu.2⟩
  obtain ⟨v, vVisits, hv, hVWalk⟩ := requireReadySegmentNonempty (readySeedShort l g) hu' hUWalk
        (fun h => hSuffix (by rw [h]; rfl))
  obtain ⟨w, pre', rest, wVisits, hOpen, hwAt, hSplit', hPre', hWWalk⟩ :=
    requireReadyIntervalWith mark 3 (hErase 1)
      (by rw [hv.1]; decide) ⟨rfl, hv.2⟩ (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hVWalk hSuffix
  have hRest : rest.filterMap mark ≠ [] := by
    simpa [hSplit', hPre'] using hSuffix
  have hPath : w.pc = 2287 ∨ w.pc = 2534 := by simpa [readyInterval] using hOpen
  rcases hPath with hSteady | hTail
  · have hSeed : At w 2287 (readyFrame l) :=
      ⟨hSteady, hwAt.2.1, hwAt.2.2.1, hwAt.2.2.2.1, hwAt.2.2.2.2.2.2⟩
    obtain ⟨s, sVisits, hs, hSWalk⟩ :=
      requireReadySegmentNonempty (readySeedSteady l g) hSeed hWWalk
        (fun h => hRest (by rw [h]; rfl))
    obtain ⟨z, post, hz, hZWalk⟩ :=
      requireReadySegmentNonempty (readyAddress hp g 0 1) hs hSWalk
        (fun h => hRest (by rw [h]; rfl))
    exact ⟨true, z, pre ++ pre', rest, post, by simp [hSplit, hSplit', List.append_assoc],
      by simp [hPre, hPre'], hz, hZWalk⟩
  · have hw' : At w 2534 (ringFrame l 7207 7208 1) := ⟨hTail,hwAt.2⟩
    obtain ⟨s, pre'', ending, sVisits, hEnd, hs, hSplit'', hPre'', hSWalk⟩ :=
      requireReadyIntervalWith mark 7 (hErase 2) (by rw [hw'.1]; decide) ⟨rfl, hw'.2⟩
        (by simp [ringFrame, readyFrame]) (by simp [ringFrame, readyFrame, readyInterval])
        hWWalk hRest
    have hEnding : ending.filterMap mark ≠ [] := by simpa [hSplit'', hPre''] using hRest
    have hs' : At s 2542 (ringFrame l 7207 7208 1) :=
      ⟨by simpa [readyInterval] using hEnd, hs.2⟩
    obtain ⟨z, post, hz, hZWalk⟩ :=
      requireReadySegmentNonempty (readyAddress hp g 2 1) hs' hSWalk
        (fun h => hEnding (by rw [h]; rfl))
    exact ⟨false, z, pre ++ pre' ++ pre'', ending, post,
      by simp [hSplit, hSplit', hSplit'', List.append_assoc],
      by simp [hPre, hPre', hPre''], hz, hZWalk⟩

private theorem afterKeyToValueCursor {l : Launch} {g : Nat} {t : TState}
    {es : List Event} {vs : List Visit} (ht : At t 2148 (readyFrame l))
    (hw : Walk kernel Assumptions.all l g t es vs) (hSome : es.filterMap readyEvent ≠ [])
    {p : Params} {m : Mem0} (hp : Pre p l m) :
    ∃ steady u pre tail post, es = pre ++ tail ∧ pre.filterMap readyEvent = [] ∧
      At u (waitSite (initialValueWaitSite steady)).pc (initialValueWaitFacts l steady) ∧
      Walk kernel Assumptions.all l g u tail post :=
  initialValueWaitThroughRoute readyEvent (fun i _ => readyEventOutside _)
    ⟨rfl,ht.2⟩ (by rw [ht.1]; decide) hw hSome hp

/-- If two successful K/V acquisitions appear in the actual prefix, the second
starts from the initialized slot-one frame on the executed steady or short path. -/
theorem initialValueCursorFromEntry {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 1908 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs)
    (hTwo : 1 < (es.filterMap readyEvent).length) :
    ∃ steady u pre tail post, es = pre ++ tail ∧ pre.filterMap readyEvent = [readyOperand l g 0] ∧
      At u (waitSite (initialValueWaitSite steady)).pc (initialValueWaitFacts l steady) ∧
      Walk kernel Assumptions.all l g u tail post := by
  obtain ⟨f, pre, rest, visits, hSplit, hK, hf, hFWalk⟩ := initialKeyCursor hp ht hw hTwo
  have hSome : rest.filterMap readyEvent ≠ [] := by
    intro h
    rw [hSplit, List.filterMap_append, hK, h] at hTwo
    simp at hTwo
  obtain ⟨steady,u,pre',tail,post,hRest,hEmpty,hu,hUWalk⟩ :=
    afterKeyToValueCursor hf hFWalk hSome hp
  exact ⟨steady,u,pre++pre',tail,post,by simp [hSplit,hRest,List.append_assoc],
    by simp [hK,hEmpty],hu,hUWalk⟩

def initialValueWaitEvent (l : Launch) (g : Nat) (steady ok : Bool) : Event :=
  ⟨(waitSite (initialValueWaitSite steady)).pc,
    .wait ⟨.shared, g/l.block, readyAddr l 1⟩ 0 ok true .cta⟩

/-- The actual second successful ready poll carries the slot-one scalar cursor
through to its genuine continuation, including any number of failed attempts. -/
theorem initialValueSuccessFromEntry {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 1908 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs)
    (hTwo : 1 < (es.filterMap readyEvent).length) :
    ∃ steady pre tail, es = pre ++ initialValueWaitEvent l g steady true :: tail ∧
      pre.filterMap readyEvent = [readyOperand l g 0] ∧
      (tail = [] ∨ ∃ u post,
        At u ((waitSite (initialValueWaitSite steady)).pc + 3) (initialValueWaitFacts l steady) ∧
        Walk kernel Assumptions.all l g u tail post) := by
  obtain ⟨steady, u, pre, tail, post, hSplit, hPre, hu, hWalk⟩ :=
    initialValueCursorFromEntry hp ht hw hTwo
  have hAddr : readyAddr l 1 < 2 ^ 32 := by
    have := hp.shared.2.1
    dsimp [readyAddr, readyStage, MbarRing.Index.slot]
    omega
  have hAlign : readyAddr l 1 % 8 = 0 := by
    have := hp.shared.1
    dsimp [readyAddr, readyStage, MbarRing.Index.slot]
    omega
  have hRetries (n : Nat) :
      (List.replicate n (initialValueWaitEvent l g steady false)).filterMap readyEvent = [] := by
    simp [readyEvent, initialValueWaitEvent]
  have hFresh : ∀ pair ∈ initialValueWaitFacts l steady,
      pair.1 ≠ (waitSite (initialValueWaitSite steady)).result := by
    cases steady <;> simp [initialValueWaitFacts, initialValueWaitSite, waitSite, ringFrame,
      readyFrame]
  have hBase : ((waitSite (initialValueWaitSite steady)).base, b32 (readyAddr l 1)) ∈
      initialValueWaitFacts l steady := by simp [initialValueWaitFacts]
  have hPhase : ((waitSite (initialValueWaitSite steady)).phase, b32 0) ∈
      initialValueWaitFacts l steady := by
    cases steady <;> simp [initialValueWaitFacts, initialValueWaitSite, waitSite, ringFrame,
      readyWord, MbarRing.Index.round]
  rcases waitWalk (initialValueWaitSite steady) hAddr hAlign (show 0 < 2 by decide)
      hFresh hBase hPhase hu hWalk with ⟨n, hOnly⟩ | ⟨n, rest, hSplit', hAfter⟩
  · change tail = List.replicate n (initialValueWaitEvent l g steady false) at hOnly
    rw [hSplit,hOnly,List.filterMap_append,hPre,hRetries] at hTwo
    simp at hTwo
  · change tail = List.replicate n (initialValueWaitEvent l g steady false) ++
      initialValueWaitEvent l g steady true :: rest at hSplit'
    refine ⟨steady, pre ++ List.replicate n (initialValueWaitEvent l g steady false), rest,
      by simp [hSplit,hSplit',List.append_assoc], by simp [hPre,hRetries], ?_⟩
    exact hAfter.imp_right (fun ⟨w, restVisits, _, hwAt, hWWalk⟩ => ⟨w, restVisits, hwAt, hWWalk⟩)

end
end PTX.Kernels.TmlFa4Fwd.Mma
