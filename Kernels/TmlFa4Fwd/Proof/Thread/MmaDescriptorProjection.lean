-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadySequence
public import Kernels.TmlFa4Fwd.Proof.Thread.Mma
import Lemmas.Flow.Final
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

/-- Retain cache-ready acquisitions and one descriptor projection chosen by the caller. -/
def descriptorProjection (select : Event → Bool) (e : Event) : Option Event :=
  if select e || (readyEvent e).isSome then some e else none

/-- Check each selected broadcast at the ordinal of the currently acquired cache use. -/
def DescriptorTrace (select : Event → Bool) (observes : Nat → Event → Prop) (use : Nat)
    (events : List Event) : Prop :=
  ∀ pre e tail, events = pre ++ e :: tail → select e = true →
    observes (use + (pre.filterMap readyEvent).length - 1) e

theorem descriptorTraceQuiet {select : Event → Bool} {observes : Nat → Event → Prop} {use : Nat}
    {events : List Event} (hNone : ∀ e ∈ events, select e = false) :
    DescriptorTrace select observes use events := by
  intro pre e tail hSplit hEvent
  have h := hNone e (hSplit.symm ▸ List.mem_append_right _ (by simp))
  rw [hEvent] at h
  cases h

theorem descriptorTraceAppend {select : Event → Bool} {observes : Nat → Event → Prop} {use : Nat}
    {xs ys : List Event} (hQuiet : ∀ e ∈ xs, select e = false)
    (hTail : DescriptorTrace select observes (use + (xs.filterMap readyEvent).length) ys) :
    DescriptorTrace select observes use (xs ++ ys) := by
  induction xs generalizing use with
  | nil => simpa using hTail
  | cons x xs ih =>
    intro pre e tail hTrace hMark
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hTrace
      have h := hTrace.1 ▸ hQuiet x List.mem_cons_self
      rw [hMark] at h
      cases h
    | cons first rest =>
      simp only [List.cons_append, List.cons.injEq] at hTrace
      obtain ⟨rfl, hEq⟩ := hTrace
      have hCount (es : List Event) : ((x :: es).filterMap readyEvent).length =
          ([x].filterMap readyEvent).length + (es.filterMap readyEvent).length := by
        rw [show x :: es = [x] ++ es from rfl, List.filterMap_append, List.length_append]
      rw [hCount xs, ← Nat.add_assoc] at hTail
      have h := ih (fun f hf => hQuiet f (List.mem_cons_of_mem _ hf)) hTail rest e tail hEq hMark
      rw [hCount rest, ← Nat.add_assoc]
      exact h

theorem descriptorTraceAtHead {select : Event → Bool} {observes : Nat → Event → Prop}
    {use : Nat} {e : Event} {rest : List Event} (hErase : readyEvent e = none)
    (hEvent : observes use e) (hTail : DescriptorTrace select observes (use + 1) rest) :
    DescriptorTrace select observes (use + 1) (e :: rest) := by
  intro pre event tail hSplit hSelect
  cases pre with
  | nil =>
    obtain rfl := (List.cons.inj hSplit).1
    simpa using hEvent
  | cons first pre =>
    obtain ⟨rfl, hRest⟩ := List.cons.inj hSplit
    simp only [List.filterMap_cons, hErase]
    exact hTail pre event tail hRest hSelect

theorem descriptorProjectionEmpty {select : Event → Bool} {events : List Event}
    (hEmpty : events.filterMap (descriptorProjection select) = []) :
    (∀ e ∈ events, select e = false) ∧ events.filterMap readyEvent = [] := by
  have h := List.filterMap_eq_nil_iff.mp hEmpty
  refine ⟨?_, List.filterMap_eq_nil_iff.mpr ?_⟩
  · intro e he
    cases hf : select e
    · rfl
    · have hBad := h e he
      simp [descriptorProjection, hf] at hBad
  · intro e he
    cases hr : readyEvent e
    · rfl
    · have hBad := h e he
      simp [descriptorProjection, hr] at hBad

private theorem descriptorIntervalExit (i : Fin 9) {s : TState} {F : List (Nat × Value)}
    (hPc : s.pc ∈ (readyInterval i).exits) (hf : s.fault = none) (hs : RoleShape s)
    (hF : Holds s.regs F) : At s s.pc F := by
  have hNo : ∀ pc ∈ (readyInterval i).exits, pc ≠ 1909 := by
    fin_cases i <;> simp [readyInterval]
  exact ⟨rfl, hs.2.2 (hNo _ hPc), hs.2.1, hf, hF⟩

/-- A checked interval that contains no selected broadcast adds no descriptor
and carries the live ready registers to its decoded exit. -/
theorem descriptorTraceInterval (i : Fin 9) {l : Launch} {g use : Nat} {s : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit}
    {select : Event → Bool} {observes : Nat → Event → Prop}
    (hPc : (readyInterval i).inside s.pc)
    (hNo : ∀ e : Event, (readyInterval i).inside e.pc → select e = false)
    (hs : At s s.pc F) (hWarp : (1062, b32 12) ∈ F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ (readyInterval i).keep)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u tail post}, u.pc ∈ (readyInterval i).exits → At u u.pc F →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      DescriptorTrace select observes use tail) :
    DescriptorTrace select observes use es := by
  have hShape : RoleShape s := ⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩
  rcases readyIntervalCutWith (descriptorProjection select) i (fun e he => by
    simp [descriptorProjection, hNo _ he, readyEventOutside i he]) hw hPc
    ⟨hShape, holds_mem hs.2.2.2.2 hWarp⟩ hs.2.2.2.2 hKeep with hEmpty |
      ⟨u, pre, tail, post, hSplit, hProj, hBound, hExit, hClean, hRole, hF, hWalk⟩
  · exact descriptorTraceQuiet (descriptorProjectionEmpty hEmpty).1
  · obtain ⟨hQuiet, hReady⟩ := descriptorProjectionEmpty hProj
    rw [hSplit]
    have hTail := after hExit (descriptorIntervalExit i hExit hClean hRole.1 hF) hBound hWalk
    exact descriptorTraceAppend hQuiet (by simpa [hReady] using hTail)

theorem descriptorTraceLocal {l : Launch} {g use pc nextPc n : Nat} {s : TState}
    {F G : List (Nat × Value)} {es : List Event} {vs : List Visit}
    {select : Event → Bool} {observes : Nat → Event → Prop}
    (hSeg : Seg kernel Assumptions.all l g n pc F nextPc G) (ht : At s pc F)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u post}, At u nextPc G → post.length ≤ vs.length →
      Walk kernel Assumptions.all l g u es post → DescriptorTrace select observes use es) :
    DescriptorTrace select observes use es := by
  obtain ⟨u, hr, hu⟩ := hSeg s ht
  rcases advanceWalkLocals hr hw with rfl | ⟨post, hLen, _, hWalk⟩
  · exact descriptorTraceQuiet (by simp)
  · exact after hu (by omega) hWalk

/-- The four actual cache-ready polls in the MMA role. -/
def descriptorReadyWait : Fin 4 → Fin 14
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | _ => 9

theorem descriptorTracePoll {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (i : Fin 4) {g use : Nat} {t : TState} {F : List (Nat × Value)}
    {es : List Event} {vs : List Visit} {select : Event → Bool} {observes : Nat → Event → Prop}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite (descriptorReadyWait i)).result)
    (hBase : ((waitSite (descriptorReadyWait i)).base, b32 (readyAddr l use)) ∈ F)
    (hPar : ((waitSite (descriptorReadyWait i)).phase, b32 (readyWord use)) ∈ F)
    (hSkip : ∀ ok, select ⟨(waitSite (descriptorReadyWait i)).pc,
      .wait ⟨.shared, g / l.block, readyAddr l use⟩ (readyWord use) ok true .cta⟩ = false)
    (ht : At t (waitSite (descriptorReadyWait i)).pc F)
    (hw : Walk kernel Assumptions.all l g t es vs)
    (after : ∀ {u rest post}, post.length < vs.length →
      At u ((waitSite (descriptorReadyWait i)).pc + 3) F →
      Walk kernel Assumptions.all l g u rest post → DescriptorTrace select observes
        (use + 1) rest) :
    DescriptorTrace select observes use es := by
  have hAddr : readyAddr l use < 2 ^ 32 := by
    have h := hp.shared.2.1
    have hSlot := (readyStage use).isLt
    unfold readyAddr
    omega
  have hAlign : readyAddr l use % 8 = 0 := by
    have h := hp.shared.1
    unfold readyAddr
    omega
  let ev := fun ok => Event.mk (waitSite (descriptorReadyWait i)).pc
    (.wait ⟨.shared, g / l.block, readyAddr l use⟩ (readyWord use) ok true .cta)
  have hMarked : (List.finRange 4).any (fun j => readyHead j == (ev true).pc) = true := by
    change (List.finRange 4).any (fun j => readyHead j == (waitSite (descriptorReadyWait i)).pc) =
      true
    fin_cases i <;> decide
  have hMark : (readyEvent (ev true)).isSome = true := by
    simp [readyEvent, ev, hMarked]
  have erase (n : Nat) : (List.replicate n (ev false)).filterMap readyEvent = [] := by
    simp [readyEvent, ev]
  rcases waitWalk (descriptorReadyWait i) hAddr hAlign (readyWord_lt use) hFresh hBase hPar
    ht hw with ⟨n, hEq⟩ | ⟨n, rest, hEq, hTail⟩
  · change es = List.replicate n (ev false) at hEq
    rw [hEq]
    apply descriptorTraceQuiet
    intro e he
    exact (List.eq_of_mem_replicate he) ▸ hSkip false
  · change es = List.replicate n (ev false) ++ ev true :: rest at hEq
    have hOne : ((List.replicate n (ev false) ++ [ev true]).filterMap readyEvent).length = 1 := by
      obtain ⟨pair, hp⟩ := Option.isSome_iff_exists.mp hMark
      simp [List.filterMap_append, erase, hp]
    rw [hEq, show ev true :: rest = [ev true] ++ rest from rfl, ← List.append_assoc]
    apply descriptorTraceAppend
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact (List.eq_of_mem_replicate he) ▸ hSkip false
      · exact (List.mem_singleton.mp he).symm ▸ hSkip true
    rw [hOne]
    rcases hTail with rfl | ⟨u, post, hLength, hu, hWalk⟩
    · exact descriptorTraceQuiet (by simp)
    · exact after hLength hu hWalk


/-- Read an actual marked descriptor at the successful ready count of its thread prefix. -/
theorem actualDescriptorTrace {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} {select : Event → Bool} {observes : Nat → Event → Prop}
    (hWarp : Prologue.warpIndex l g = 12) (he : X.get (g, index) = some e)
    (hLate : 1907 < e.pc) (hSelected : select e = true)
    (hRole : ∀ {t es vs}, At t 1908 (readyFrame l) →
      Walk kernel Assumptions.all l g t es vs → DescriptorTrace select observes 0 es) :
    let d := atPrefix l X g index
    observes (d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2 - 1) e := by
  have hg := event_thread_lt hX he
  obtain ⟨s,visits,hIndex,hAt,hWalk,_,_,inst,hHint⟩ :=
    mmaRoleWalkOfDemand hp hX he hWarp (.inl hLate)
  have hFrame : At s 1908 (readyFrame l) := hAt.mono ⟨hAt.2.2.2.2.2.1,
    hAt.2.2.2.2.1,trivial⟩
  have hTrace := hRole hFrame hWalk
  let suffix := (X.tr g).drop 6
  let k := index-6
  have hSuffix : suffix[k]? = some e := by
    dsimp only [suffix,k]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  have hSplit : suffix = suffix.take k ++ e :: suffix.drop (k+1) := by
    conv_lhs => rw [← List.take_append_drop k suffix]
    have hDrop : (suffix.drop k)[0]? = some e := by
      rwa [List.getElem?_drop,Nat.add_zero]
    cases h : suffix.drop k with
    | nil => simp [h] at hDrop
    | cons first rest =>
      obtain rfl : first = e := Option.some.inj (by simpa [h] using hDrop)
      have hRest : suffix.drop (k+1) = rest := by
        rw [← List.drop_drop,h]
        rfl
      rw [hRest]
  have hEvidence := hTrace (suffix.take k) e _ hSplit hSelected
  have hPrefix : ((X.tr g).take 6).filterMap readyEvent = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro prior hm
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hm
    have hjTrace := hj
    rw [List.length_take] at hjTrace
    rw [List.getElem_take]
    have hJLen : j < (X.tr g).length := by omega
    have hpGet : X.get (g,j) = some (X.tr g)[j] := List.getElem?_eq_getElem hJLen
    cases hMark : readyEvent (X.tr g)[j] with
    | none => rfl
    | some pair =>
      have hPc : ∃ i : Fin 4, (X.tr g)[j].pc = readyHead i := by
        unfold readyEvent at hMark
        split at hMark
        · split at hMark
          · rename_i hSite
            obtain ⟨i,_,hCode⟩ := List.any_eq_true.mp hSite
            exact ⟨i,(beq_iff_eq.mp hCode).symm⟩
          · cases hMark
        · cases hMark
      obtain ⟨i,hSite⟩ := hPc
      have hLate : 173 < (X.tr g)[j].pc := by rw [hSite]; fin_cases i <;> decide
      obtain ⟨_,_,hJ,_,_⟩ := Prologue.nonzeroCommonPrefixOfLateEvent hp hX hg
        (by rw [hWarp]; decide) hpGet hLate
      obtain rfl : j = 5 := by omega
      have hEq := Option.some.inj (hpGet.symm.trans hHint)
      rw [hEq] at hMark
      cases hMark
  have hLen : ((X.tr g).take 6).length ≤ index := (List.length_take_le ..).trans hIndex
  have hTake : ((X.tr g).take 6).take index = (X.tr g).take 6 :=
    List.take_of_length_le hLen
  have hCount : ((suffix.take k).filterMap readyEvent).length =
      (((X.tr g).take index).filterMap readyEvent).length := by
    have hPrefixLen : ((X.tr g).take 6).length = 6 := by
      rw [List.length_take, Nat.min_eq_left]
      exact hIndex.trans (len_of_get he).le
    conv_rhs => rw [← List.take_append_drop 6 (X.tr g),List.take_append]
    rw [hTake,hPrefixLen,List.filterMap_append,hPrefix,List.nil_append]
  have hUse := Thread.Mma.readyUsesAtPrefix hp hX hg hWarp index
  simpa only [hCount, hUse, Nat.zero_add] using hEvidence

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
