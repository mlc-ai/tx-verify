-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionReadyElements
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlotGeometry
import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private def PassedVectorElement (site element : Nat) (s : TState) : Prop :=
  site < s.pc ∨ s.pc = site ∧ element < s.sub

private theorem afterVectorElement {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (box : Fin 4) (chunk : Fin 8) {element : Nat}
    (hPc : s.pc = outputStorePc stage box chunk) (hSub : s.sub ≤ 3) (hSeen : element ≤ s.sub)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    7755 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 ∧
      PassedVectorElement (outputStorePc stage box chunk) element u := by
  obtain ⟨a, data, hEvent, hElem, hu⟩ := vectorElementStep stage box chunk hPc he
  have hSite : 7755 ≤ outputStorePc stage box chunk ∧ outputStorePc stage box chunk < 9205 := by
    fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide
  rw [hu]
  unfold afterStore
  have hLen : (outputOperands stage box chunk).length = 4 := List.length_ofFn
  rw [hLen]
  split
  · rename_i hk
    refine ⟨by change 7755 ≤ s.pc; omega, by change s.pc ≤ 9205; omega,
      by change s.sub + 1 ≤ 3; omega, .inr ⟨hPc, ?_⟩⟩
    change element < s.sub + 1
    omega
  · exact ⟨by change 7755 ≤ s.pc + 1; omega, by change s.pc + 1 ≤ 9205; omega,
      Nat.zero_le _, .inl (by change outputStorePc stage box chunk < s.pc + 1; omega)⟩

private theorem afterElementStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (stage : Fin 2) (box : Fin 4) (chunk : Fin 8) {element : Nat}
    (hLo : 7755 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (hPast : PassedVectorElement (outputStorePc stage box chunk) element s)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    7755 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 ∧
      PassedVectorElement (outputStorePc stage box chunk) element u := by
  rcases hPast with hs | ⟨hs, ht⟩
  · obtain ⟨hL, hH, hS, hP⟩ := afterStagingVectorStep stage box chunk hLo hHi hSub hs hw
    exact ⟨hL, hH, hS, .inl hP⟩
  · rcases hw with ⟨_, ht'⟩ | ⟨_, _, he⟩
    · exact (not_tau_of_stops (decodedStoreStops stage box chunk hs) ht').elim
    · exact afterVectorElement stage box chunk hs hSub ht.le he

private theorem elementCannotReappear {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (stage : Fin 2) (box : Fin 4) (chunk : Fin 8) {element : Nat}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 7755 ≤ s.pc) (hHi : s.pc ≤ 9205) (hSub : s.sub ≤ 3)
    (hPast : PassedVectorElement (outputStorePc stage box chunk) element s)
    {index : Nat} {a : Acc} {data : List Byte}
    (hGet : events[index]? = some ⟨outputStorePc stage box chunk, .wr a data⟩)
    (hLen : index + 1 < events.length) (hElem : a.elem = element) : False := by
  have hSite : outputStorePc stage box chunk < 9205 := by
    fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide
  induction hw generalizing index with
  | stop => simp at hGet
  | last => simp at hLen
  | @tau s u events visits ht hw ih =>
    have hEnd : s.pc < 9205 := by
      by_contra hn
      have hh := correctionReturnTail (by omega : s.pc = 9205) (.tau ht hw)
        (List.mem_of_getElem? hGet)
      change outputStorePc stage box chunk = 9205 at hh
      omega
    obtain ⟨hL, hH, hS, hP⟩ := afterElementStep stage box chunk hLo hEnd hSub hPast
      (.inl ⟨rfl, ht⟩)
    exact ih hL hH hS hP hGet hLen
  | @ev s u event events visits he hw ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
      subst event
      have hPc : s.pc = outputStorePc stage box chunk := (estep_source_pc he).symm
      have hn := hPast.resolve_left (by omega)
      obtain ⟨b, bs, hActual, hSub', _⟩ := vectorElementStep stage box chunk hPc he
      have hSame := (Kind.wr.inj (congrArg Event.kind hActual)).1
      subst b
      omega
    | succ index =>
      have hGet' : events[index]? = _ := hGet
      have hEnd : s.pc < 9205 := by
        by_contra hn
        have hh := correctionReturnTail (by omega : s.pc = 9205) (.ev he hw)
          (List.mem_cons_of_mem _ (List.mem_of_getElem? hGet'))
        change outputStorePc stage box chunk = 9205 at hh
        omega
      obtain ⟨hL, hH, hS, hP⟩ := afterElementStep stage box chunk hLo hEnd hSub hPast
        (.inr ⟨_, rfl, he⟩)
      exact ih hL hH hS hP hGet' (by simp at hLen; omega)

private theorem orderedVectorElementsDifferent {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (stage : Fin 2) (box : Fin 4) (chunk : Fin 8)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 7755 ≤ s.pc) (hHi : s.pc ≤ 9205) (hSub : s.sub ≤ 3)
    {j k : Nat} {a b : Acc} {data data' : List Byte}
    (hj : events[j]? = some ⟨outputStorePc stage box chunk, .wr a data⟩)
    (hk : events[k]? = some ⟨outputStorePc stage box chunk, .wr b data'⟩)
    (hOrd : j < k) (hLen : k + 1 < events.length) (hSame : a.elem = b.elem) : False := by
  have hSite : outputStorePc stage box chunk < 9205 := by
    fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide
  induction hw generalizing j k with
  | stop => simp at hj
  | last => simp at hLen
  | @tau s u events visits ht hw ih =>
    have hEnd : s.pc < 9205 := by
      by_contra hn
      have hh := correctionReturnTail (by omega : s.pc = 9205) (.tau ht hw)
        (List.mem_of_getElem? hj)
      change outputStorePc stage box chunk = 9205 at hh
      omega
    obtain ⟨hL, hH, hS⟩ := stagingRoleStepBounds stage hLo hEnd hSub (.inl ⟨rfl, ht⟩)
    exact ih hL hH hS hj hk hOrd hLen
  | @ev s u event events visits he hw ih =>
    cases k with
    | zero => omega
    | succ k =>
      have hk' : events[k]? = _ := hk
      have hLen' : k + 1 < events.length := by simp at hLen; omega
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst event
        have hPc : s.pc = outputStorePc stage box chunk := (estep_source_pc he).symm
        obtain ⟨a', bs, hActual, hElem, _⟩ := vectorElementStep stage box chunk hPc he
        have hEq := (Kind.wr.inj (congrArg Event.kind hActual)).1
        subst a'
        obtain ⟨hL, hH, hS, hPassed⟩ := afterVectorElement stage box chunk hPc hSub
          (hElem.le : a.elem ≤ s.sub) he
        exact elementCannotReappear stage box chunk hw hL hH hS hPassed hk' hLen' hSame.symm
      | succ j =>
        have hj' : events[j]? = _ := hj
        have hEnd : s.pc < 9205 := by
          by_contra hn
          have hh := correctionReturnTail (by omega : s.pc = 9205) (.ev he hw)
            (List.mem_cons_of_mem _ (List.mem_of_getElem? hj'))
          change outputStorePc stage box chunk = 9205 at hh
          omega
        obtain ⟨hL, hH, hS⟩ := stagingRoleStepBounds stage hLo hEnd hSub (.inr ⟨_, rfl, he⟩)
        exact ih hL hH hS hj' hk' (by omega) hLen'

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j k r : Nat} {stage : Fin 2}
    (hReady : CorrectionReady X (g,r) stage)
include hp hX hReady

private theorem sameStagingElementSiteUnique (box : Fin 4) (chunk : Fin 8) {a b : Acc}
    {data data' : List Byte} (hj : X.get (g,j) = some ⟨outputStorePc stage box chunk, .wr a data⟩)
    (hk : X.get (g,k) = some ⟨outputStorePc stage box chunk, .wr b data'⟩) (hElem : a.elem = b.elem)
    : j = k := by
  let ready : Event := ⟨outputFencePc stage + 2,
    .arrive (Epilogue.readyLoc l g stage) 0 1 true .cta⟩
  have hr : X.get (g,r) = some ready := hReady.decoded hp hX
  have hWarp := (CorrectionReady.ofActualArrival hp hX stage hr).2
  have hg : g < l.threads := Step.CtaBar.thread_lt_of_get hX hr
  have hReadyLate : 7754 < ready.pc := by
    change 7754 < outputFencePc stage + 2
    fin_cases stage <;> decide
  obtain ⟨s, o, _, hAt, _, _, _, _, _, _, hRun, _⟩ :=
    correctionEntryBeforeEvent hp hX (g := g) hg hWarp.1 hWarp.2 hr (.inl hReadyLate)
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hRun
  have hSite : 7754 < outputStorePc stage box chunk := by
    fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide
  have indexAfterEntry {w : Nat} {e : Event} (he : X.get (g,w) = some e)
      (hePc : e.pc = outputStorePc stage box chunk) : 9 ≤ w := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hw⟩ :=
      correctionEntryBeforeEvent hp hX (g := g) hg hWarp.1 hWarp.2 he (.inl (hePc.symm ▸ hSite))
    exact hw
  have hJ : 9 ≤ j := indexAfterEntry hj rfl
  have hK : 9 ≤ k := indexAfterEntry hk rfl
  have shifted {w : Nat} {e : Event} (hW : 9 ≤ w) (he : X.get (g,w) = some e) :
      ((X.tr g).drop 9)[w - 9]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hW]
    exact he
  obtain ⟨f, hf, _, hWrites⟩ := hReady.stagingBeforeFence hp hX
  have hBeforeJ := (hWrites (StageStagingWrite.ofEvent box chunk hj)).trans hf
  have hBeforeK := (hWrites (StageStagingWrite.ofEvent box chunk hk)).trans hf
  have hJLen : (j - 9) + 1 < ((X.tr g).drop 9).length := by
    have hOrd : j < r := hBeforeJ.2.1
    have hLen : r < (X.tr g).length := hBeforeJ.2.2
    rw [List.length_drop]
    omega
  have hKLen : (k - 9) + 1 < ((X.tr g).drop 9).length := by
    have hOrd : k < r := hBeforeK.2.1
    have hLen : r < (X.tr g).length := hBeforeK.2.2
    rw [List.length_drop]
    omega
  rcases lt_trichotomy j k with hLess | hEq | hGreater
  · exact (orderedVectorElementsDifferent stage box chunk hWalk hAt.1.ge
      (by rw [hAt.1]; decide) (by rw [hAt.2.1]; decide) (shifted hJ hj) (shifted hK hk)
      (by omega) hKLen hElem).elim
  · exact hEq
  · exact (orderedVectorElementsDifferent stage box chunk hWalk hAt.1.ge
      (by rw [hAt.1]; decide) (by rw [hAt.2.1]; decide) (shifted hK hk) (shifted hJ hj)
      (by omega) hJLen hElem.symm).elim

/-- With its observed publication, any two writes of one lane and stage covering the
same physical staging byte have the same trace index. -/
theorem sameStagingByteUnique {a b : Acc} {data data' : List Byte} {loc : Loc}
    (hj : StageStagingWrite X (g,j) stage a data) (hk : StageStagingWrite X (g,k) stage b data')
    (ha : a.Covers loc) (hb : b.Covers loc) : j = k := by
  obtain ⟨box, chunk, hJ⟩ := hj.decoded
  obtain ⟨box', chunk', hK⟩ := hk.decoded
  obtain ⟨elem, hA⟩ := stagingWriteElement hp hX stage box chunk hJ
  obtain ⟨elem', hB⟩ := stagingWriteElement hp hX stage box' chunk' hK
  let x := 4 * chunk.val + elem.val
  let x' := 4 * chunk'.val + elem'.val
  have hXBound : x < 32 := by dsimp only [x]; have := chunk.isLt; have := elem.isLt; omega
  have hXBound' : x' < 32 := by dsimp only [x']; have := chunk'.isLt; have := elem'.isLt; omega
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hFirst : (outputElementAccess l g stage box x (rowOf l g)).Covers loc := hA ▸ ha
  have hOther : (outputElementAccess l g stage box' x' (rowOf l g)).Covers loc := hB ▸ hb
  obtain ⟨_, _, hBox, _, hCol⟩ :=
    Output.sameNormalizedElementOfCover hXBound hXBound' hRow hRow hFirst hOther
  have hElem : a.elem = b.elem := by
    rw [hA, hB]
    change x % 4 = x' % 4
    rw [hCol]
  have hChunk : chunk = chunk' := by
    apply Fin.ext
    dsimp only [x, x'] at hCol
    have := elem.isLt
    have := elem'.isLt
    omega
  subst box' chunk'
  exact sameStagingElementSiteUnique hp hX hReady box chunk hJ hK hElem

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
