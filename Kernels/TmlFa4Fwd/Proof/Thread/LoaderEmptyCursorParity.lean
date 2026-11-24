-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyPrimingTrace
import Kernels.TmlFa4Fwd.Proof.CtaMemoryOrder
import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress
public import Lemmas.Flow.Polls

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader
  (kvUseStage kvUseStage_val kvEmptyPhase emptySlot emptySlot_address recurringEmptyWait
    recurringEmptyWaitCode reuseArrival loaderFixedWaitOffset fixedLoaderWaitOffset
    laterPublicationIsRecurring)

noncomputable section

open scoped Classical

private def usesBefore (slot : Fin 3) (use : Nat) : Nat :=
  (use + (2 - slot.val)) / 3

private theorem usesBeforeStep (slot : Fin 3) (use : Nat) :
    usesBefore slot (use + 1) = usesBefore slot use + if kvUseStage use = slot then 1 else 0 := by
  have hSlot : kvUseStage use = slot ↔ use % 3 = slot.val :=
    Fin.ext_iff.trans (by rw [kvUseStage_val])
  have hLt := slot.isLt
  unfold usesBefore
  by_cases hs : kvUseStage use = slot
  · have := hSlot.mp hs
    rw [ite_eq_left hs]
    omega
  · have hn : use % 3 ≠ slot.val := fun h => hs (hSlot.mpr h)
    rw [ite_eq_right hs]
    omega

private theorem parityOfUse {use : Nat} {slot : Fin 3} (h : kvUseStage use = slot) :
    (if kvEmptyPhase use then 1 else 0) = (usesBefore slot use + 1) % 2 := by
  have hs : use % 3 = slot.val := by rw [← h, kvUseStage_val]
  have hLt := slot.isLt
  unfold usesBefore kvEmptyPhase Mma.kvParity
  have hDiv : (use + (2 - slot.val)) / 3 = use / 3 := by omega
  rw [hDiv]
  simp only [beq_iff_eq]
  split <;> omega

/-- A successful recurring poll on the chosen slot. -/
def recurringPollOn (l : Launch) (g : Nat) (slot : Fin 3) (e : Event) : Bool :=
  if recurringEmptyEvent e then okPoll (emptyObject l g slot) e else false

private theorem emptyObjectInj (l : Launch) (g : Nat) :
    Function.Injective (emptyObject l g) := by
  intro i j he
  by_contra hNe
  apply Prologue.initObject_ne (i := emptySlot i) (j := emptySlot j) _ he
  intro hs
  apply hNe
  have hVal := congrArg Fin.val hs
  change 7 + i.val = 7 + j.val at hVal
  exact Fin.ext (by omega)

private theorem markedPoll {l : Launch} {g use : Nat} {slot : Fin 3} {site : Fin 4} :
    recurringPollOn l g slot (cursorPoll l g use site true) = decide (kvUseStage use = slot) := by
  unfold recurringPollOn
  rw [ite_eq_left (show recurringEmptyEvent (cursorPoll l g use site true) from ⟨site, _, _, rfl⟩)]
  rw [okPoll_wait (show cursorPoll l g use site true = _ from rfl)]
  simp only [Bool.true_and]
  congr 1
  exact propext ⟨fun h => emptyObjectInj l g h, congrArg (emptyObject l g)⟩

private theorem retryUnmarked {l : Launch} {g use : Nat} {slot : Fin 3} {site : Fin 4} :
    recurringPollOn l g slot (cursorPoll l g use site false) = false := by
  unfold recurringPollOn
  apply ite_eq_right
  rintro ⟨i, loc, q, h⟩
  have hKind := congrArg Event.kind h
  cases hKind

private theorem publicationUnmarked {l : Launch} {g use : Nat} {slot : Fin 3} {site : Fin 4} :
    recurringPollOn l g slot (cursorArrival l g use site) = false := by
  unfold recurringPollOn
  apply ite_eq_right
  rintro ⟨i, loc, q, h⟩
  have hKind := congrArg Event.kind h
  cases hKind

private theorem quietUnmarked {l : Launch} {g : Nat} {slot : Fin 3} {e : Event}
    (h : ¬ recurringEmptyEvent e) : recurringPollOn l g slot e = false := by
  exact ite_eq_right h

private def AlternatesFrom (mark : Event → Bool) (base : Nat) (es : List Event) : Prop :=
  ∀ i pc loc q acq scope,
    es[i]? = some ⟨pc, .wait loc q true acq scope⟩ →
    mark ⟨pc, .wait loc q true acq scope⟩ = true →
    q % 2 = (base + (es.take i).countP mark + 1) % 2

private theorem altQuiet {mark : Event → Bool} {base : Nat} {es : List Event}
    (h : ∀ e ∈ es, mark e = false) : AlternatesFrom mark base es := by
  intro i pc loc q acq scope he hmark
  rw [h _ (List.mem_of_getElem? he)] at hmark
  cases hmark

private theorem altAppend {mark : Event → Bool} {base : Nat} {left right : List Event}
    (hl : AlternatesFrom mark base left)
    (hr : AlternatesFrom mark (base + left.countP mark) right) :
    AlternatesFrom mark base (left ++ right) := by
  intro i pc loc q acq scope he hmark
  by_cases hi : i < left.length
  · rw [List.getElem?_append_left hi] at he
    rw [List.take_append_of_le_length hi.le]
    exact hl i pc loc q acq scope he hmark
  · rw [List.getElem?_append_right (by omega)] at he
    rw [List.take_append, List.take_of_length_le (by omega), List.countP_append]
    simpa only [Nat.add_assoc] using hr (i - left.length) pc loc q acq scope he hmark

private theorem altSingle {mark : Event → Bool} {base : Nat} {e : Event}
    (h : ∀ pc loc q acq scope, e = ⟨pc, .wait loc q true acq scope⟩ →
      mark e = true → q % 2 = (base + 1) % 2) : AlternatesFrom mark base [e] := by
  intro i pc loc q acq scope he hm
  cases i with
  | zero =>
    obtain rfl := Option.some.inj he
    simpa using h pc loc q acq scope rfl hm
  | succ i => simp at he

private theorem RecurringCursorTrace.markedAlternates {l : Launch} {g use : Nat} {es : List Event}
    (h : RecurringCursorTrace l g use es) (slot : Fin 3) :
    AlternatesFrom (recurringPollOn l g slot) (usesBefore slot use) es := by
  induction h with
  | nil => exact altQuiet (by simp)
  | @gap use pre tail quiet _ ih =>
    have hFalse := fun e he => quietUnmarked (l := l) (g := g) (slot := slot) (quiet e he).2
    have hCount : pre.countP (recurringPollOn l g slot) = 0 :=
      List.countP_eq_zero.mpr (fun e he => by simp [hFalse e he])
    apply altAppend (altQuiet hFalse)
    rwa [hCount, Nat.add_zero]
  | @packet use n site mid tail _ quiet _ ih =>
    let mark := recurringPollOn l g slot
    let failed := List.replicate n (cursorPoll l g use site false)
    let poll := cursorPoll l g use site true
    let arrived := cursorArrival l g use site
    have hf : ∀ e ∈ failed, mark e = false := by
      intro e he
      have h := (List.mem_replicate.mp he).2
      subst e
      exact retryUnmarked
    have hFailed : failed.countP mark = 0 := List.countP_eq_zero.mpr fun e he => by simp [hf e he]
    have hMid : ∀ e ∈ mid ++ [arrived], mark e = false := by
      intro e he
      rcases List.mem_append.mp he with hm | hm
      · exact quietUnmarked (quiet e hm).2
      · obtain rfl := List.mem_singleton.mp hm
        exact publicationUnmarked
    have hMidCount : (mid ++ [arrived]).countP mark = 0 :=
      List.countP_eq_zero.mpr fun e he => by simp [hMid e he]
    have hResult : AlternatesFrom mark (usesBefore slot use)
        (failed ++ ([poll] ++ ((mid ++ [arrived]) ++ tail))) := by
      apply altAppend (altQuiet hf)
      rw [hFailed, Nat.add_zero]
      have hSingle : AlternatesFrom mark (usesBefore slot use) [poll] := by
        apply altSingle
        intro pc loc q acq scope he hm
        have hs : kvUseStage use = slot := of_decide_eq_true (markedPoll.symm.trans hm)
        have hKind := congrArg Event.kind he
        cases hKind
        rw [parityOfUse hs, Nat.mod_mod]
      apply altAppend hSingle
      apply altAppend (altQuiet hMid)
      rw [hMidCount, Nat.add_zero, List.countP_singleton]
      simp only [mark, poll, markedPoll, decide_eq_true_eq]
      rw [← usesBeforeStep]
      exact ih
    simpa only [failed, poll, arrived, mark, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using hResult

/-- In the actual suffix starting at the cursor seed, every recurring successful
poll uses the parity of its earlier same-slot recurring polls plus its priming offset. -/
theorem RecurringCursorTrace.parityAt {l : Launch} {g : Nat} {es : List Event}
    (h : RecurringCursorTrace l g 2 es) (slot : Fin 3)
    {i pc q : Nat} {acq : Bool} {scope : MbarScope}
    (he : es[i]? = some ⟨pc, .wait (emptyObject l g slot) q true acq scope⟩)
    (hMarker : recurringEmptyEvent ⟨pc, .wait (emptyObject l g slot) q true acq scope⟩) :
    q % 2 = ((es.take i).countP (recurringPollOn l g slot) + (if slot = 2 then 1 else 2)) % 2 := by
  have hMarked : recurringPollOn l g slot
      ⟨pc, .wait (emptyObject l g slot) q true acq scope⟩ = true := by
    simp [recurringPollOn, hMarker, okPoll_wait rfl]
  have hParity := h.markedAlternates slot i pc (emptyObject l g slot) q acq scope he hMarked
  fin_cases slot <;> simp [usesBefore] at hParity ⊢ <;> omega

private theorem actualMarkedWait {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g n pc q : Nat} {acq : Bool} {scope : MbarScope} {slot : Fin 3}
    (he : X.get (g, n) = some ⟨pc, .wait (emptyObject l g slot) q true acq scope⟩)
    (hRange : pc < 1744) :
    pc = 517 ∨ pc = 782 ∨ recurringEmptyEvent ⟨pc, .wait (emptyObject l g slot) q true acq scope⟩ :=
  by
  let fixed : List Nat := [679, 704, 730, 756, 1146, 1175, 1361]
  have hAudit : Flow.mbarWait.toList.all
      (fun pc => decide (pc < 1744 → pc = 517 ∨ pc = 782 ∨
        pc ∈ [960, 1206, 1430, 1611] ∨ pc ∈ fixed)) = true := by
    decide
  have hSite :=
    (of_decide_eq_true (List.all_eq_true.mp hAudit pc (actualMbarPollSite hX he))) hRange
  rcases hSite with h | h | hs | hs
  · exact .inl h
  · exact .inr (.inl h)
  · have hMap : [960, 1206, 1430, 1611] =
        List.ofFn fun site : Fin 4 => (recurringEmptyWait site).pc := rfl
    rw [hMap] at hs
    obtain ⟨site, rfl⟩ := List.mem_ofFn.mp hs
    have hScope := actualPollScope hX he
    subst scope
    have hAcquire : acq = true := by
      rcases get_source hX he with ⟨_, hFalse⟩ | ⟨_, ins, _, _, hc, hf⟩
      · cases hFalse
      obtain ⟨_, _, _, _, _, hop, _⟩ := fires_wait_flags hf rfl
      have hSame := Option.some.inj (hc.symm.trans (recurringEmptyWaitCode site).1)
      rw [hSame] at hop
      cases hop
      rfl
    subst acq
    exact .inr (.inr ⟨site, _, q, rfl⟩)
  · have hFixed : pc ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] := by
      simp [fixed] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hAddr := congrArg Loc.addr (loaderFixedWaitOffset hp hX he hFixed)
    rw [emptyObject, emptySlot_address] at hAddr
    simp only at hAddr
    have hOff : fixedLoaderWaitOffset pc < 56 ∨ 72 < fixedLoaderWaitOffset pc := by
      simp [fixed] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hSlot := slot.isLt
    omega

private theorem successfulEmptySource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    {slot : Fin 3} {e : Event} (he : e ∈ X.tr g) (hBelow : e.pc < 1744)
    (hOk : okPoll (emptyObject l g slot) e = true) :
    e.pc = 517 ∨ e.pc = 782 ∨ recurringEmptyEvent e := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp he
  change X.get (g, n) = some e at hn
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [okPoll, sourceWaitSuccess, Bool.false_eq_true] at hOk
  case wait loc q ok acq scope =>
    cases ok <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at hOk
    subst loc
    exact actualMarkedWait hp hX hn hBelow

private theorem primingCount {l : Launch} {g : Nat} {slot : Fin 3} {stage : Fin 2} {n : Nat} :
    let mark := okPoll (emptyObject l g slot)
    let stage' : Fin 3 := ⟨stage.val, by have := stage.isLt; omega⟩
    (List.replicate n (primingCursorPoll l g stage false) ++
      [primingCursorPoll l g stage true]).countP mark = if stage' = slot then 1 else 0 := by
  dsimp only
  simp only [List.countP_append, List.countP_replicate, List.countP_singleton,
    okPoll_wait (show primingCursorPoll l g stage false = _ from rfl),
    okPoll_wait (show primingCursorPoll l g stage true = _ from rfl),
    Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, decide_eq_true_eq]
  have h : emptyObject l g ⟨stage.val, by have := stage.isLt; omega⟩ = emptyObject l g slot ↔
      (⟨stage.val, by have := stage.isLt; omega⟩ : Fin 3) = slot :=
    ⟨fun h => emptyObjectInj l g h, congrArg _⟩
  by_cases hs : (⟨stage.val, by have := stage.isLt; omega⟩ : Fin 3) = slot <;>
    simp [hs, h]

private theorem primingAlternates {l : Launch} {g base : Nat} {slot : Fin 3}
    (stage : Fin 2) (n : Nat)
    (hBase : (⟨stage.val, by have := stage.isLt; omega⟩ : Fin 3) = slot → base = 0) :
    AlternatesFrom (okPoll (emptyObject l g slot)) base
      (List.replicate n (primingCursorPoll l g stage false) ++
        [primingCursorPoll l g stage true]) := by
  let mark := okPoll (emptyObject l g slot)
  have hf : ∀ e ∈ List.replicate n (primingCursorPoll l g stage false), mark e = false := by
    intro e he
    have he' := (List.mem_replicate.mp he).2
    subst e
    change okPoll (emptyObject l g slot) (primingCursorPoll l g stage false) = false
    rw [okPoll_wait (show primingCursorPoll l g stage false = _ from rfl)]
    rfl
  have hZero : (List.replicate n (primingCursorPoll l g stage false)).countP mark = 0 :=
    List.countP_eq_zero.mpr fun e he => by simp [hf e he]
  apply altAppend (altQuiet hf)
  rw [hZero, Nat.add_zero]
  apply altSingle
  intro pc loc q acq scope he hOk
  have hMark : mark (primingCursorPoll l g stage true) =
      decide (emptyObject l g ⟨stage.val, by have := stage.isLt; omega⟩ = emptyObject l g slot) :=
    okPoll_wait (show primingCursorPoll l g stage true = _ from rfl)
  have hSlot := emptyObjectInj l g (of_decide_eq_true (hMark.symm.trans hOk))
  have hKind := congrArg Event.kind he
  obtain ⟨_, rfl, _, _, _⟩ := Kind.wait.inj hKind
  rw [hBase hSlot]

private theorem cursorAlternatesForEmptyObject {l : Launch} {g : Nat} {es : List Event}
    (h : RecurringCursorTrace l g 2 es) (slot : Fin 3)
    (hMark : ∀ e ∈ es, okPoll (emptyObject l g slot) e = true → recurringEmptyEvent e) :
    AlternatesFrom (okPoll (emptyObject l g slot)) (if slot = 2 then 0 else 1) es := by
  intro i pc loc q acq scope he hOk
  let mark := okPoll (emptyObject l g slot)
  have hLoc : loc = emptyObject l g slot := by
    have hEq := okPoll_wait (m := emptyObject l g slot)
      (show (⟨pc, .wait loc q true acq scope⟩ : Event) = _ from rfl)
    exact of_decide_eq_true (hEq.symm.trans hOk)
  subst loc
  have hEmpty := hMark _ (List.mem_of_getElem? he) hOk
  have hParity := h.parityAt slot he hEmpty
  have hCount : (es.take i).countP (recurringPollOn l g slot) = (es.take i).countP mark := by
    apply List.countP_congr
    intro e hm
    cases hOk' : mark e with
    | false => simp [recurringPollOn, show okPoll (emptyObject l g slot) e = false from hOk']
    | true =>
      have := hMark e (List.mem_of_mem_take hm) hOk'
      simp [recurringPollOn, this, show okPoll (emptyObject l g slot) e = true from hOk']
  rw [hCount] at hParity
  change q % 2 = ((if slot = 2 then 0 else 1) + (es.take i).countP mark + 1) % 2
  by_cases hs : slot = 2 <;> simp [hs] at hParity ⊢ <;> omega


/-- All actual successful empty polls through a recurring loader publication
alternate per physical slot from parity one. -/
theorem actualRecurringEmptyAlternation {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (site : Fin 4) {g index : Nat} {target : Loc} (slot : Fin 3)
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive target true⟩) :
    AlternatesEmptyThrough l X g index slot 1 := by
  obtain ⟨pre0, pre1, pre2, rest, nK, nV, hEs, hEarly, hPre0, hPre1, hPre2,
      hRange, _, _, _, _, hCursor⟩ :=
    actualLoaderCursorThrough hp hX site he
  let early := (X.tr g).take 5
  let prefixEvents := (X.tr g).take (index + 1)
  let k := List.replicate nK (primingCursorPoll l g 0 false) ++ [primingCursorPoll l g 0 true]
  let v := List.replicate nV (primingCursorPoll l g 1 false) ++ [primingCursorPoll l g 1 true]
  let mark := okPoll (emptyObject l g slot)
  have hSplit : prefixEvents = early ++ (pre0 ++ (k ++ (pre1 ++ (v ++ (pre2 ++ rest))))) := by
    simpa only [prefixEvents, early, k, v, List.append_assoc] using hEs
  have hRaw (e : Event) (hm : e ∈ prefixEvents) : e ∈ X.tr g := List.mem_of_mem_take hm
  have hQuiet {xs : List Event} (hIn : ∀ e ∈ xs, e ∈ prefixEvents)
      (hLow : ∀ e ∈ xs, e.pc ≠ 517 ∧ e.pc ≠ 782 ∧ e.pc < 909) :
      ∀ e ∈ xs, mark e = false := by
    intro e hm
    obtain ⟨hK, hV, hPc⟩ := hLow e hm
    cases hs : mark e
    · rfl
    exfalso
    rcases successfulEmptySource hp hX (slot := slot) (hRaw e (hIn e hm))
      (by omega) hs with h | h | h
    · exact hK h
    · exact hV h
    · obtain ⟨i, loc, parity, rfl⟩ := h
      have hRange : 909 ≤ (recurringEmptyWait i).pc := by fin_cases i <;> decide
      change (recurringEmptyWait i).pc < 909 at hPc
      omega
  have hEarly' := hQuiet (xs := early) (fun e hm => by rw [hSplit]; simp [hm])
    (fun e hm => by have := hEarly e hm; omega)
  have h0 := hQuiet (xs := pre0) (fun e hm => by rw [hSplit]; simp [hm])
    (fun e hm => by have := hPre0 e hm; omega)
  have h1 := hQuiet (xs := pre1) (fun e hm => by rw [hSplit]; simp [hm])
    (fun e hm => by have := hPre1 e hm; omega)
  have h2 := hQuiet (xs := pre2) (fun e hm => by rw [hSplit]; simp [hm])
    (fun e hm => by have := hPre2 e hm; omega)
  have hRest : AlternatesFrom mark (if slot = 2 then 0 else 1) rest := by
    apply cursorAlternatesForEmptyObject hCursor slot
    intro e hm hOk
    have hRaw' := hRaw e (by rw [hSplit]; simp [hm])
    have hBounds := hRange e hm
    rcases successfulEmptySource hp hX (slot := slot) hRaw' hBounds.2 hOk with h | h | h
    · omega
    · omega
    · exact h
  have hK : k.countP mark = if (0 : Fin 3) = slot then 1 else 0 :=
    primingCount (stage := 0)
  have hV : v.countP mark = if (1 : Fin 3) = slot then 1 else 0 :=
    primingCount (stage := 1)
  have hBase : k.countP mark + v.countP mark = if slot = 2 then 0 else 1 := by
    rw [hK, hV]
    fin_cases slot <;> rfl
  have count0 {xs : List Event} (h : ∀ e ∈ xs, mark e = false) : xs.countP mark = 0 :=
    List.countP_eq_zero.mpr fun e hm => by simp [h e hm]
  have hAlt : AlternatesFrom mark 0 prefixEvents := by
    rw [hSplit]
    apply altAppend (altQuiet hEarly')
    rw [count0 hEarly', Nat.add_zero]
    apply altAppend (altQuiet h0)
    rw [count0 h0, Nat.add_zero]
    apply altAppend (primingAlternates (slot := slot) 0 nK (by simp))
    rw [Nat.zero_add]
    apply altAppend (altQuiet h1)
    rw [count0 h1, Nat.add_zero]
    apply altAppend (primingAlternates (slot := slot) 1 nV ?_)
    · apply altAppend (altQuiet h2)
      rw [count0 h2, Nat.add_zero, hBase]
      exact hRest
    · intro hSlot
      have hs : (1 : Fin 3) = slot := hSlot
      rw [hK, ← hs]
      decide
  intro j e q acq scope hj hGet hKind
  obtain ⟨pc, kind⟩ := e
  dsimp only at hKind
  subst kind
  have hIndex : prefixEvents[j]? = some ⟨pc, .wait (emptyObject l g slot) q true acq scope⟩ := by
    rw [List.getElem?_take_of_lt (show j < index + 1 by omega)]
    exact hGet
  have hOk : mark ⟨pc, .wait (emptyObject l g slot) q true acq scope⟩ = true := by
    simp [mark, okPoll_wait rfl]
  have h := hAlt j pc (emptyObject l g slot) q acq scope hIndex hOk
  simpa only [prefixEvents, mark, List.take_take, Nat.min_eq_left (show j ≤ index + 1 by omega),
    Nat.zero_add, emptyOrdinal, okPolls] using h


/-- Every actual publication with positive local generation has an alternating
empty-poll prefix with initial parity one. -/
theorem actualPositivePublicationEmptyAlternation {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner : Nat} {issue : EvId} {slot : Fin 3}
    (hPub : X.AsyncArrive issue (readyObject l owner slot) true)
    (hPositive : 0 < (atPrefix l X issue.1 issue.2).published.countP
      (fun pub => pub.slot == slot)) :
    AlternatesEmptyThrough l X issue.1 issue.2 slot 1 := by
  obtain ⟨i, hi, hPrior, _⟩ := earlierPublication hp hX hPub hPositive
  obtain ⟨site, he⟩ := laterPublicationIsRecurring hp hX hi hPrior hPub
  exact actualRecurringEmptyAlternation hp hX site slot he

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
