-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyPrimingTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFacts
import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress
import Kernels.TmlFa4Fwd.Proof.LoaderReusePriming
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyPublicationGroup
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader
  (actualAsyncArrival copyCommitPc kvUseStage kvUseStage_val recurringPacketSite reuseArrival
    readyTarget readyUseTarget readyOrdinalOfUse loaderStartupAsyncAddress primingPacketSite)

noncomputable section
open scoped Classical

private def recurringMark (e : Event) : Bool := decide (recurringPublicationEvent e)

private theorem quietCount {es : List Event} (h : ∀ e ∈ es, ¬ recurringPublicationEvent e) :
    es.countP recurringMark = 0 :=
  List.countP_eq_zero.mpr fun e hm => by simp [recurringMark, h e hm]

private theorem recurringPc {e : Event} (h : recurringPublicationEvent e) : 909 ≤ e.pc := by
  obtain ⟨site, loc, rfl⟩ := h
  change 909 ≤ reuseArrival site
  fin_cases site <;> decide

private theorem lastOfAppendRight {α : Type} {xs ys : List α} {e : α}
    (h : (xs ++ ys).getLast? = some e) (hne : ys ≠ []) : ys.getLast? = some e := by
  rw [List.getLast?_append] at h
  cases hs : ys.getLast? with
  | none => exact (hne (List.getLast?_eq_none_iff.mp hs)).elim
  | some => simpa [hs] using h

private theorem RecurringCursorTrace.lastUse {l : Launch} {g use : Nat} {es : List Event}
    (h : RecurringCursorTrace l g use es) {last : Event}
    (hLast : es.getLast? = some last) (hPublication : recurringPublicationEvent last) :
    ∃ site : Fin 4, let current := use + es.countP recurringMark - 1
      last = cursorArrival l g current site ∧ site.val % 2 = current % 2 := by
  induction h with
  | nil => simp at hLast
  | @gap use pre tail hQuiet hNext ih =>
    have hNonempty : tail ≠ [] := by
      intro he
      simp only [he, List.append_nil] at hLast
      exact (hQuiet last (List.mem_of_getLast? hLast)).1 hPublication
    simpa only [List.countP_append, quietCount (fun e hm => (hQuiet e hm).1), Nat.zero_add]
      using ih (lastOfAppendRight hLast hNonempty)
  | @packet use n site mid tail hPlane hQuiet hNext ih =>
    let failed := List.replicate n (cursorPoll l g use site false)
    let before := cursorPoll l g use site true :: mid
    let arrived := cursorArrival l g use site
    have hNoPoll (ok : Bool) : ¬ recurringPublicationEvent (cursorPoll l g use site ok) := by
      rintro ⟨_, _, hEvent⟩
      have hKind := congrArg Event.kind hEvent
      cases hKind
    have hf : failed.countP recurringMark = 0 := quietCount
      (fun e he => (List.mem_replicate.mp he).2.symm ▸ hNoPoll false)
    have hb : before.countP recurringMark = 0 := quietCount (fun e he => by
      rcases List.mem_cons.mp he with rfl | hm
      · exact hNoPoll true
      · exact (hQuiet e hm).1)
    have ha : recurringMark arrived = true := by
      exact decide_eq_true ⟨site, _, rfl⟩
    have hCount : (failed ++ (before ++ arrived :: tail)).countP recurringMark =
        tail.countP recurringMark + 1 := by
      rw [List.countP_append, hf, Nat.zero_add, List.countP_append, hb, Nat.zero_add,
        List.countP_cons, ha, ite_eq_left rfl]
    have hLast' : (failed ++ (before ++ arrived :: tail)).getLast? = some last := by
      simpa only [failed, before, arrived, List.cons_append, List.append_assoc] using hLast
    have hExpr : (List.replicate n (cursorPoll l g use site false) ++
        cursorPoll l g use site true :: mid ++ cursorArrival l g use site :: tail) =
          failed ++ (before ++ arrived :: tail) := by
      simp only [failed, before, arrived, List.cons_append, List.append_assoc]
    rw [hExpr, hCount]
    by_cases hempty : tail = []
    · subst tail
      have hEqual : last = arrived := by
        simpa [List.getLast?_append] using hLast'.symm
      simpa using (show ∃ j : Fin 4,
        last = cursorArrival l g use j ∧ j.val % 2 = use % 2 from ⟨site, hEqual, hPlane⟩)
    · have hPrefix : (failed ++ (before ++ arrived :: tail)) = (failed ++ before ++ [arrived]) ++
          tail := by simp [List.append_assoc]
      rw [hPrefix] at hLast'
      obtain ⟨j, hEqual, hParity⟩ := ih (lastOfAppendRight hLast' hempty)
      exact ⟨j, (show use + 1 + tail.countP recurringMark - 1 =
        use + (tail.countP recurringMark + 1) - 1 by omega) ▸ hEqual,
        by omega⟩

private def recurring (pub : Publication) : Bool := decide (pub.packet.period ≠ .priming)

private theorem classifiedPlaneOfArrival (site : Fin 6) {l : Launch} {g : Nat} {loc : Loc}
    {pub : Publication}
    (hObs : observe l g ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ = .publish pub) :
    pub.packet = DecodedObservation.packetOfSite site := by
  have hPacket : DecodedObservation.observePacket (copyCommitPc site + 1) true =
      some (DecodedObservation.packetOfSite site) := by fin_cases site <;> decide
  simp only [observe, hPacket] at hObs
  split at hObs <;> cases hObs
  exact (Option.some.inj (by assumption)).symm

private theorem stepRecurringCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e) (d : D) :
    (advance l g d e).published.countP recurring =
      d.published.countP recurring + if recurringMark e then 1 else 0 := by
  have noArrival (h : ∀ loc, e.kind ≠ .asyncArrive loc true) : recurringMark e = false := by
    apply decide_eq_false
    rintro ⟨_, loc, hEvent⟩
    exact h loc (congrArg Event.kind hEvent)
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try (solve | rw [noArrival (by intro loc h; cases h)]; simp [advance, observe])
  case asyncCommit =>
    rw [noArrival (by intro loc h; cases h)]
    cases h : DecodedObservation.observePacket pc false <;> simp [advance, observe, h]
  case asyncArrive loc noinc =>
    obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := actualAsyncArrival hX he
    obtain ⟨pub, _, _, hObs⟩ := readyObservation hp hX he rfl
    rw [advancePublication hObs, List.countP_cons]
    have hPacket := classifiedPlaneOfArrival site hObs
    have hPeriod : pub.packet.period ≠ .priming ↔ 909 ≤ copyCommitPc site + 1 := by
      rw [hPacket]
      fin_cases site <;> decide
    have hMarked : recurringPublicationEvent ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ ↔
        909 ≤ copyCommitPc site + 1 := by
      refine ⟨recurringPc, ?_⟩
      intro hPc
      fin_cases site
      · have : ¬909 ≤ copyCommitPc 0 + 1 := by decide
        exact (this hPc).elim
      · have : ¬909 ≤ copyCommitPc 1 + 1 := by decide
        exact (this hPc).elim
      · exact ⟨0, loc, rfl⟩
      · exact ⟨1, loc, rfl⟩
      · exact ⟨2, loc, rfl⟩
      · exact ⟨3, loc, rfl⟩
    have hBit : recurringMark ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ = recurring pub := by
      apply Bool.eq_iff_iff.mpr
      simpa only [recurringMark, recurring, decide_eq_true_eq] using hMarked.trans hPeriod.symm
    rw [hBit]
  case tensorIssue =>
    rw [noArrival (by intro loc h; cases h)]
    cases h : DecodedObservation.observeInput pc with
    | none => simp [advance, observe, *]
    | some plane => cases plane <;> simp [advance, observe, *]
  case wait loc parity ok acq scope =>
    rw [noArrival (by intro loc h; cases h)]
    cases ok <;> cases acq <;> cases scope <;> try (solve | simp [advance, observe])
    cases h : DecodedObservation.locateSlot l g loc false <;> simp [advance, observe, h]

private theorem recurringPrefixCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (g n : Nat) (hn : n ≤ (X.tr g).length) :
    (atPrefix l X g n).published.countP recurring = ((X.tr g).take n).countP recurringMark := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hLt : n < (X.tr g).length := by omega
    let e := (X.tr g)[n]
    have he : X.get (g, n) = some e := List.getElem?_eq_getElem hLt
    rw [prefixStep he, stepRecurringCount hp hX he, ih (by omega), List.take_add_one]
    change ((X.tr g).take n).countP recurringMark +
      (if recurringMark e then 1 else 0) =
        ((X.tr g).take n ++ ((X.tr g)[n]?).toList).countP recurringMark
    rw [show (X.tr g)[n]? = some e from he]
    simp [List.countP_append]

private theorem actualReadyTargetSource {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} {e : Event} (he : e ∈ X.tr g)
    {target : Loc} (hTarget : readyTarget e = some target) :
    ∃ (index : Nat) (site : Fin 6), e.pc = copyCommitPc site + 1 ∧
      X.get (g, index) = some ⟨e.pc, .asyncArrive target true⟩ ∧
      e = ⟨e.pc, .asyncArrive target true⟩ := by
  obtain ⟨index, hGet⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [readyTarget] at hTarget
  case asyncArrive loc noinc =>
    cases noinc
    · cases hTarget
    · change some loc = some target at hTarget
      obtain rfl := Option.some.inj hTarget
      have he : X.get (g, index) = some ⟨pc, .asyncArrive loc true⟩ := hGet
      obtain ⟨⟨site, hPc⟩, _, _, _⟩ := actualAsyncArrival hX he
      exact ⟨index, site, hPc, he, rfl⟩

private theorem withoutReadyTargets {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} {es : List Event}
    (hPrefix : ∀ e ∈ es, e ∈ X.tr g) (hEarly : ∀ e ∈ es, e.pc < 674) :
    es.filterMap readyTarget = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  cases h : readyTarget e with
  | none => rfl
  | some target =>
    obtain ⟨_, site, hPc, _⟩ := actualReadyTargetSource hX (hPrefix e he) h
    have hLo : 674 ≤ copyCommitPc site + 1 := by fin_cases site <;> decide
    have := hEarly e he
    omega

private theorem primingReadyTargets {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {es : List Event} (stage : Fin 2)
    (hPrefix : ∀ e ∈ es, e ∈ X.tr g)
    (hOnly : ∀ e ∈ es, ∀ site : Fin 6, e.pc = copyCommitPc site + 1 →
      site = primingPacketSite stage)
    (hSeen : ∃ target, (⟨copyCommitPc (primingPacketSite stage) + 1,
      .asyncArrive target true⟩ : Event) ∈ es)
    (hCount : es.countP (fun a => a.pc == copyCommitPc (primingPacketSite stage) + 1) = 1) :
    es.filterMap readyTarget = [readyUseTarget l (g / l.block) stage] := by
  let target := readyUseTarget l (g / l.block) stage
  have hMatch {e : Event} {loc : Loc} (hm : e ∈ es) (he : readyTarget e = some loc) :
      e.pc = copyCommitPc (primingPacketSite stage) + 1 ∧ loc = target := by
    obtain ⟨j, site, hPc, hEvent, _⟩ := actualReadyTargetSource hX (hPrefix e hm) he
    obtain rfl := hOnly e hm site hPc
    have hSite : e.pc ∈ [674, 904] := by rw [hPc]; fin_cases stage <;> decide
    have hAddr := loaderStartupAsyncAddress hp hX hEvent hSite
    rw [hPc] at hAddr
    exact ⟨hPc, hAddr.trans (by fin_cases stage <;> rfl)⟩
  have hl : (es.filterMap readyTarget).length ≤ 1 := by
    rw [List.length_filterMap_eq_countP, ← hCount]
    apply List.countP_mono_left
    intro e he hSome
    obtain ⟨loc, hl⟩ := Option.isSome_iff_exists.mp hSome
    exact beq_iff_eq.mpr (hMatch he hl).1
  have hm : target ∈ es.filterMap readyTarget := by
    obtain ⟨t, ht⟩ := hSeen
    have h := (hMatch ht (show readyTarget ⟨_, .asyncArrive t true⟩ = some t by rfl)).2
    exact List.mem_filterMap.mpr ⟨_, ht, congrArg some h⟩
  cases hList : es.filterMap readyTarget with
  | nil => simp [hList] at hm
  | cons x xs =>
    have hNil : xs = [] := by
      rw [hList, List.length_cons] at hl
      exact List.length_eq_zero_iff.mp (by omega)
    subst xs
    have hx : target = x := by simpa [hList] using hm
    exact congrArg (fun a : Loc => [a]) hx.symm

private theorem RecurringCursorTrace.targets {l : Launch} {g use : Nat} {es : List Event}
    (h : RecurringCursorTrace l g use es)
    (hKnown : ∀ e ∈ es, (readyTarget e).isSome → recurringPublicationEvent e) :
    es.filterMap readyTarget =
      (List.range' use (es.countP recurringMark)).map (readyUseTarget l (g / l.block)) := by
  have noTargets {xs : List Event} (hNone : ∀ e ∈ xs, ¬ recurringPublicationEvent e)
      (hKnown : ∀ e ∈ xs, (readyTarget e).isSome → recurringPublicationEvent e) :
      xs.filterMap readyTarget = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    cases h : readyTarget e
    · rfl
    · exact (hNone e he (hKnown e he (by simp [h]))).elim
  induction h with
  | nil => rfl
  | @gap use pre tail hQuiet _ ih =>
    have hNone := fun e he => (hQuiet e he).1
    have hPre := noTargets hNone (fun e he => hKnown e (List.mem_append_left tail he))
    rw [List.filterMap_append, hPre, List.nil_append, List.countP_append, quietCount hNone,
      Nat.zero_add]
    exact ih (fun e he => hKnown e (List.mem_append_right pre he))
  | @packet use n site mid tail hPlane hQuiet hStep ih =>
    let poll := cursorPoll l g use site
    let arrived := cursorArrival l g use site
    let failed := List.replicate n (poll false)
    let before := failed ++ (poll true :: mid)
    have hWalk : failed ++ poll true :: mid ++ arrived :: tail =
        before ++ arrived :: tail := by simp only [before, List.cons_append, List.append_assoc]
    rw [hWalk] at hKnown ⊢
    have hNonePoll (ok : Bool) : ¬ recurringPublicationEvent (poll ok) := by
      rintro ⟨_, _, h⟩
      cases congrArg Event.kind h
    have hNone : ∀ e ∈ before, ¬ recurringPublicationEvent e := by
      intro e hm
      rw [List.mem_append, List.mem_replicate, List.mem_cons] at hm
      rcases hm with ⟨_, rfl⟩ | rfl | hm
      · exact hNonePoll false
      · exact hNonePoll true
      · exact (hQuiet e hm).1
    have hZero := noTargets hNone (fun e he => hKnown e (List.mem_append_left _ he))
    have hNext := ih fun e hm => hKnown e
      (List.mem_append_right _ (List.mem_cons_of_mem _ hm))
    have hMark : recurringMark arrived = true := decide_eq_true ⟨site, _, rfl⟩
    have hTarget : readyTarget arrived = some (readyUseTarget l (g / l.block) use) := rfl
    rw [List.filterMap_append, hZero, List.nil_append, List.filterMap_cons, hTarget,
      List.countP_append, quietCount hNone, Nat.zero_add, List.countP_cons, hMark,
      show (if true = true then 1 else 0) = 1 from rfl, hNext]
    rw [List.range'_succ]
    rfl

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i : Nat} {pub : Publication} {loc : Loc}
    (hIssue : X.AsyncArrive (g, i) loc true)
    (hPublished : (atPrefix l X g (i + 1)).published = pub :: (atPrefix l X g i).published)
include hp hX hIssue hPublished

/-- In the loader's role history the recurring packet at ordinal zero uses
ring slot two. Each further publication advances one slot and alternates the
cache plane. The recorded count includes this publication. -/
theorem recurringPublicationSlotPlaneAndGeneration (hRecurring : pub.packet.period ≠ .priming) :
    let use := ((atPrefix l X g (i + 1)).published.countP
      (fun q => decide (q.packet.period ≠ .priming))) + 1
    pub.slot = kvUseStage use ∧
      pub.packet.plane = (if use % 2 = 0 then .key else .value) ∧
      (atPrefix l X g i).published.countP (fun q => q.slot == pub.slot) = use / 3 := by
  obtain ⟨pc, he⟩ := hIssue
  have hi := (List.getElem?_eq_some_iff.mp (show (X.tr g)[i]? = _ from he)).1
  obtain ⟨⟨decoded, rfl⟩, _, _, _⟩ := actualAsyncArrival hX he
  obtain ⟨q, _, hObj, hObs⟩ := readyObservation hp hX he rfl
  have hState := (congrArg D.published (prefixStep (l := l) he)).trans (advancePublication hObs)
  obtain rfl := (List.cons.inj (hPublished.symm.trans hState)).1
  have hPacket := classifiedPlaneOfArrival decoded hObs
  have hSite : ∃ site, decoded = recurringPacketSite site := by
    have hn := hRecurring
    rw [hPacket] at hn
    fin_cases decoded
    · exact (hn rfl).elim
    · exact (hn rfl).elim
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨site, rfl⟩ := hSite
  change X.get (g, i) = some ⟨reuseArrival site, .asyncArrive loc true⟩ at he
  obtain ⟨pre0, pre1, pre2, rest, nK, nV, hSplit, hEarly, hPre0, hPre1, hPre2,
      hRange, hkSeen, hvSeen, hkCount, hvCount, hCursor⟩ := actualLoaderCursorThrough hp hX site he
  let last : Event := ⟨reuseArrival site, .asyncArrive loc true⟩
  have hMarkLast : recurringPublicationEvent last := ⟨site, loc, rfl⟩
  have hLast : ((X.tr g).take (i + 1)).getLast? = some last := by
    rw [List.take_add_one, show (X.tr g)[i]? = some last from he]
    simp [List.getLast?_append]
  let initial := (X.tr g).take 5 ++ pre0 ++
    (List.replicate nK (primingCursorPoll l g 0 false) ++ [primingCursorPoll l g 0 true]) ++
    pre1 ++ (List.replicate nV (primingCursorPoll l g 1 false) ++ [primingCursorPoll l g 1 true]) ++
    pre2
  change (X.tr g).take (i + 1) = initial ++ rest at hSplit
  have hQuiet : ∀ e ∈ initial, ¬ recurringPublicationEvent e := by
    intro e hm hMark
    have hLo := recurringPc hMark
    simp only [initial, List.mem_append, List.mem_replicate, List.mem_singleton] at hm
    rcases hm with (((((hh | h0) | (hk | hk)) | h1) | (hv | hv)) | h2)
    · have := hEarly e hh; omega
    · have := hPre0 e h0; omega
    · obtain ⟨_, rfl⟩ := hk; exact (by change 909 ≤ 517 at hLo; omega)
    · subst e; exact (by change 909 ≤ 517 at hLo; omega)
    · have := (hPre1 e h1).2; omega
    · obtain ⟨_, rfl⟩ := hv; exact (by change 909 ≤ 782 at hLo; omega)
    · subst e; exact (by change 909 ≤ 782 at hLo; omega)
    · have := (hPre2 e h2).2; omega
  rw [hSplit] at hLast
  have hRest : rest ≠ [] := by
    intro hr
    simp only [hr, List.append_nil] at hLast
    exact hQuiet last (List.mem_of_getLast? hLast) hMarkLast
  obtain ⟨actualSite, hEqual, hPlane⟩ := hCursor.lastUse
    (lastOfAppendRight hLast hRest) hMarkLast
  let use := rest.countP recurringMark + 1
  have hCount := recurringPrefixCount hp hX g (i + 1) (by omega)
  rw [hSplit, List.countP_append, quietCount hQuiet, Nat.zero_add] at hCount
  change pub.slot = kvUseStage (_ + 1) ∧ pub.packet.plane = _ ∧
    (atPrefix l X g i).published.countP (fun q => q.slot == pub.slot) = _
  change (atPrefix l X g (i + 1)).published.countP recurring = _ at hCount
  rw [show ((atPrefix l X g (i + 1)).published.countP
    (fun q => decide (q.packet.period ≠ .priming))) =
      rest.countP recurringMark from hCount]
  have hu : 2 + rest.countP recurringMark - 1 = use := by dsimp [use]; omega
  rw [hu] at hEqual hPlane
  have hSameSite : actualSite = site := by
    have h := congrArg Event.pc hEqual
    change reuseArrival site = reuseArrival actualSite at h
    fin_cases site <;> fin_cases actualSite <;> first | rfl | cases h
  subst actualSite
  have hTarget : loc = readyObject l g (kvUseStage use) := by
    have h := congrArg Event.kind hEqual
    exact (Kind.asyncArrive.inj h).1
  have hSlot : pub.slot = kvUseStage use := by
    apply Fin.ext
    have hA := congrArg Loc.addr (hObj.symm.trans hTarget)
    simp [readyObject, PTX.Kernels.TmlFa4Fwd.Loader.readySlot_address] at hA
    omega
  refine ⟨hSlot, ?_, ?_⟩
  · rw [hPacket, ← hPlane]
    fin_cases site <;> decide
  have hRaw {event : Event} (hm : event ∈ initial ++ rest) : event ∈ X.tr g := by
    rw [← hSplit] at hm
    exact List.mem_of_mem_take hm
  have hK := primingReadyTargets hp hX (g := g) (es := pre1) 0
    (fun e hm => hRaw (by simp [initial, hm])) (by
      intro e hm site hPc
      have hArea := hPre1 e hm
      fin_cases site <;> try rfl
      all_goals simp [copyCommitPc] at hPc; omega)
    hkSeen hkCount
  have hV := primingReadyTargets hp hX (g := g) (es := pre2) 1
    (fun e hm => hRaw (by simp [initial, hm])) (by
      intro e hm site hPc
      have hArea := hPre2 e hm
      fin_cases site <;> try rfl
      all_goals simp [copyCommitPc] at hPc; omega)
    hvSeen hvCount
  have hHead := withoutReadyTargets hX (es := (X.tr g).take 5)
    (fun e hm => List.mem_of_mem_take hm) (fun e hm => by have := hEarly e hm; omega)
  have hPrelude := withoutReadyTargets hX (es := pre0) (g := g)
    (fun _ hm => hRaw (by simp [initial, hm])) (fun e hm => by have := hPre0 e hm; omega)
  have hPolls (stage : Fin 2) (n : Nat) :
      (List.replicate n (primingCursorPoll l g stage false) ++
        [primingCursorPoll l g stage true]).filterMap readyTarget = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e hm
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hm
    rcases hm with ⟨_, rfl⟩ | rfl <;> rfl
  have hInit : initial.filterMap readyTarget =
      [readyUseTarget l (g / l.block) 0, readyUseTarget l (g / l.block) 1] := by
    simp only [initial, List.filterMap_append, hHead, hPrelude, hPolls, hK, hV,
      List.nil_append, List.append_nil, List.singleton_append]
    rfl
  have hRestReady := hCursor.targets (by
    intro e hm has
    obtain ⟨target, hHas⟩ := Option.isSome_iff_exists.mp has
    obtain ⟨j, actual, hPc, _, hEv⟩ :=
      actualReadyTargetSource hX (hRaw (List.mem_append_right _ hm)) hHas
    have lo := (hRange e hm).1
    fin_cases actual
    · have hInitPc : e.pc = 674 := hPc
      omega
    · have hInitPc : e.pc = 904 := hPc
      omega
    · exact ⟨0, target, hEv.trans (by rw [hPc]; rfl)⟩
    · exact ⟨1, target, hEv.trans (by rw [hPc]; rfl)⟩
    · exact ⟨2, target, hEv.trans (by rw [hPc]; rfl)⟩
    · exact ⟨3, target, hEv.trans (by rw [hPc]; rfl)⟩)
  let route := readyUseTarget l (g / l.block)
  have hSeq : ((X.tr g).take (i + 1)).filterMap readyTarget = (List.range (use + 1)).map route := by
    rw [hSplit, List.filterMap_append, hInit, hRestReady, List.range_eq_range',
      show use + 1 = 2 + rest.countP recurringMark by dsimp [use]; omega,
      ← List.range'_append_1 (s := 0) (m := 2), List.map_append]
    rfl
  have hLoc : loc = route use := hTarget
  have hBefore : ((X.tr g).take i).filterMap readyTarget = (List.range use).map route := by
    rw [List.take_add_one, show (X.tr g)[i]? = some last from he, List.range_succ,
      List.filterMap_append, List.map_append] at hSeq
    apply List.append_cancel_right (bs := [loc])
    simpa [last, readyTarget, ← hLoc] using hSeq
  have hGen := readyOrdinalOfUse (use := use) (i := (g, i)) hBefore
  have hCountSlot := publicationOrdinal hp hX g i pub.slot
  rw [hCountSlot, hSlot]
  exact hGen

/-- The exact logical occurrence of an actual recurring publication is its
physical slot plus three times its generation. The copy cursor uses the same
publication count. -/
private theorem recurringPublicationOccurrence (hRecurring : pub.packet.period ≠ .priming) :
    let ordinal := (atPrefix l X g i).published.countP (fun q => q.slot == pub.slot)
    recurringUseBefore X (g, i) = 3 * ordinal + pub.slot.val ∧
      ∃ e, X.get (g, i) = some e ∧ recurringPublicationMark e = true := by
  obtain ⟨hSlot, _, hPhase⟩ :=
    recurringPublicationSlotPlaneAndGeneration hp hX hIssue hPublished hRecurring
  obtain ⟨pc, he⟩ := hIssue
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hSame : recurringMark = recurringPublicationMark := by
    funext e
    apply Bool.eq_iff_iff.mpr
    simp only [recurringMark, decide_eq_true_eq, recurringPublicationMark_iff]
  have hOccurrence : ((atPrefix l X g i).published.countP recurring) + 2 =
      recurringUseBefore X (g, i) := by
    rw [recurringPrefixCount hp hX g i hi.le, hSame]
    simp only [recurringUseBefore, Nat.add_comm]
  have hAdvance := stepRecurringCount hp hX he (atPrefix l X g i)
  rw [← congrArg D.published (prefixStep (l := l) he), hPublished, List.countP_cons,
    show recurring pub = true from decide_eq_true hRecurring, hSame] at hAdvance
  have hMarked : recurringPublicationMark ⟨pc, .asyncArrive loc true⟩ = true := by
    cases hMark : recurringPublicationMark ⟨pc, .asyncArrive loc true⟩
    · simp only [hMark, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hAdvance
      omega
    · rfl
  refine ⟨?_, _, he, hMarked⟩
  rw [hPhase, hSlot, kvUseStage_val, hPublished, List.countP_cons]
  have hCheck : decide (pub.packet.period ≠ .priming) = true := decide_eq_true hRecurring
  rw [hCheck, ite_eq_left rfl]
  change recurringUseBefore X (g, i) =
    3 * (((atPrefix l X g i).published.countP recurring + 1 + 1) / 3) +
      ((atPrefix l X g i).published.countP recurring + 1 + 1) % 3
  omega

private theorem primingPublicationRank (hPriming : pub.packet.period = .priming) :
    (atPrefix l X g i).published.countP (fun q => q.slot == pub.slot) = 0 ∧
      pub.slot.val < 2 ∧
      pub.packet.plane = (if pub.slot.val % 2 = 0 then .key else .value) := by
  obtain ⟨pc, he⟩ := hIssue
  obtain ⟨⟨site, rfl⟩, _, _, _⟩ := actualAsyncArrival hX he
  obtain ⟨q, _, hLoc, hObs⟩ := readyObservation hp hX he rfl
  have hState := (congrArg D.published (prefixStep (l := l) he)).trans (advancePublication hObs)
  obtain rfl := (List.cons.inj (hPublished.symm.trans hState)).1
  have hPacket := classifiedPlaneOfArrival site hObs
  have hSite : copyCommitPc site + 1 ∈ [674, 904] := by
    rw [hPacket] at hPriming
    fin_cases site <;> first | decide | contradiction
  have hFirst : (atPrefix l X g i).published.countP (fun q' => q'.slot == pub.slot) = 0 := by
    by_contra hNe
    have hExact : X.AsyncArrive (g, i) (readyObject l g pub.slot) true := by
      rw [← hLoc]
      exact ⟨_, he⟩
    have hPos : 0 < (atPrefix l X g i).published.countP (fun q' => q'.slot == pub.slot) :=
      Nat.pos_of_ne_zero hNe
    obtain ⟨j, hj, hEarlier, _⟩ := earlierPublication hp hX hExact hPos
    obtain ⟨later, hLater⟩ :=
      Loader.laterPublicationIsRecurring hp hX hj hEarlier hExact
    rw [← hLoc, he] at hLater
    have hEq := congrArg Event.pc (Option.some.inj hLater)
    change copyCommitPc site + 1 = reuseArrival later at hEq
    have hHi : copyCommitPc site + 1 ≤ 904 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
      omega
    have hLo : 909 ≤ reuseArrival later := by fin_cases later <;> decide
    omega
  have hAddr := congrArg Loc.addr ((loaderStartupAsyncAddress hp hX he hSite).symm.trans hLoc)
  change l.sharedBase + (if copyCommitPc site + 1 = 674 then 32 else 40) =
    (Prologue.initObject l (g / l.block) (Loader.readySlot pub.slot)).addr at hAddr
  rw [Loader.readySlot_address] at hAddr
  rw [hPacket] at hPriming
  refine ⟨hFirst, ?_⟩
  fin_cases site <;> try contradiction
  · have hSlot : pub.slot.val = 0 := by
      change l.sharedBase + 32 = l.sharedBase + 8 * pub.slot.val + 32 at hAddr
      omega
    exact ⟨by omega, by rw [hSlot, hPacket]; rfl⟩
  · have hSlot : pub.slot.val = 1 := by
      change l.sharedBase + 40 = l.sharedBase + 8 * pub.slot.val + 32 at hAddr
      omega
    exact ⟨by omega, by rw [hSlot, hPacket]; rfl⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A ready publication with logical occurrence at least two uses the recurring
publication cursor. The initial two arrivals cannot supply this occurrence. -/
theorem readyPublicationOccurrence {g i owner : Nat} {slot : Fin 3}
    (hPub : X.AsyncArrive (g, i) (readyObject l owner slot) true)
    (hRepeat : 2 ≤ 3 * ((atPrefix l X g i).published.countP (fun q => q.slot == slot)) + slot.val) :
    recurringUseBefore X (g, i) =
      3 * ((atPrefix l X g i).published.countP (fun q => q.slot == slot)) + slot.val ∧
      ∃ e, X.get (g, i) = some e ∧ recurringPublicationMark e = true := by
  obtain ⟨pc, he⟩ := hPub
  obtain ⟨pub, _, hLoc, hObs⟩ := readyObservation hp hX he rfl
  have hPublished := (congrArg D.published (prefixStep (l := l) he)).trans (advancePublication hObs)
  have hSlot : pub.slot = slot := by
    have hAddr := congrArg Loc.addr hLoc
    change (Prologue.initObject l (owner / l.block) (Loader.readySlot slot)).addr =
      (Prologue.initObject l (g / l.block) (Loader.readySlot pub.slot)).addr at hAddr
    rw [Loader.readySlot_address, Loader.readySlot_address] at hAddr
    change l.sharedBase + 8 * slot.val + 32 = l.sharedBase + 8 * pub.slot.val + 32 at hAddr
    exact Fin.ext (by omega)
  have hPub : X.AsyncArrive (g, i) (readyObject l owner slot) true := ⟨pc, he⟩
  rw [← hSlot] at hRepeat ⊢
  apply recurringPublicationOccurrence hp hX hPub hPublished
  intro hPriming
  obtain ⟨hRank, hBefore, _⟩ := primingPublicationRank hp hX hPub hPublished hPriming
  omega

/-- A ready use past the two priming packets selects a recurring publication. -/
theorem PublishedCopyGroup.recurringOfReadyUse {issue : EvId} (group : PublishedCopyGroup l X issue)
    {owner : Nat} {slot : Fin 3} (hPub : X.AsyncArrive issue (readyObject l owner slot) true)
    (hRepeat : 2 ≤ 3*((atPrefix l X issue.1 issue.2).published.countP
      (fun q => q.slot == slot))+slot.val) :
    group.publication.packet.period ≠ .priming := by
  obtain ⟨g,i⟩ := issue
  obtain ⟨pc,he⟩ := hPub
  obtain ⟨actual,_,hLoc,hObs⟩ := readyObservation hp hX he rfl
  have hTrace := (congrArg D.published (prefixStep (l := l) he)).trans
    (advancePublication hObs)
  have hGroup := (List.cons.inj (hTrace.symm.trans group.published)).1
  have hSlot : actual.slot = slot := by
    have hAddr := congrArg Loc.addr hLoc
    change (Prologue.initObject l (owner/l.block) (Loader.readySlot slot)).addr =
      (Prologue.initObject l (g/l.block) (Loader.readySlot actual.slot)).addr at hAddr
    rw [Loader.readySlot_address,Loader.readySlot_address] at hAddr
    change l.sharedBase+8*slot.val+32 = l.sharedBase+8*actual.slot.val+32 at hAddr
    exact Fin.ext (by omega)
  intro hPriming
  rw [← hSlot] at hRepeat
  have hp' : actual.packet.period = .priming := hGroup.symm ▸ hPriming
  obtain ⟨hRank,hBefore,_⟩ := primingPublicationRank hp hX ⟨pc,he⟩ hTrace hp'
  change 2 ≤ 3*((atPrefix l X g i).published.countP (fun q => q.slot == actual.slot))+
    actual.slot.val at hRepeat
  omega

/-- The logical use of a recorded recurring arrival identifies its exact
physical barrier and publication generation. -/
theorem recurringPublicationAtUse {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hMark : recurringPublicationMark e = true) :
    let use := recurringUseBefore X (g,index)
    X.AsyncArrive (g,index) (readyObject l g (kvUseStage use)) true ∧
      (atPrefix l X g index).published.countP (fun pub => pub.slot == kvUseStage use) =
        use/3 := by
  have hRecurring := (recurringPublicationMark_iff e).mp hMark
  have hLow := recurringPc hRecurring
  obtain ⟨_,target,rfl⟩ := hRecurring
  obtain ⟨⟨site,hSite⟩,_,_,_⟩ := actualAsyncArrival hX he
  rw [hSite] at he hLow
  obtain ⟨pub,_,hLoc,hObs⟩ := readyObservation hp hX he rfl
  have hPublished := (congrArg D.published (prefixStep (l := l) he)).trans
    (advancePublication hObs)
  have hPacket := classifiedPlaneOfArrival site hObs
  have hPeriod : ∀ site, 909 ≤ copyCommitPc site + 1 →
      (DecodedObservation.packetOfSite site).period ≠ .priming := by decide
  have hRepeat : pub.packet.period ≠ .priming := by
    rw [hPacket]
    exact hPeriod site hLow
  have hArrive : X.AsyncArrive (g,index) target true := ⟨_,he⟩
  obtain ⟨hUse,_⟩ := recurringPublicationOccurrence hp hX hArrive hPublished hRepeat
  let use := recurringUseBefore X (g,index)
  let phase := (atPrefix l X g index).published.countP (fun q => q.slot == pub.slot)
  change use = 3 * phase + pub.slot.val at hUse
  have hSlot : kvUseStage use = pub.slot := Fin.ext (by
    rw [kvUseStage_val]
    have := pub.slot.isLt
    omega)
  dsimp only
  rw [hSlot]
  exact ⟨hLoc ▸ hArrive,by have := pub.slot.isLt; omega⟩

omit hp hX in
/-- A publication of at least the pending copy's logical use necessarily follows
that copy on its issuing lane. The carry of the same ordinal in the open packet
ensures the strict order even when the publication is the first one tracking it. -/
private theorem copyBeforePublicationOfOccurrence {X : Execution} {g i j : Nat}
    {s : AsyncCopy.Spec} (hCopy : X.Copy (g, i) s)
    {e : Event} (hEvent : X.get (g, j) = some e)
    (hPublication : recurringPublicationMark e = true)
    (hOrdinal : recurringUseBefore X (g, i) ≤ recurringUseBefore X (g, j)) :
    TraceBefore X (g, i) (g, j) := by
  have hLength : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hEvent).1
  refine ⟨rfl, ?_, hLength⟩
  by_contra! hNot
  rcases Nat.eq_or_lt_of_le hNot with rfl | hAfter
  · obtain ⟨pc, he⟩ := hCopy
    obtain rfl := Option.some.inj (hEvent.symm.trans he)
    obtain ⟨site, loc, hEq⟩ := (recurringPublicationMark_iff _).mp hPublication
    cases congrArg Event.kind hEq
  · have hCount := countP_take_mono recurringPublicationMark (X.tr g) (show j + 1 ≤ i by omega)
    rw [countP_take_succ hEvent hPublication] at hCount
    dsimp only [recurringUseBefore] at hOrdinal
    omega

/-- On the same loader lane, a ready publication with at least the copy's
logical occurrence tracks that already issued copy. -/
theorem copyBeforeReadyPublicationOfOccurrence {copy publication : EvId} {s : AsyncCopy.Spec}
    {owner : Nat} {slot : Fin 3} (hCopy : X.Copy copy s)
    (hPub : X.AsyncArrive publication (readyObject l owner slot) true)
    (hLane : copy.1 = publication.1)
    (hOrdinal : recurringUseBefore X copy ≤
      3 * ((atPrefix l X publication.1 publication.2).published.countP (fun q => q.slot == slot)) +
        slot.val) :
    TraceBefore X copy publication := by
  obtain ⟨g, j⟩ := publication
  obtain ⟨g', i⟩ := copy
  change g' = g at hLane
  subst g'
  have hLower : 2 ≤ recurringUseBefore X (g, i) := by
    unfold recurringUseBefore
    omega
  obtain ⟨hUse, e, he, hMark⟩ := readyPublicationOccurrence hp hX hPub
    (hLower.trans hOrdinal)
  exact copyBeforePublicationOfOccurrence hCopy he hMark (hUse.symm ▸ hOrdinal)

/-- A recorded recurring vector belongs to the publication of its same
logical use on the producer lane. -/
theorem copyMemberOfPublicationOfOccurrence {g i j owner : Nat} {e : Event} {slot : Fin 3}
    {spec : AsyncCopy.Spec} (he : X.get (g,i) = some e) (hVector : recurringVectorEvent e)
    (hKind : e.kind = .copy spec) (hPub : X.AsyncArrive (g,j) (readyObject l owner slot) true)
    (hUse : recurringUseBefore X (g,i) =
      3 * ((atPrefix l X g j).published.countP (fun q => q.slot == slot)) + slot.val) :
    ∃ group : PublishedCopyGroup l X (g,j), (i,spec) ∈ group.copies := by
  obtain ⟨site,pair,upper,actual,rfl⟩ := hVector
  have hSpec := Kind.copy.inj hKind
  subst actual
  have hRecurring : 2 ≤ recurringUseBefore X (g,i) := by unfold recurringUseBefore; omega
  have hRank := (readyPublicationOccurrence hp hX hPub (hUse ▸ hRecurring)).1
  have hCopy : X.Copy (g,i) spec := ⟨_,he⟩
  have hOrder := copyBeforeReadyPublicationOfOccurrence hp hX hCopy hPub rfl hUse.le
  obtain ⟨packet,k,loc,hj,_,hLimit,hGet,_,hi,hNone⟩ :=
    copyFirstPublicationBeforePublicationAtPacket hX he hPub hOrder.2.1
  have hLow : 909 ≤ Loader.packetPlanePc (recurringPacketSite site) pair upper := by
    fin_cases site <;> fin_cases pair <;> cases upper <;> decide
  have hMarked (q : Fin 6)
      (h : 909 ≤ copyCommitPc q + 1) :
      recurringPublicationMark ⟨copyCommitPc q+1,.asyncArrive loc true⟩ = true := by
    have hSites : ∀ q : Fin 6, 909 ≤ copyCommitPc q + 1 →
        ∃ r : Fin 4, copyCommitPc q + 1 = reuseArrival r := by decide
    obtain ⟨r,hr⟩ := hSites q h
    exact (recurringPublicationMark_iff _).2 ⟨r,loc,by rw [hr]⟩
  have hSame : k = j := by
    by_contra! hDiff
    have hLt : k + 1 ≤ j := by omega
    have hCount := countP_take_mono recurringPublicationMark (X.tr g) hLt
    rw [countP_take_succ hGet (hMarked packet (by omega))] at hCount
    have hPrior := countP_take_mono recurringPublicationMark (X.tr g)
      (show i ≤ k by omega)
    have hEq := hUse.trans hRank.symm
    change 2 + ((X.tr g).take i).countP recurringPublicationMark =
      2 + ((X.tr g).take j).countP recurringPublicationMark at hEq
    omega
  exact copyMemberOfNextPublication hp hX hCopy hPub (hSame ▸ hi) (hSame ▸ hNone)

/-- A publication's slot and generation recover its K/V plane, including priming. -/
theorem publicationPlaneOfGeneration {g i : Nat} {pub : Publication} {loc : Loc}
    (hIssue : X.AsyncArrive (g, i) loc true)
    (hPublished : (atPrefix l X g (i + 1)).published = pub :: (atPrefix l X g i).published) :
    let ordinal := (atPrefix l X g i).published.countP (fun q => q.slot == pub.slot)
    pub.packet.plane = if (3 * ordinal + pub.slot.val) % 2 = 0 then .key else .value := by
  dsimp only
  by_cases hPriming : pub.packet.period = .priming
  · obtain ⟨hRank, _, hPlane⟩ := primingPublicationRank hp hX hIssue hPublished hPriming
    simpa only [hRank, Nat.mul_zero, Nat.zero_add] using hPlane
  · obtain ⟨hSlot, hPlane, hOrdinal⟩ :=
      recurringPublicationSlotPlaneAndGeneration hp hX hIssue hPublished hPriming
    rw [hOrdinal, hSlot, kvUseStage_val]
    have hUse (use : Nat) : 3 * (use / 3) + use % 3 = use := by omega
    rw [hUse]
    exact hPlane

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
