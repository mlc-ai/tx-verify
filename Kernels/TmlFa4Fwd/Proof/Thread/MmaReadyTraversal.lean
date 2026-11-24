-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyOrder
public import Kernels.TmlFa4Fwd.Proof.MmaReadySequence
public import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
public import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (readySlot readySlot_address)
open Observation (readyObject)

noncomputable section

private theorem waitSitePc {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g index pc parity : Nat} {loc : Loc} {acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨pc, .wait loc parity true acq scope⟩) :
    pc ∈ Flow.mbarWait.toList := by
  obtain ⟨_, hk⟩ | ⟨_, ins, _, _, hCode, hFire⟩ := get_source hX he
  · cases hk
  have hOp : isMbarPoll ins.op = true := by
    by_contra hc
    have hw : ∀ p b d par a sc, ins.op ≠ .mbarWait p b d par a sc := by
      intro p b d par a sc ho
      exact hc (ho.symm ▸ rfl)
    exact fires_notWait (eventTmpl_notWait hw) hFire loc parity true acq scope rfl
  have hAll : OpPcsFast kernel.code isMbarPoll Flow.mbarWait.toList = true := by decide +kernel
  exact OpPcsFast.mem hAll hCode hOp

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem readyWaitPc {g index pc parity : Nat} {acq : Bool} {scope : MbarScope}
    (hw : warpIndex l g = 12) (slot : Fin 3)
    (he : X.get (g, index) = some ⟨pc, .wait (readyObject l g slot) parity true acq scope⟩) :
    (List.finRange 4).any (fun i => readyHead i == pc) = true := by
  have hSite := waitSitePc hX he
  have limits : Flow.mbarWait.toList.all (fun p =>
      decide (173 < p ∧ p ≠ 9205 ∧ p ∉ registerHintSites)) = true := by decide
  obtain ⟨hLate, hExit, hHint⟩ := of_decide_eq_true (List.all_eq_true.mp limits pc hSite)
  have hBody := roleBodyPcOfEvent hp hX he hLate hHint
  rw [hw] at hBody
  have hRange : 1908 ≤ pc ∧ pc < 2768 := by
    simpa [roleBodyPc, hExit] using hBody
  have table : Flow.mbarWait.toList.all (fun pc =>
      !(decide (1908 ≤ pc ∧ pc < 2768)) ||
        (List.finRange 4).any (fun i => readyHead i == pc) ||
        [2141, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626].contains pc) = true := by
    decide
  have hCases := List.all_eq_true.mp table pc hSite
  have hDec := decide_eq_true hRange
  simp only [hDec, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hCases
  rcases hCases with h | h
  · exact h
  · have hMem := List.contains_iff_mem.mp h
    have hOffset := mmaFixedWaitAddress hp hX he (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢
      tauto)
    change initObject l (g / l.block) (readySlot slot) = _ at hOffset
    rw [readySlot_address] at hOffset
    have hAddr := congrArg Loc.addr hOffset
    have hValues : fixedMmaWaitOffset pc ∈ [0, 8, 96, 104, 112, 120] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
      rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
    have hSlot := slot.isLt
    change l.sharedBase + 8 * slot.val + 32 = l.sharedBase + fixedMmaWaitOffset pc at hAddr
    omega

/-- An actual ready acquire of the MMA lane occurs at one of its decoded gate heads. -/
theorem ReadyPoll.atGate {g index parity : Nat} (hw : warpIndex l g = 12) {slot : Fin 3}
    {acquire : Bool} {scope : MbarScope} (h : ReadyPoll l X g index slot parity acquire scope) :
    ∃ gate : Fin 4, X.get (g,index) = some ⟨readyHead gate,
      .wait (readyObject l g slot) parity true acquire scope⟩ := by
  obtain ⟨⟨pc, kind⟩, he, hk⟩ := h
  dsimp only at hk
  subst kind
  obtain ⟨gate, _, hGate⟩ := List.any_eq_true.mp (readyWaitPc hp hX hw slot he)
  exact ⟨gate, by rwa [beq_iff_eq.mp hGate]⟩

private theorem rawReadyAttemptSequence {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) :
    ReadyAttemptSequence l g 0 ((X.tr g).filterMap readyAttemptEvent) := by
  classical
  have late {j : Nat} {e : Event} {operand : Bool × (Nat × (Loc × Nat))}
      (hr : X.get (g, j) = some e) (hMark : readyAttemptEvent e = some operand) :
      5 ≤ j ∧ ∃ next o, At next 174 [(1062, b32 12), (2535, b32 l.sharedBase)] ∧
        Run kernel Assumptions.all l g next ((X.tr g).drop 5) o := by
    have hPc : ∃ i : Fin 4, e.pc = readyHead i := by
      unfold readyAttemptEvent at hMark
      split at hMark
      · split at hMark
        · rename_i hHead
          obtain ⟨i, _, h⟩ := List.any_eq_true.mp hHead
          exact ⟨i, (beq_iff_eq.mp h).symm⟩
        · cases hMark
      · cases hMark
    obtain ⟨i, hPc⟩ := hPc
    have hLate : 173 < e.pc := by rw [hPc]; fin_cases i <;> decide
    obtain ⟨next, o, hj, ht, hRun⟩ :=
      nonzeroCommonPrefixOfLateEvent hp hX hg (by rw [hw]; decide) hr hLate
    exact ⟨hj, next, o, ht.mono ⟨hw ▸ ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩, hRun⟩
  by_cases hNone : (X.tr g).filterMap readyAttemptEvent = []
  · rw [hNone]
    exact .nil _
  obtain ⟨operand, hOp⟩ := List.exists_mem_of_ne_nil _ hNone
  obtain ⟨e, hMem, hMark⟩ := List.mem_filterMap.mp hOp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hMem
  have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
  obtain ⟨hPos, t, o, ht, hRun⟩ := late he hMark
  have hNonempty : (X.tr g).drop 5 ≠ [] := by
    intro hn
    have hm := List.drop_eq_nil_iff.mp hn
    omega
  obtain ⟨s, _, hHint, hAt, hBody⟩ := firstRegisterHintFromCommon hp hg
    (⟨12, by decide⟩ : Fin 16) ht hRun hNonempty
  have hPrefix : ((X.tr g).take 6).filterMap readyAttemptEvent = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro prior hMem
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hMem
    have hBounds := hk
    rw [List.length_take] at hBounds
    have hkLt : k < 6 := by omega
    have hkTrace : k < (X.tr g).length := by omega
    rw [List.getElem_take]
    have hGet : X.get (g, k) = some (X.tr g)[k] :=
      List.getElem?_eq_getElem hkTrace
    cases hM : readyAttemptEvent (X.tr g)[k] with
    | none => rfl
    | some pair =>
      have hK := (late hGet hM).1
      have hkEq : k = 5 := by omega
      subst k
      have hEq := Option.some.inj (hGet.symm.trans hHint)
      rw [hEq] at hM
      cases hM
  obtain ⟨visits, hWalk⟩ := walkFromRun hBody
  have hs : At s 1908 (readyFrame l) := hAt.mono ⟨hAt.2.2.2.2.2.1, hAt.2.2.2.2.1, trivial⟩
  rw [← List.take_append_drop 6 (X.tr g), List.filterMap_append, hPrefix, List.nil_append]
  exact readyAttemptSequenceFromEntry hp hs hWalk

private theorem rawTaggedReadySequence {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) :
    TaggedReadySequence l g 0 ((X.tr g).filterMap readyEventTagged) := by
  rw [← readyAttemptProjection]
  exact (rawReadyAttemptSequence hp hX hg hw).erase

/-- A failed or successful cache-ready attempt uses the ring slot and phase of the
same logical generation. The prefix may end at that attempt. -/
theorem readyAttemptUseAtPrefix {g index pc phase : Nat} {loc : Loc} {ok acquire : Bool}
    {scope : MbarScope} (hw : warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨pc,.wait loc phase ok acquire scope⟩)
    (hGate : ∃ i : Fin 4, pc = readyHead i) :
    let use := (((X.tr g).take index).filterMap readyEvent).length
    ReadyUseSite use pc ∧ (loc, phase) = readyOperand l g use := by
  let e : Event := ⟨pc,.wait loc phase ok acquire scope⟩
  let before := (X.tr g).take index
  let attempts := before.filterMap readyAttemptEvent
  have hMark : readyAttemptEvent e = some (ok, (pc, (loc, phase))) := by
    obtain ⟨i,hi⟩ := hGate
    have hYes : (List.finRange 4).any (fun i => readyHead i == pc) = true :=
      List.any_eq_true.mpr ⟨i, by simp, beq_iff_eq.mpr hi.symm⟩
    simp [e, readyAttemptEvent, hYes]
  have hSplit : (X.tr g).filterMap readyAttemptEvent =
      attempts ++ (ok, (pc, (loc, phase))) ::
        ((X.tr g).drop (index+1)).filterMap readyAttemptEvent := by
    conv_lhs => rw [← List.take_append_drop index (X.tr g), List.filterMap_append]
    have hLen : index < (X.tr g).length := len_of_get he
    have hHead : (X.tr g)[index] = e := (List.getElem?_eq_some_iff.mp he).2
    rw [List.drop_eq_getElem_cons hLen, hHead, List.filterMap_cons, hMark]
  have hGet : ((X.tr g).filterMap readyAttemptEvent)[attempts.length]? =
      some (ok, (pc, (loc, phase))) := by
    rw [hSplit, List.getElem?_append_right (by rfl), Nat.sub_self]
    rfl
  have hBefore : ((X.tr g).filterMap readyAttemptEvent).take attempts.length = attempts := by
    rw [hSplit, List.take_left]
  have hReady := (rawReadyAttemptSequence hp hX (event_thread_lt hX he) hw).get hGet
  dsimp only at hReady
  rw [hBefore, Nat.zero_add, show attempts.filterMap successfulReadyAttempt =
    before.filterMap readyEventTagged from readyAttemptProjection before] at hReady
  rw [← taggedProjectionErase before, List.length_map]
  exact hReady

omit hp hX in
private def valueReadyTag (pc : Nat) : Bool := pc == readyHead 1 || pc == readyHead 3

omit hp hX in
private theorem taggedValueCount {l : Launch} {g use : Nat} {es : List (Nat × (Loc × Nat))}
    (h : TaggedReadySequence l g use es) :
    es.countP (fun e => valueReadyTag e.1) = (use+es.length)/2-use/2 := by
  induction h with
  | nil => simp
  | @next use pc rest hSite _ ih =>
    have hFlag : valueReadyTag pc = decide (use%2 = 1) := by
      rcases hSite with ⟨rfl,rfl⟩ | ⟨rfl,_,hMod⟩ | ⟨hPc,hMod⟩
      · rfl
      · rw [hMod]
        rfl
      · rcases hPc with rfl | rfl <;> rw [hMod] <;> rfl
    simp only [List.countP_cons,hFlag,decide_eq_true_eq,List.length_cons,ih]
    split <;> omega

omit hp hX in
private theorem taggedPrefix {l : Launch} {g use : Nat} {es : List (Nat × (Loc × Nat))}
    (h : TaggedReadySequence l g use es) (n : Nat) :
    TaggedReadySequence l g use (es.take n) := by
  induction h generalizing n with
  | nil => simpa only [List.take_nil] using (TaggedReadySequence.nil (l := l) (g := g) _)
  | next hSite _ ih =>
    cases n
    · exact .nil _
    · exact .next hSite (ih _)

omit hp hX in
private theorem valueReadyProjection (es : List Event) :
    (es.filterMap readyEventTagged).countP (fun e => valueReadyTag e.1) =
      es.countP (readyAtSite 1) + es.countP (readyAtSite 3) := by
  rw [List.countP_filterMap]
  have hSites (i : Fin 4) : (slotWait i).pc = readyHead i := by fin_cases i <;> rfl
  have mark (e : Event) :
      ((readyEventTagged e).map (fun e => valueReadyTag e.1)).getD false =
        (readyAtSite 1 e || readyAtSite 3 e) := by
    obtain ⟨pc,kind⟩ := e
    cases kind <;> try rfl
    case wait loc q ok acq sc =>
      cases ok
      · rfl
      · change ((readyEventTagged ⟨pc,.wait loc q true acq sc⟩).map
          (fun e => valueReadyTag e.1)).getD false =
            (pc == (slotWait 1).pc || pc == (slotWait 3).pc)
        rw [hSites 1,hSites 3]
        by_cases hL : pc = readyHead 1
        · subst pc
          rfl
        by_cases hT : pc = readyHead 3
        · subst pc
          rfl
        · simp only [readyEventTagged,readyEvent]
          split <;> simp [valueReadyTag,beq_eq_false_iff_ne.mpr hL,beq_eq_false_iff_ne.mpr hT]
  rw [show (fun (e : Event) => ((readyEventTagged e).map
    (fun e => valueReadyTag e.1)).getD false) = (fun e => readyAtSite 1 e || readyAtSite 3 e)
    from funext mark]
  have disjoint (e : Event) (hL : readyAtSite 1 e = true) (hT : readyAtSite 3 e = true) :
      False := by
    obtain ⟨pc,kind⟩ := e
    cases kind <;> simp [readyAtSite] at hL hT
    case wait loc q ok acq sc =>
      cases ok <;> simp at hL hT
      exact (by decide : (slotWait 1).pc ≠ (slotWait 3).pc) (hL.symm.trans hT)
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.countP_cons,ih]
    cases hL : readyAtSite 1 e <;> cases hT : readyAtSite 3 e
    all_goals first
      | exact (disjoint e hL hT).elim
      | simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

/-- Every second logical cache use is a value acquire, in steady code or the tail. -/
theorem readyValueCountAtPrefix {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (index : Nat) :
    let before := (X.tr g).take index
    before.countP (readyAtSite 1) + before.countP (readyAtSite 3) =
      (before.filterMap readyEvent).length/2 := by
  let before := (X.tr g).take index
  let tags := before.filterMap readyEventTagged
  obtain ⟨suffix,hSplit⟩ := List.take_prefix index (X.tr g)
  have hPrefix : ((X.tr g).filterMap readyEventTagged).take tags.length = tags := by
    rw [← hSplit,List.filterMap_append]
    simp [tags,before]
  have hSequence := rawTaggedReadySequence hp hX hg hw
  have hCount := taggedValueCount (hPrefix ▸ taggedPrefix hSequence tags.length)
  rw [Nat.zero_add,Nat.zero_div,Nat.sub_zero] at hCount
  change tags.countP _ = tags.length/2 at hCount
  dsimp only
  rw [← valueReadyProjection]
  simpa only [tags,before,← taggedProjectionErase,List.length_map] using hCount

private theorem rawReadySequence {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) :
    ReadySequence l g 0 ((X.tr g).filterMap readyEvent) := by
  rw [← taggedProjectionErase]
  exact (rawTaggedReadySequence hp hX hg hw).erase

private theorem readyOperandsOfPoll {g index parity : Nat} {slot : Fin 3} {acq : Bool}
    {scope : MbarScope} (hw : warpIndex l g = 12) (h : ReadyPoll l X g index slot parity acq scope)
    :
    ∃ e, X.get (g, index) = some e ∧ readyEvent e = some (readyObject l g slot, parity) := by
  obtain ⟨⟨pc, kind⟩, he, hk⟩ := h
  dsimp only at hk
  subst kind
  exact ⟨_, he, by simp [readyEvent, readyWaitPc hp hX hw slot he]⟩


omit hp hX in
private theorem taggedSequenceGet {l : Launch} {g use index pc : Nat}
    {es : List (Nat × (Loc × Nat))} {value : Loc × Nat}
    (hs : TaggedReadySequence l g use es) (he : es[index]? = some (pc, value)) :
    ReadyUseSite (use + index) pc := by
  induction hs generalizing index with
  | nil => simp at he
  | @next use site rest hSite _ ih =>
    cases index with
    | zero =>
      have hPc : site = pc := congrArg Prod.fst (Option.some.inj he)
      simpa only [hPc, Nat.add_zero] using hSite
    | succ index =>
      rw [List.getElem?_cons_succ] at he
      simpa only [Nat.add_assoc, Nat.add_comm 1] using ih he

/-- The actual poll's ordinal determines whether its gate is a K or a V gate. -/
theorem ReadyPoll.useSite {g index parity : Nat} {slot : Fin 3} {acq : Bool} {scope : MbarScope}
    (hw : warpIndex l g = 12) (hPoll : ReadyPoll l X g index slot parity acq scope) :
    ∃ pc, X.get (g,index) = some ⟨pc, .wait (readyObject l g slot) parity true acq scope⟩ ∧
      ReadyUseSite (((X.tr g).take index).filterMap readyEvent).length pc := by
  obtain ⟨e, he, hReady⟩ := readyOperandsOfPoll hp hX hw hPoll
  obtain ⟨f, hf, hKind⟩ := hPoll
  have hf' : f = e := Option.some.inj (hf.symm.trans he)
  subst f
  have hTagged : readyEventTagged e = some (e.pc, (readyObject l g slot, parity)) := by
    simp [readyEventTagged, hReady]
  let before := (X.tr g).take index
  let suffix := (X.tr g).drop index
  have hGet : suffix[0]? = some e := by
    rw [List.getElem?_drop, Nat.add_zero]
    exact he
  have hIndexed : (suffix.filterMap readyEventTagged)[0]? =
      some (e.pc, (readyObject l g slot, parity)) := by
    cases hp : suffix with
    | nil => simp [hp] at hGet
    | cons first rest =>
      obtain rfl : first = e := Option.some.inj (by simpa [hp] using hGet)
      simp [hTagged]
  have hAt : ((X.tr g).filterMap readyEventTagged)[(before.filterMap readyEventTagged).length]? =
      some (e.pc, (readyObject l g slot, parity)) := by
    conv_lhs => rw [← List.take_append_drop index (X.tr g), List.filterMap_append]
    rw [List.getElem?_append_right (by rfl), Nat.sub_self]
    exact hIndexed
  have hSite := taggedSequenceGet
    (rawTaggedReadySequence hp hX (event_thread_lt hX he) hw) hAt
  have hCount : (before.filterMap readyEventTagged).length = (before.filterMap readyEvent).length :=
    (List.length_map (f := Prod.snd)).symm.trans
      (congrArg List.length (taggedProjectionErase before))
  rw [Nat.zero_add, hCount] at hSite
  cases e
  simp only at hKind
  subst_vars
  exact ⟨_, he, hSite⟩

omit hp hX in
private theorem sequenceGet {l : Launch} {g use index : Nat} {es : List (Loc × Nat)}
    {value : Loc × Nat} (hs : ReadySequence l g use es) (he : es[index]? = some value) :
    value = readyOperand l g (use + index) := by
  induction hs generalizing index with
  | nil => simp at he
  | @next use rest hSeq ih =>
    cases index with
    | zero => simpa using (Option.some.inj he).symm
    | succ index =>
      rw [List.getElem?_cons_succ] at he
      have hIndex : use + 1 + index = use + (index + 1) := by omega
      simpa only [hIndex] using ih he

/-- A successful observation in the decoded ready projection names a physical K/V slot. -/
theorem readySlotOfProjection {g j : Nat} {e : Event} {loc : Loc} {parity : Nat}
    (hw : warpIndex l g = 12) (he : X.get (g, j) = some e)
    (hMark : readyEvent e = some (loc, parity)) :
    ∃ slot : Fin 3, loc = readyObject l g slot := by
  have hEvent : e ∈ X.tr g := List.mem_of_getElem? he
  have hReady : (loc, parity) ∈ (X.tr g).filterMap readyEvent :=
    List.mem_filterMap.mpr ⟨e, hEvent, hMark⟩
  obtain ⟨i, hi, hGet⟩ := List.getElem_of_mem hReady
  have hAt : ((X.tr g).filterMap readyEvent)[i]? = some (loc, parity) := by
    rw [List.getElem?_eq_getElem hi]
    exact congrArg some hGet
  have hOperand := sequenceGet (rawReadySequence hp hX (event_thread_lt hX he) hw) hAt
  exact ⟨readyStage i, by
    simpa only [Nat.zero_add, readyOperand, readyObject] using congrArg Prod.fst hOperand⟩

omit hp hX in
private theorem readyObjectInjective (l : Launch) (g : Nat) :
    Function.Injective (readyObject l g) := by
  intro a b he
  change initObject l (g / l.block) (readySlot a) =
    initObject l (g / l.block) (readySlot b) at he
  rw [readySlot_address, readySlot_address] at he
  have ha := congrArg Loc.addr he
  change l.sharedBase + 8 * a.val + 32 = l.sharedBase + 8 * b.val + 32 at ha
  exact Fin.ext (by omega)

private theorem eventIsPollOfProjection {g index : Nat} {e : Event} (hw : warpIndex l g = 12)
    (he : X.get (g, index) = some e) (slot : Fin 3) :
    okPoll (readyObject l g slot) e =
      ((readyEvent e).map (fun operand => decide (operand.1 = readyObject l g slot))).getD
        false := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try rfl
  case wait loc parity ok acquire scope =>
    cases ok
    · rfl
    · by_cases hLoc : loc = readyObject l g slot
      · subst loc
        have hPc := readyWaitPc hp hX hw slot he
        simp [okPoll, sourceWaitSuccess, readyEvent, hPc]
      · simp only [readyEvent]
        split <;> simp [okPoll, sourceWaitSuccess, hLoc]

omit hp hX in
private theorem countAllReady {l : Launch} {g : Nat} (es : List (Loc × Nat))
    (hOperand : ∀ e ∈ es, ∃ slot : Fin 3, e.1 = readyObject l g slot) :
    es.length = es.countP (fun x => decide (x.1 = readyObject l g 0)) +
      es.countP (fun x => decide (x.1 = readyObject l g 1)) +
      es.countP (fun x => decide (x.1 = readyObject l g 2)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨slot, hLoc⟩ := hOperand e (by simp)
    have hEq (i : Fin 3) : (readyObject l g slot = readyObject l g i) ↔ slot = i :=
      (readyObjectInjective l g).eq_iff
    have hLen := ih (fun v hv => hOperand v (List.mem_cons_of_mem _ hv))
    simp only [List.length_cons, List.countP_cons, hLoc, hEq]
    fin_cases slot <;> simp <;> omega

omit hp hX in
private theorem readySequenceSlotCount {l : Launch} {g use : Nat} {es : List (Loc × Nat)}
    (hs : ReadySequence l g use es) {n : Nat} (hn : n ≤ es.length) (slot : Fin 3) :
    (use + (2 - slot.val)) / 3 +
        (es.take n).countP (fun x => decide (x.1 = readyObject l g slot)) =
      (use + n + (2 - slot.val)) / 3 := by
  induction hs generalizing n with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hn
    subst n
    rfl
  | @next use tail hs ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hn' : n ≤ tail.length := by simp only [List.length_cons] at hn; omega
      have hRest := ih hn'
      have hEq : (readyOperand l g use).1 = readyObject l g (readyStage use) := rfl
      have hInjective : readyObject l g (readyStage use) = readyObject l g slot ↔
          readyStage use = slot := (readyObjectInjective l g).eq_iff
      have hVal : (readyStage use).val = use % 3 := rfl
      have hLt := slot.isLt
      simp only [List.take_succ_cons, List.countP_cons, hEq, hInjective, decide_eq_true_eq]
      by_cases hSame : readyStage use = slot
      · have hSlot := (congrArg Fin.val hSame).symm.trans hVal
        rw [ite_eq_left hSame]
        omega
      · have hSlot : use % 3 ≠ slot.val := fun h => hSame (Fin.ext (hVal.trans h))
        rw [ite_eq_right hSame]
        omega

private theorem readyCountsAtPrefix {g index : Nat} (hw : warpIndex l g = 12) (i : Fin 3) :
    (((X.tr g).take index).filterMap readyEvent).countP
      (fun x => decide (x.1 = readyObject l g i)) = (atPrefix l X g index).kvAcquires i := by
  let pre := (X.tr g).take index
  change _ = (summary l g pre).kvAcquires i
  rw [kvAcquireCount, okPolls, List.countP_filterMap]
  apply List.countP_congr
  intro ev hv
  have hm := (List.take_sublist index (X.tr g)).subset hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
  have hh := eventIsPollOfProjection hp hX hw
    (show X.get (g, j) = some (X.tr g)[j] from List.getElem?_eq_getElem hj) i
  simpa only [Observation.readyObject] using Iff.of_eq (congrArg (· = true) hh.symm)

/-- The abstract ring cursor counts exactly the successful ready events from the actual prefix. -/
theorem readyUsesAtPrefix {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (index : Nat) :
    let state := atPrefix l X g index
    (((X.tr g).take index).filterMap readyEvent).length =
      state.kvAcquires 0 + state.kvAcquires 1 + state.kvAcquires 2 := by
  let es := ((X.tr g).take index).filterMap readyEvent
  have hEach : ∀ pair ∈ es, ∃ i : Fin 3, pair.1 = readyObject l g i := by
    intro pair hMem
    obtain ⟨e,he,hMark⟩ := List.mem_filterMap.mp hMem
    have hFull := (List.take_sublist index (X.tr g)).subset he
    have ha : pair ∈ (X.tr g).filterMap readyEvent := List.mem_filterMap.mpr ⟨e,hFull,hMark⟩
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem ha
    have h := sequenceGet (rawReadySequence hp hX hg hw) (List.getElem?_eq_getElem hj)
    exact ⟨readyStage j, by
      simpa only [Nat.zero_add,readyOperand,readyObject] using congrArg Prod.fst h⟩
  have hCount := countAllReady es hEach
  dsimp only [es] at hCount
  rw [readyCountsAtPrefix hp hX hw 0,readyCountsAtPrefix hp hX hw 1,
    readyCountsAtPrefix hp hX hw 2] at hCount
  exact hCount

/-- The first earlier ready event is the slot-zero acquire. Therefore the
first slot-one acquire observes local generation zero. -/
theorem initialValueReadyPhaseZero {g index : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 12)
    (hOne : (((X.tr g).take index).filterMap readyEvent).length = 1) :
    (atPrefix l X g index).kvAcquires 1 = 0 := by
  obtain ⟨operand,hOnly⟩ := List.length_eq_one_iff.mp hOne
  obtain ⟨suffix,hPrefix⟩ := List.take_prefix index (X.tr g)
  have hFirst : ((X.tr g).filterMap readyEvent)[0]? = some operand := by
    rw [← hPrefix,List.filterMap_append,hOnly]
    rfl
  have hSlot := sequenceGet (rawReadySequence hp hX hg hWarp) hFirst
  rw [← readyCountsAtPrefix hp hX hWarp 1,hOnly,hSlot]
  have hDifferent : readyObject l g 0 ≠ readyObject l g 1 :=
    (readyObjectInjective l g).ne (by decide)
  have hObj : (readyOperand l g (0+0)).1 = readyObject l g 0 := rfl
  simp only [List.countP_cons,List.countP_nil,hObj,decide_eq_false hDifferent,
    Bool.false_eq_true,ite_false,
    Nat.zero_add]

/-- The accepted ready poll uses the slot and parity selected by the total earlier
successful acquisitions of this actual MMA lane. -/
theorem readyOperandAtPrefix {g index parity : Nat} (hw : warpIndex l g = 12) {slot : Fin 3}
    {acquire : Bool} {scope : MbarScope} (hPoll : ReadyPoll l X g index slot parity acquire scope) :
    let d := atPrefix l X g index
    let use := d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2
    slot.val = use % 3 ∧ parity = use / 3 % 2 := by
  dsimp only
  obtain ⟨e, he, hMark⟩ := readyOperandsOfPoll hp hX hw hPoll
  have hg : g < l.threads := event_thread_lt hX he
  have hSeq := rawReadySequence hp hX hg hw
  let pre := (X.tr g).take index
  let op := (readyObject l g slot, parity)
  have hStep : (X.tr g).take (index + 1) = pre ++ [e] := by
    change (X.tr g)[index]? = some e at he
    simp [List.take_add_one, he, pre]
  obtain ⟨post, hPost⟩ := List.take_prefix (index + 1) (X.tr g)
  rw [hStep] at hPost
  have hTrace : (X.tr g).filterMap readyEvent =
      pre.filterMap readyEvent ++ op :: post.filterMap readyEvent := by
    conv_lhs => rw [← hPost]
    simp [hMark, op]
  have hGet : ((X.tr g).filterMap readyEvent)[(pre.filterMap readyEvent).length]? = some op := by
    rw [hTrace, List.getElem?_append_right (by simp)]
    simp
  have hUse := sequenceGet hSeq hGet
  have hTotals := readyUsesAtPrefix hp hX hg hw index
  rw [Nat.zero_add, hTotals] at hUse
  exact ⟨congrArg Fin.val (readyObjectInjective l g (congrArg Prod.fst hUse)),
    congrArg Prod.snd hUse⟩

omit hp hX in
private theorem projectionIndex {α β : Type} (mark : α → Option β)
    {xs : List α} {use : Nat} {b : β} (hb : (xs.filterMap mark)[use]? = some b) :
    ∃ j a, xs[j]? = some a ∧ mark a = some b ∧ ((xs.take j).filterMap mark).length = use := by
  induction xs generalizing use with
  | nil => simp at hb
  | cons a tail ih =>
    cases hMark : mark a with
    | none =>
      obtain ⟨j, e, he, hProj, hUse⟩ := ih (by simpa [hMark] using hb)
      exact ⟨j + 1, e, he, hProj, by simpa [hMark] using hUse⟩
    | some first =>
      cases use with
      | zero =>
        have hEq : first = b := Option.some.inj (by simpa [hMark] using hb)
        exact ⟨0, a, rfl, hEq ▸ hMark, rfl⟩
      | succ use =>
        obtain ⟨j, e, he, hProj, hUse⟩ := ih (by simpa [hMark] using hb)
        exact ⟨j + 1, e, he, hProj, by simp [hMark, hUse]⟩

/-- The actual ready acquire observes the physical slot and its exact generation
selected by the total number of ready uses in the issuing lane's prefix. -/
theorem ReadyPoll.exactOccurrence {g index parity : Nat} (hw : warpIndex l g = 12) {slot : Fin 3}
    {acquire : Bool} {scope : MbarScope} (poll : ReadyPoll l X g index slot parity acquire scope) :
    let d := atPrefix l X g index
    let use := d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2
    slot.val = use % 3 ∧ d.kvAcquires slot = use / 3 ∧ parity = use / 3 % 2 := by
  dsimp only
  obtain ⟨hSlot, hParity⟩ := readyOperandAtPrefix hp hX hw poll
  obtain ⟨_, he, _⟩ := readyOperandsOfPoll hp hX hw poll
  have hg := event_thread_lt hX he
  let xs := ((X.tr g).take index).filterMap readyEvent
  let ys := ((X.tr g).drop index).filterMap readyEvent
  have hSeq : ReadySequence l g 0 (xs ++ ys) := by
    dsimp only [xs, ys]
    rw [← List.filterMap_append, List.take_append_drop]
    exact rawReadySequence hp hX hg hw
  have hCount := readySequenceSlotCount hSeq (n := xs.length) (by simp) slot
  rw [List.take_left, Nat.zero_add, Nat.zero_add] at hCount
  have hBase : (2 - slot.val) / 3 = 0 := by have := slot.isLt; omega
  rw [hBase, Nat.zero_add] at hCount
  change (((X.tr g).take index).filterMap readyEvent).countP _ =
    (xs.length + (2 - slot.val)) / 3 at hCount
  rw [readyCountsAtPrefix hp hX hw slot] at hCount
  let use := (atPrefix l X g index).kvAcquires 0 +
    (atPrefix l X g index).kvAcquires 1 + (atPrefix l X g index).kvAcquires 2
  have hTotal : xs.length = use := readyUsesAtPrefix hp hX hg hw index
  rw [hTotal] at hCount
  change (atPrefix l X g index).kvAcquires slot = (use + (2 - slot.val)) / 3 at hCount
  change slot.val = use % 3 at hSlot
  refine ⟨hSlot, ?_, hParity⟩
  change (atPrefix l X g index).kvAcquires slot = use / 3
  have := slot.isLt
  omega

omit hp hX in
private theorem readyProjectionIsAcquire {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {e : Event}
    {loc : Loc} {parity : Nat}
    (he : X.get (g,j) = some e) (hMark : readyEvent e = some (loc, parity)) :
    e.kind = .wait loc parity true true .cta := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try (solve | cases hMark)
  case wait observed q ok acquire scope =>
    cases ok
    · cases hMark
    simp only [readyEvent] at hMark
    split at hMark
    · rename_i hPc
      have hPair := Option.some.inj hMark
      cases hPair
      obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hPc
      have hSite : (slotWait i).pc = readyHead i := by fin_cases i <;> decide
      have hDecoded : (slotWait i).pc = pc := hSite.trans (beq_iff_eq.mp hi)
      rw [← hDecoded] at he
      obtain ⟨rfl, rfl⟩ := readyGateAcquireFlags hX i he
      rfl
    · cases hMark

/-- The projected ready ordinal of an actual prefix is realized by a CTA acquire
on the lane, at the corresponding physical ring slot and parity. -/
theorem readyPollAtOrdinalBefore {g stop use : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hUse : use < (((X.tr g).take stop).filterMap readyEvent).length) :
    ∃ j < stop, ReadyPoll l X g j (readyStage use) (readyWord use) true .cta ∧
      (((X.tr g).take j).filterMap readyEvent).length = use := by
  let before := (X.tr g).take stop
  let value := (before.filterMap readyEvent)[use]
  have hValue : (before.filterMap readyEvent)[use]? = some value :=
    List.getElem?_eq_getElem hUse
  obtain ⟨j, e, he, hMark, hjUse⟩ := projectionIndex readyEvent hValue
  have hj : j < before.length := (List.getElem?_eq_some_iff.mp he).1
  have hjStop : j < stop := by
    have hLen : before.length = min stop (X.tr g).length := List.length_take
    omega
  have hReal : X.get (g,j) = some e := by
    change ((X.tr g).take stop)[j]? = some e at he
    rw [List.getElem?_take_of_lt hjStop] at he
    exact he
  obtain ⟨suffix, hSuffix⟩ := List.take_prefix stop (X.tr g)
  have hAll : ((X.tr g).filterMap readyEvent)[use]? = some value := by
    rw [← hSuffix, List.filterMap_append, List.getElem?_append_left hUse]
    exact hValue
  have hOperand := sequenceGet (rawReadySequence hp hX hg hw) hAll
  rw [hOperand] at hMark
  have hKind :
      e.kind = .wait (readyObject l g (readyStage use)) (readyWord use) true true .cta := by
    change readyEvent e = some (readyOperand l g (0 + use)) at hMark
    rw [Nat.zero_add] at hMark
    exact readyProjectionIsAcquire hX hReal hMark
  refine ⟨j, hjStop, ⟨e, hReal, hKind⟩, ?_⟩
  simpa [before, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjStop)] using hjUse

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
