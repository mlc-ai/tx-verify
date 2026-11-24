-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
import Kernels.TmlFa4Fwd.Proof.LoaderReusePriming
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.MBarrier
open PTX.Kernels.TmlFa4Fwd.Loader
  (namesReady readyOrdinal kvUseStage kvUseStage_val readySlot_address readySlot
    actualAsyncArrival copyCommitPc reuseArrival loaderStartupAsyncAddress
    laterPublicationIsRecurring)

noncomputable section
open scoped Classical

private def usesBefore (slot : Fin 3) (use : Nat) : Nat :=
  (use + (2-slot.val))/3

private theorem usesBeforeStep (slot : Fin 3) (use : Nat) :
    usesBefore slot (use+1) = usesBefore slot use + if kvUseStage use = slot then 1 else 0 := by
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

private def recurringOn (loc : Loc) (e : Event) : Bool :=
  if recurringPublicationEvent e then namesReady loc e else false

private def primingOn (loc : Loc) (e : Event) : Bool :=
  if recurringPublicationEvent e then false else namesReady loc e

private theorem recurringCountZero (loc : Loc) {es : List Event}
    (h : ∀ e ∈ es, ¬ recurringPublicationEvent e) : es.countP (recurringOn loc) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e he
  simp [recurringOn, h e he]

private theorem readyCountSplit (loc : Loc) (es : List Event) :
    es.countP (namesReady loc) = es.countP (primingOn loc) + es.countP (recurringOn loc) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.countP_cons, ih]
    by_cases h : recurringPublicationEvent e <;> simp only [primingOn, recurringOn, h,
      ite_true, ite_false, Bool.false_eq_true, Nat.add_zero] <;> omega

private theorem recurringCursorMark {l : Launch} {g use : Nat} {site : Fin 4} (slot : Fin 3) :
    recurringOn (readyObject l g slot) (cursorArrival l g use site) =
      decide (kvUseStage use = slot) := by
  have h : recurringPublicationEvent (cursorArrival l g use site) := ⟨site,_,rfl⟩
  rw [recurringOn, ite_eq_left h]
  simp only [cursorArrival, namesReady]
  change decide (readyObject l g (kvUseStage use) = readyObject l g slot) = _
  congr 1
  apply propext
  constructor
  · intro he
    have hLoc := congrArg Loc.addr he
    simp only [readyObject,readySlot_address] at hLoc
    exact Fin.ext (by omega)
  · exact congrArg (readyObject l g)

private theorem PacketsBeforeDrain.recurringCount {l : Launch} {g start final : Nat}
    {es : List Event} (h : PacketsBeforeDrain l g start final es) (slot : Fin 3) :
    es.countP (recurringOn (readyObject l g slot)) + usesBefore slot start =
      usesBefore slot final :=
  by
  let mark := recurringOn (readyObject l g slot)
  induction h with
  | done => simp
  | @gap use fin pre tail hQuiet hNext ih =>
    rw [List.countP_append, recurringCountZero _ (fun e he => (hQuiet e he).1), Nat.zero_add]
    exact ih
  | @packet use fin n site mid tail hQuiet hNext ih =>
    have hPoll (ok : Bool) : mark (cursorPoll l g use site ok) = false := by
      simp [mark,recurringOn,namesReady,cursorPoll]
    let retry := List.replicate n (cursorPoll l g use site false)
    let ok := cursorPoll l g use site true
    let arrive := cursorArrival l g use site
    have hEq : List.replicate n (cursorPoll l g use site false) ++
        cursorPoll l g use site true :: mid ++ cursorArrival l g use site :: tail =
        retry ++ (ok :: (mid ++ arrive :: tail)) := by
      simp [retry,ok,arrive,List.append_assoc]
    have hMid : mid.countP mark = 0 :=
      recurringCountZero (readyObject l g slot) (fun e he => (hQuiet e he).1)
    have hRetry : retry.countP mark = 0 := by simp [retry,hPoll]
    have hOne : mark arrive = decide (kvUseStage use = slot) := recurringCursorMark slot
    have hOk : mark ok = false := hPoll true
    change (_ : List Event).countP mark + _ = _
    rw [hEq,List.countP_append,hRetry,Nat.zero_add,List.countP_cons,hOk]
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
    rw [List.countP_append, hMid, Nat.zero_add, List.countP_cons, hOne]
    simp only [decide_eq_true_eq]
    rw [usesBeforeStep] at ih
    change tail.countP mark + _ = _ at ih
    omega

private theorem primingMarkSource {X : Execution} {g i : Nat} {e : Event}
    {loc : Loc} (he : X.get (g,i) = some e) (hMark : primingOn loc e = true) :
    X.AsyncArrive (g,i) loc true ∧ ¬ recurringPublicationEvent e := by
  have hNo : ¬ recurringPublicationEvent e := by
    intro h
    simp [primingOn,h] at hMark
  rw [primingOn, ite_eq_right hNo] at hMark
  obtain ⟨site,kind⟩ := e
  cases kind <;> simp only [namesReady,Bool.false_eq_true] at hMark
  rename_i target noinc
  cases noinc <;> simp only [Bool.false_eq_true,decide_eq_true_eq] at hMark
  subst target
  exact ⟨⟨site,he⟩,hNo⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem primingOnlyFirstTwo {g i : Nat} {e : Event} {slot : Fin 3}
    (he : X.get (g,i) = some e) (hMark : primingOn (readyObject l g slot) e = true) :
    slot.val < 2 := by
  obtain ⟨⟨pc,hPub⟩,hNo⟩ := primingMarkSource he hMark
  obtain ⟨⟨packet,hPc⟩,_,_,_⟩ := actualAsyncArrival hX hPub
  have hEvent : e = ⟨pc,.asyncArrive (readyObject l g slot) true⟩ :=
    Option.some.inj (he.symm.trans hPub)
  have hAt : pc ∈ [674,904] := by
    fin_cases packet
    · rw [hPc]; decide
    · rw [hPc]; decide
    · exact (hNo (by rw [hEvent,hPc]; exact ⟨0,_,rfl⟩)).elim
    · exact (hNo (by rw [hEvent,hPc]; exact ⟨1,_,rfl⟩)).elim
    · exact (hNo (by rw [hEvent,hPc]; exact ⟨2,_,rfl⟩)).elim
    · exact (hNo (by rw [hEvent,hPc]; exact ⟨3,_,rfl⟩)).elim
  have hOff := congrArg Loc.addr (loaderStartupAsyncAddress hp hX hPub hAt)
  simp only [readyObject,readySlot_address] at hOff
  change l.sharedBase + 8 * slot.val + 32 = l.sharedBase + (if pc = 674 then 32 else 40) at hOff
  split at hOff <;> omega

private theorem primingBudget (g : Nat) (slot : Fin 3) :
    (X.tr g).countP (primingOn (readyObject l g slot)) ≤ usesBefore slot 2 := by
  let mark := primingOn (readyObject l g slot)
  have hUnique (i j : Nat) {a b : Event} (ha : X.get (g,i) = some a)
      (hb : X.get (g,j) = some b) (hma : mark a = true) (hmb : mark b = true) :
      ¬ i < j := by
    intro hLt
    obtain ⟨hA,_⟩ := primingMarkSource ha hma
    obtain ⟨hB,hNo⟩ := primingMarkSource hb hmb
    obtain ⟨site,hLater⟩ := laterPublicationIsRecurring hp hX hLt hA hB
    exact hNo ⟨site,_,Option.some.inj (hb.symm.trans hLater)⟩
  change (X.tr g).countP mark ≤ usesBefore slot 2
  have hBudget : (X.tr g).countP mark ≤ 1 := by
    by_contra! h
    obtain ⟨i,a,ha,hma,hA⟩ :=
      MbarRing.Slot.exists_nth_countP mark (xs := X.tr g) (c := 0) (by omega)
    obtain ⟨j,b,hb,hmb,hB⟩ :=
      MbarRing.Slot.exists_nth_countP mark (xs := X.tr g) (c := 1) (by omega)
    have hLt : i < j := by
      by_contra! hLe
      have hMon := (List.take_sublist_take_left (l := X.tr g) hLe).countP_le (p := mark)
      omega
    exact hUnique i j ha hb hma hmb hLt
  by_cases hSlot : slot.val < 2
  · have h := slot.isLt
    unfold usesBefore
    omega
  have hZero : (X.tr g).countP mark = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hm hMark
    obtain ⟨i,he⟩ := List.mem_iff_getElem?.mp hm
    exact hSlot (primingOnlyFirstTwo hp hX (show X.get (g,i) = some e from he) hMark)
  omega

private theorem actualDrainWithCoverage {g i : Nat} {slot : Fin 3}
    (hPub : X.AsyncArrive (g,i) (readyObject l g slot) true) (hExit : Thread.Exited X g) :
    ∃ seed final pos t front,
      (X.tr g).drop seed = front ++ (X.tr g).drop (seed + front.length) ∧
      PacketsBeforeDrain l g 2 final front ∧ seed + front.length ≤ pos ∧
      At t 1863 (drainCarry l final) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) none ∧
      (X.tr g).countP (namesReady (readyObject l g slot)) ≤ usesBefore slot final := by
  let loc := readyObject l g slot
  have finish {j : Nat} {target : Loc} (hj : X.AsyncArrive (g,j) target true)
      (hQuiet : ∀ seed, (∀ e, X.get (g,j) = some e → recurringPublicationEvent e → seed ≤ j) →
        ∀ e ∈ (X.tr g).take seed, ¬ recurringPublicationEvent e) :
      ∃ seed final pos t front,
        (X.tr g).drop seed = front ++ (X.tr g).drop (seed + front.length) ∧
        PacketsBeforeDrain l g 2 final front ∧ seed + front.length ≤ pos ∧
        At t 1863 (drainCarry l final) ∧
        Run kernel Assumptions.all l g t ((X.tr g).drop pos) none ∧
        (X.tr g).countP (namesReady loc) ≤ usesBefore slot final := by
    obtain ⟨seed,final,pos,_,t,front,hTake,hPackets,hBefore,_,_,ht,hRun,hSeed,hAfter⟩ :=
      actualDrainEntryOfPublication hp hX hj hExit
    have hAll := List.take_append_drop seed (X.tr g)
    rw [hTake, ← List.append_assoc] at hAll
    have hCount : (X.tr g).countP (recurringOn loc) = front.countP (recurringOn loc) := by
      rw [← hAll, List.countP_append, List.countP_append,
        recurringCountZero loc (hQuiet seed hSeed), recurringCountZero loc hAfter]
      simp
    have hSlots := hPackets.recurringCount slot
    have hPriming := primingBudget hp hX g slot
    have hCover : (X.tr g).countP (namesReady loc) ≤ usesBefore slot final := by
      rw [readyCountSplit, hCount]
      exact (Nat.add_le_add_right hPriming _).trans_eq (by simpa [loc,Nat.add_comm] using hSlots)
    exact ⟨seed,final,pos,t,front,hTake,hPackets,hBefore,ht,hRun,hCover⟩
  by_cases hSome : ∃ j, ∃ e, X.get (g,j) = some e ∧ recurringPublicationEvent e
  · let first := Nat.find hSome
    obtain ⟨e,he,hRec⟩ := Nat.find_spec hSome
    obtain ⟨site,target,rfl⟩ := hRec
    have hRec : recurringPublicationEvent ⟨reuseArrival site,.asyncArrive target true⟩ :=
      ⟨site,target,rfl⟩
    exact finish (j := first) (target := target) ⟨_,he⟩ (by
      intro seed hSeed a ha hRec'
      obtain ⟨j,hJ⟩ := List.mem_iff_getElem?.mp ha
      have hLt : j < seed := by have := (List.getElem?_eq_some_iff.mp hJ).1; simp at this; omega
      rw [List.getElem?_take_of_lt hLt] at hJ
      have hMin := Nat.find_min' hSome (show ∃ e, X.get (g,j) = some e ∧ recurringPublicationEvent e
        from ⟨a,hJ,hRec'⟩)
      have hLe := hSeed _ he hRec
      omega)
  exact finish hPub (by
    intro seed _ e hm hRec
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hm)
    exact hSome ⟨j,e,hj,hRec⟩)

/-- Every actual ready publication on an exited lane precedes a successful final
empty acquire covering its own generation. -/
theorem publicationObservedThroughDrain {g i : Nat} {slot : Fin 3}
    (hPub : X.AsyncArrive (g,i) (readyObject l g slot) true) (hExit : Thread.Exited X g) :
    ∃ (wait finish index phase : Nat) (r : Record Ref),
      (X.objects (emptyObject l g slot))[index]? = some r ∧ r.id = .thread (g,wait) ∧
      r.reply.waited = some true ∧
      observedAt (X.objects (emptyObject l g slot)) index = some phase ∧
      (atPrefix l X g i).published.countP (fun pub => pub.slot == slot) ≤ phase ∧
      Resumes kernel X (g,wait) (g,finish) ∧ OwnerExit l X (g / l.block) (g,finish) := by
  obtain ⟨seed,final,pos,t,front,hTake,hPackets,hBefore,ht,hRun,hCoverage⟩ :=
    actualDrainWithCoverage hp hX hPub hExit
  let mark := namesReady (readyObject l g slot)
  have hCount : ((X.tr g).take i).countP mark < usesBefore slot final := by
    obtain ⟨pc,he⟩ := hPub
    have hOne : mark ⟨pc,.asyncArrive (readyObject l g slot) true⟩ = true := by
      simp [mark,namesReady]
    have hPrior : ((X.tr g).take (i+1)).countP mark =
        ((X.tr g).take i).countP mark + 1 := by
      rw [List.take_add_one, show (X.tr g)[i]? = _ from he]
      simp [List.countP_append,hOne]
    have hLen := (List.getElem?_eq_some_iff.mp he).1
    have hAll := (List.take_sublist (i+1) (X.tr g)).countP_le (p := mark)
    change (X.tr g).countP mark ≤ usesBefore slot final at hCoverage
    omega
  have hPos : 0 < usesBefore slot final := by omega
  obtain ⟨wait,finish,index,phase,r,hAt,hId,hSuccess,hSeen,hPhase,hResume,hOwner⟩ :=
    drainObservedOfCursor hp hX hTake hPackets hBefore ht hRun hExit slot hPos
  refine ⟨wait,finish,index,phase,r,hAt,hId,hSuccess,hSeen,?_,hResume,hOwner⟩
  rw [publicationOrdinalAtObject hp hX hPub]
  change ((X.tr g).take i).countP mark ≤ phase
  change usesBefore slot final ≤ phase+1 at hPhase
  omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
