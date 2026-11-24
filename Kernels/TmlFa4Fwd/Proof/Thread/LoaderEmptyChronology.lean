-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.Flow PTX.EventFrame PTX.MBarrier
open PTX.Kernels.TmlFa4Fwd.Thread.Mma.Observation (emptyObject)
open PTX.Kernels.TmlFa4Fwd.Loader
  (reuseEntry reuseArrival loaderSliceEvents recurringPacketSite copyCommitPc packetArrivalStep
    actualReuseCheckpoint reuseEmptyPrefixFromCheckpoint recurringGuardOfEmptyPrefix
    laterPublicationIsRecurring actualAsyncArrival readySlot readySlot_address
    loaderStartupAsyncAddress)

noncomputable section

private theorem uniqueReusePc (site : Fin 4) {pc : Nat}
    (hSite : pc ∈ [674, 904, 1137, 1342, 1602, 1735])
    (hRange : reuseEntry site ≤ pc ∧ pc < reuseArrival site + 1) :
    pc = reuseArrival site := by
  have hTable : ([674, 904, 1137, 1342, 1602, 1735] : List Nat).all
      (fun p => decide ((reuseEntry site ≤ p ∧ p < reuseArrival site + 1) →
        p = reuseArrival site)) = true := by
    fin_cases site <;> decide
  exact of_decide_eq_true (List.all_eq_true.mp hTable pc hSite) hRange

private theorem sliceConsOfIn {l : Launch} {g : Nat} {t : TState} {ev : Option Event}
    {tail : List Visit} (site : Fin 4)
    (hIn : reuseEntry site ≤ t.pc ∧ t.pc < reuseArrival site + 1) :
    loaderSliceEvents (reuseEntry site) (reuseArrival site + 1)
      (visit kernel l g t ev :: tail) =
      ev.toList ++ loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) tail := by
  unfold loaderSliceEvents
  rw [List.takeWhile_cons_of_pos]
  · cases ev <;> rfl
  simp only [visit_pc, Bool.and_eq_true]
  exact ⟨decide_eq_true hIn.1, decide_eq_true hIn.2⟩

private theorem sliceNilOfOutside {head : Visit} {tail : List Visit} (site : Fin 4)
    (hOutside : ¬ (reuseEntry site ≤ head.pc ∧ head.pc < reuseArrival site + 1)) :
    loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) (head :: tail) = [] := by
  unfold loaderSliceEvents
  rw [List.takeWhile_cons_of_neg]
  · rfl
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hOutside

private theorem noSecondSlicePublication {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (site : Fin 4)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSites : ∀ e ∈ es, ∀ loc, e.kind = .asyncArrive loc true →
      e.pc ∈ [674, 904, 1137, 1342, 1602, 1735])
    {a b : Event} {x y : Loc} {i j : Nat}
    (ha : (loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs)[i]? = some a)
    (hb : (loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs)[j]? = some b)
    (hA : a.kind = .asyncArrive x true) (_hB : b.kind = .asyncArrive y true)
    (hOrder : i < j) : False := by
  induction hw generalizing i j with
  | stop => simp [loaderSliceEvents] at ha
  | @tau t u es vs h hw ih =>
    by_cases hIn : reuseEntry site ≤ t.pc ∧ t.pc < reuseArrival site + 1
    · rw [sliceConsOfIn site hIn] at ha hb
      exact ih hSites ha hb hOrder
    · rw [sliceNilOfOutside site (by simpa only [visit_pc] using hIn)] at ha
      simp at ha
  | @last t ev he =>
    by_cases hIn : reuseEntry site ≤ t.pc ∧ t.pc < reuseArrival site + 1
    · rw [sliceConsOfIn site hIn] at hb
      have hJ := (List.getElem?_eq_some_iff.mp hb).1
      simp [loaderSliceEvents] at hJ
      omega
    · rw [sliceNilOfOutside site (by simpa only [visit_pc] using hIn)] at ha
      simp at ha
  | @ev t u ev es vs he hw ih =>
    by_cases hIn : reuseEntry site ≤ t.pc ∧ t.pc < reuseArrival site + 1
    · have hThis := sliceConsOfIn (l := l) (g := g) (ev := some ev) (tail := vs) site hIn
      rw [hThis] at ha hb
      cases i with
      | zero =>
        obtain rfl := Option.some.inj ha
        have hPc := estep_source_pc he
        have hSrc := uniqueReusePc site (hSites ev (by simp) x hA) (hPc ▸ hIn)
        have hT : t.pc = copyCommitPc (recurringPacketSite site) + 1 := hPc.symm.trans hSrc
        obtain ⟨_, _, hu⟩ := packetArrivalStep (recurringPacketSite site) hT he
        have hNone : loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs = [] := by
          cases vs with
          | nil => rfl
          | cons first rest =>
            have hOut : ¬ first.pc < reuseArrival site + 1 := by
              rw [hw.zero_pc rfl, hu]
              exact Nat.lt_irrefl _
            unfold loaderSliceEvents
            rw [List.takeWhile_cons_of_neg]
            · rfl
            · simp [hOut]
        have hJ := (List.getElem?_eq_some_iff.mp hb).1
        simp [hNone] at hJ
        omega
      | succ i =>
        cases j with
        | zero => omega
        | succ j =>
          exact ih (fun e he => hSites e (List.mem_cons_of_mem _ he)) ha hb (by omega)
    · rw [sliceNilOfOutside site (by simpa only [visit_pc] using hIn)] at ha
      simp at ha

private theorem earlierBeforePacket {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (site : Fin 4)
    {g start index : Nat} {s : TState} {vs : List Visit} {loc : Loc}
    (hw : Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs)
    (hSeen : (loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs)[index - start]? =
      some ⟨reuseArrival site, .asyncArrive loc true⟩)
    {prior : Nat} {priorLoc : Loc} (hlt : prior < index)
    (he : X.AsyncArrive (g, prior) priorLoc true) : prior < start := by
  by_contra! hAfter
  let slice := loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs
  have hPrefix : slice <+: (X.tr g).drop start := by
    rw [hw.events]
    exact (List.takeWhile_prefix _).filterMap Visit.ev
  obtain ⟨pc, hOld⟩ := he
  have hGet : ((X.tr g).drop start)[prior - start]? = some ⟨pc, .asyncArrive priorLoc true⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hAfter]
    exact hOld
  have hJ : index - start < slice.length := (List.getElem?_eq_some_iff.mp hSeen).1
  have hI : prior - start < slice.length := by omega
  have hOldSlice : slice[prior - start]? = some ⟨pc, .asyncArrive priorLoc true⟩ := by
    rw [List.getElem?_eq_getElem hI, hPrefix.getElem hI]
    exact (List.getElem?_eq_getElem (hI.trans_le hPrefix.length_le)).symm.trans hGet
  have hSites : ∀ e ∈ (X.tr g).drop start, ∀ loc, e.kind = .asyncArrive loc true →
      e.pc ∈ [674, 904, 1137, 1342, 1602, 1735] := by
    intro e hmem target hKind
    obtain ⟨pos, hPos, rfl⟩ := List.getElem_of_mem hmem
    have hh : ((X.tr g).drop start)[pos]? = some ((X.tr g).drop start)[pos] :=
      List.getElem?_eq_getElem hPos
    rw [List.getElem?_drop] at hh
    change X.get (g, start + pos) = _ at hh
    generalize hhEv : ((X.tr g).drop start)[pos] = event at hh hKind ⊢
    obtain ⟨pc, kind⟩ := event
    dsimp only at hKind ⊢
    subst kind
    obtain ⟨⟨site, rfl⟩, _, _, _⟩ := actualAsyncArrival hX hh
    fin_cases site <;> decide
  exact noSecondSlicePublication site hw hSites hOldSlice hSeen rfl rfl (by omega)

/-- A reuse checkpoint is later than all prior publications of the same loader lane. -/
structure OrderedGuardedReuse (l : Launch) (X : Execution) (publication : EvId) (slot : Fin 3)
    extends GuardedReuse l X publication slot where
  issuer : acquire.1 = publication.1
  before : acquire.2 < publication.2
  afterEarlier : ∀ (i : Nat) (loc : Loc), i < publication.2 →
    X.AsyncArrive (publication.1, i) loc true → i < acquire.2

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem orderedRecurringGuard {owner : Nat} {publication : EvId} {slot : Fin 3}
    (hPub : RecurringPublication X publication (readyObject l owner slot)) :
    Nonempty (OrderedGuardedReuse l X publication slot) := by
  obtain ⟨g, index⟩ := publication
  obtain ⟨site, he⟩ := hPub
  obtain ⟨stage, start, s, vs, hStart, hs, hw, hTarget⟩ := actualReuseCheckpoint hp hX site he
  obtain ⟨n, phase, rest, _, hLoc, hPrefix⟩ :=
    reuseEmptyPrefixFromCheckpoint hp site stage hs hw (List.mem_of_getElem? hTarget)
  obtain ⟨wait, copy, hWait, hPoll, hGuard, hTrack⟩ :=
    recurringGuardOfEmptyPrefix hp hX site stage he hStart hPrefix
  have hAddr := congrArg Loc.addr hLoc
  change (Prologue.initObject l (owner / l.block) (readySlot slot)).addr =
    (Prologue.initObject l (g / l.block) (readySlot stage)).addr at hAddr
  rw [readySlot_address, readySlot_address] at hAddr
  simp only at hAddr
  have hSlot : slot = stage := Fin.ext (by omega)
  subst stage
  have hWa := hGuard.1.2.1
  have hCp := hTrack.2.1
  refine ⟨⟨⟨(g, wait), (g, copy), phase, ⟨_, hPoll, rfl⟩, hGuard, hTrack⟩,
    rfl, by change wait < index; omega, ?_⟩⟩
  intro i loc hLt hOld
  exact (earlierBeforePacket hX site hw hTarget hLt hOld).trans_le hWait

/-- Every positive-slot publication has a guard after its lane's earlier publications. -/
theorem positiveGenerationOrderedGuard {owner : Nat} {publication : EvId} {slot : Fin 3}
    (he : X.AsyncArrive publication (readyObject l owner slot) true)
    (hOrdinal : 0 < (atPrefix l X publication.1 publication.2).published.countP
      (fun pub => pub.slot == slot)) :
    Nonempty (OrderedGuardedReuse l X publication slot) := by
  obtain ⟨i, hi, hpast, _⟩ := earlierPublication hp hX he hOrdinal
  exact orderedRecurringGuard hp hX (laterPublicationIsRecurring hp hX hi hpast he)

/-- A publication of ordinal `n + 1` observes at least phase `n` when its guard has
at least that many earlier successful acquisitions, including the initially free use.
Every slot starts with free parity. -/
theorem OrderedGuardedReuse.observedLowerOfPrefix {publication : EvId} {slot : Fin 3} {n : Nat}
    (h : OrderedGuardedReuse l X publication slot)
    (hCount : n + 1 ≤ emptyOrdinal l X h.acquire slot)
    (hAlt : AlternatesEmptyThrough l X publication.1 publication.2 slot 1) :
    ∃ (j phase : Nat) (r : Record Ref),
      let log := X.objects (emptyObject l h.acquire.1 slot)
      log[j]? = some r ∧ r.id = .thread h.acquire ∧ r.fault = none ∧
        r.reply.waited = some true ∧ observedAt log j = some phase ∧ n ≤ phase := by
  have hUntil : AlternatesEmptyThrough l X h.acquire.1 h.acquire.2 slot 1 := by
    have hAlt' : AlternatesEmptyThrough l X h.acquire.1 publication.2 slot 1 :=
      h.issuer.symm ▸ hAlt
    intro i e q acq scope hi he hw
    exact hAlt' i e q acq scope (hi.trans h.before.le) he hw
  obtain ⟨j, phase, r, hj, hid, hf, hSuccess, hObs, hPhase⟩ :=
    h.empty.observedAtLeastOfPrefix hp hX (by decide) hUntil (by omega)
  exact ⟨j, phase, r, hj, hid, hf, hSuccess, hObs, by omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
