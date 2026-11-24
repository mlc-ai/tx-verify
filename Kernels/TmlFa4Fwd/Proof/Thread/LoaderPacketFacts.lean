-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderTransitions
public import Kernels.TmlFa4Fwd.Proof.LoaderCommittedPacket
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.LoaderPacketContinuity

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- A reachable body of one ordinary K/V packet, up to its decoded commit. -/
def PacketBody (l : Launch) (g : Nat) (packet : Packet) (events : List Event) : Prop :=
  ∃ (site : Fin 6) (t : TState) (es : List Event) (visits : List Visit),
    DecodedObservation.packetOfSite site = packet ∧
    t.pc = copyPacketFirst site ∧ Walk kernel Assumptions.all l g t es visits ∧
    (∃ v ∈ visits, v.pc = copyCommitPc site) ∧
    events = (visits.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev

/-- Read the ordinary copy vectors, in issue order, from event observations. -/
def vectorOf (e : Event) : Option AsyncCopy.Spec :=
  match e.kind with
  | .copy spec => some spec
  | _ => none

theorem packetBodyVectors {l : Launch} {g : Nat} {packet : Packet} {events : List Event}
    (h : PacketBody l g packet events) : (events.filterMap vectorOf).length = 32 := by
  obtain ⟨site, _, _, _, _, hStart, hw, hReach, rfl⟩ := h
  rw [List.length_filterMap_eq_countP]
  have hPred : (fun e => (vectorOf e).isSome) = loaderCopyEvent := by
    funext e
    obtain ⟨_, kind⟩ := e
    cases kind <;> rfl
  rw [hPred]
  exact loaderPacketCopiesAtCommit hw hStart hReach

/-- The ordinary copy issues of one actual publication, in issue order.
The first and commit fields are positions in the lane's event trace. -/
structure PublishedCopyGroup (l : Launch) (X : Execution) (issue : EvId) where
  publication : Publication
  published : (atPrefix l X issue.1 (issue.2 + 1)).published =
    publication :: (atPrefix l X issue.1 issue.2).published
  first : Nat
  commit : Nat
  closesAt : commit + 1 = issue.2
  copies : List (Nat × AsyncCopy.Spec)
  committed : (atPrefix l X issue.1 issue.2).lastCommit =
    some ⟨publication.packet, copies.map Prod.snd⟩
  count : copies.length = 32
  ordered : copies.Pairwise (fun a b => a.1 < b.1)
  noWait : ∀ {j : Nat} {ev : Event} {loc parity ok acquire scope},
    first ≤ j → j < commit → X.get (issue.1, j) = some ev →
      ev.kind ≠ .wait loc parity ok acquire scope
  member : ∀ j spec, (j, spec) ∈ copies ↔
    first ≤ j ∧ j < commit ∧ X.Copy (issue.1, j) spec
  sameGroup : ∀ {i j a b}, (i, a) ∈ copies → (j, b) ∈ copies → i < j →
    SameAsyncGroup X (issue.1, i) (issue.1, j)

/-- The indices of the machine's committed issues are strictly increasing. -/
theorem PublishedCopyGroup.nodup {l : Launch} {X : Execution} {issue : EvId}
    (group : PublishedCopyGroup l X issue) : group.copies.Nodup :=
  group.ordered.imp fun h hEq => (Nat.ne_of_lt h) (congrArg Prod.fst hEq)

private def indexedCopies (first : Nat) (events : List Event) : List (Nat × AsyncCopy.Spec) :=
  (events.zipIdx first).filterMap fun (e, j) => (vectorOf e).map (j, ·)

private theorem indexedCopiesVectors (first : Nat) (events : List Event) :
    (indexedCopies first events).map Prod.snd = events.filterMap vectorOf := by
  induction events generalizing first with
  | nil => rfl
  | cons e es ih =>
    simp only [indexedCopies, List.zipIdx_cons, List.filterMap_cons] at ih ⊢
    cases vectorOf e <;> simp [ih]

private theorem memIndexedCopies {first j : Nat} {events : List Event} {spec : AsyncCopy.Spec} :
    (j, spec) ∈ indexedCopies first events ↔
      first ≤ j ∧ ∃ e, events[j - first]? = some e ∧ e.kind = .copy spec := by
  simp only [indexedCopies, List.mem_filterMap]
  constructor
  · rintro ⟨⟨e, k⟩, hMem, hs⟩
    cases hk : e.kind <;> simp [vectorOf, hk] at hs
    case copy s =>
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hle, he⟩ := List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp hMem
      exact ⟨hle, e, he, hk⟩
  · rintro ⟨hle, e, he, hk⟩
    exact ⟨(e, j), List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr ⟨hle, he⟩,
      by simp [vectorOf, hk]⟩

private theorem indexedCopiesOrdered (first : Nat) (events : List Event) :
    (indexedCopies first events).Pairwise (fun a b => a.1 < b.1) := by
  induction events generalizing first with
  | nil => exact List.Pairwise.nil
  | cons e es ih =>
    cases h : vectorOf e with
    | none => simpa [indexedCopies, h] using ih (first + 1)
    | some spec =>
      have hHead : ∀ a ∈ indexedCopies (first + 1) es, first < a.1 := by
        rintro ⟨j, v⟩ hm
        exact (memIndexedCopies.mp hm).1
      have hOrder : ((first, spec) :: indexedCopies (first + 1) es).Pairwise
          (fun a b => a.1 < b.1) := .cons hHead (ih (first + 1))
      simpa [indexedCopies, h] using hOrder

private theorem noncommitPendingCopies {l : Launch} {g : Nat} {d : D} {e : Event}
    (h : e.kind ≠ .asyncCommit) :
    (advance l g d e).pendingCopies = (vectorOf e).toList ++ d.pendingCopies := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try (solve | simp [advance, observe, vectorOf])
  case asyncCommit => exact (h rfl).elim
  case asyncArrive loc noinc =>
    cases noinc
    · simp [advance, observe, vectorOf]
    · cases hp : DecodedObservation.observePacket pc true <;>
        cases hs : DecodedObservation.locateSlot l g loc true <;>
        simp [advance, observe, vectorOf, hp, hs]
  case tensorIssue =>
    cases hp : DecodedObservation.observeInput pc with
    | none => simp [advance, observe, vectorOf, hp]
    | some plane => cases plane <;> simp [advance, observe, vectorOf, hp]
  case wait loc parity ok acq scope =>
    cases ok <;> cases acq <;> cases scope <;>
      try (solve | simp [advance, observe, vectorOf])
    cases hs : DecodedObservation.locateSlot l g loc false <;>
      simp [advance, observe, vectorOf, hs]

private theorem pendingCopiesFold {l : Launch} {g : Nat} (d : D) (es : List Event)
    (h : ∀ e ∈ es, e.kind ≠ .asyncCommit) :
    (es.foldl (advance l g) d).pendingCopies =
      (es.filterMap vectorOf).reverse ++ d.pendingCopies := by
  induction es generalizing d with
  | nil => rfl
  | cons e es ih =>
    have hr : ∀ f ∈ es, f.kind ≠ .asyncCommit := fun f hf => h f (List.mem_cons_of_mem _ hf)
    rw [List.foldl_cons, ih _ hr, noncommitPendingCopies (h e (by simp)), List.filterMap_cons]
    cases vectorOf e <;> simp [List.append_assoc]

private theorem pendingEmptyOfSeparation {l : Launch} {X : Execution} {g n : Nat}
    (hn : n ≤ (X.tr g).length)
    (hSeparated : ∀ i < n, ∀ spec, X.Copy (g, i) spec →
      ∃ j e packet, i < j ∧ j < n ∧ X.get (g, j) = some e ∧
        observe l g e = .commit packet) :
    (atPrefix l X g n).pendingCopies = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hLt : n < (X.tr g).length := by omega
    let e := (X.tr g)[n]
    have he : X.get (g, n) = some e := List.getElem?_eq_getElem hLt
    rw [prefixStep he]
    by_cases hCommit : ∃ packet, observe l g e = .commit packet
    · obtain ⟨packet, hp⟩ := hCommit
      exact (advanceCommit hp).1
    have hNoCopy : vectorOf e = none := by
      cases hk : e.kind <;> simp [vectorOf, hk]
      case copy spec =>
        have hEq : e = ⟨e.pc, .copy spec⟩ := congrArg (Event.mk e.pc) hk
        have hc : X.Copy (g, n) spec := ⟨e.pc, hEq ▸ he⟩
        obtain ⟨j, _, _, hj, hLt, _, _⟩ := hSeparated n (by omega) spec hc
        omega
    have hKeep : (advance l g (atPrefix l X g n) e).pendingCopies =
        (atPrefix l X g n).pendingCopies := by
      by_cases hk : e.kind = .asyncCommit
      · obtain ⟨pc, kind⟩ := e
        change kind = .asyncCommit at hk
        subst kind
        cases hPacket : DecodedObservation.observePacket pc false with
        | none => simp [advance, observe, hPacket]
        | some packet => exact (hCommit ⟨packet, by simp [observe, hPacket]⟩).elim
      · rw [noncommitPendingCopies hk, hNoCopy]
        rfl
    rw [hKeep]
    apply ih (by omega)
    intro i hi spec hc
    obtain ⟨j, event, packet, hij, hj, hGet, hObs⟩ := hSeparated i (by omega) spec hc
    have hNe : j ≠ n := by
      rintro rfl
      obtain rfl := Option.some.inj (he.symm.trans hGet)
      exact hCommit ⟨packet, hObs⟩
    exact ⟨j, event, packet, hij, by omega, hGet, hObs⟩

/-- Recover the 32 ordinary issues closed by the commit adjoining an actual publication. -/
theorem publishedCopyGroupWithEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {loc : Loc} (hIssue : X.AsyncArrive issue loc true) :
    ∃ group : PublishedCopyGroup l X issue, ∃ (site : Fin 6) (e : Event),
      X.get (issue.1,group.first) = some e ∧ e.pc = copyPacketFirst site := by
  obtain ⟨g, index⟩ := issue
  obtain ⟨pc, he⟩ := hIssue
  obtain ⟨⟨site, rfl⟩, _, _, _⟩ := actualAsyncArrival hX he
  obtain ⟨pub, _, _, hPub⟩ := readyObservation hp hX he rfl
  have hArrive : DecodedObservation.observePacket (copyCommitPc site + 1) true =
      some (DecodedObservation.packetOfSite site) := by fin_cases site <;> decide
  have hPacket : pub.packet = DecodedObservation.packetOfSite site := by
    have h := hPub
    simp only [observe, hArrive] at h
    split at h <;> cases h
    exact (Option.some.inj (by assumption)).symm
  obtain ⟨first, t, vs, body, hIndex, ht, hw, hReach, hBody, hPrefix⟩ :=
    actualPacketPrefix hp hX site he
  let commit := first + body.length
  have hEvent {j : Nat} {e : Event} (h : body[j]? = some e) :
      X.get (g, first + j) = some e := by
    have hl := (List.getElem?_eq_some_iff.mp h).1
    change (X.tr g)[first + j]? = some e
    rw [← List.getElem?_drop, List.prefix_iff_getElem?.mp hPrefix j (by simp; omega),
      List.getElem_append_left hl, ← List.getElem?_eq_getElem hl]
    exact h
  have hc : X.get (g, commit) = some ⟨copyCommitPc site, .asyncCommit⟩ := by
    change (X.tr g)[first + body.length]? = _
    rw [← List.getElem?_drop, List.prefix_iff_getElem?.mp hPrefix body.length (by simp)]
    simp
  have hCommit : DecodedObservation.observePacket (copyCommitPc site) false =
      some (DecodedObservation.packetOfSite site) := by fin_cases site <;> decide
  have hBodyTrace : (X.tr g).take commit = (X.tr g).take first ++ body := by
    have hBodyPrefix : body <+: (X.tr g).drop first :=
      (show body <+: body ++ _ from ⟨_, rfl⟩).trans hPrefix
    have hTake : ((X.tr g).drop first).take body.length = body := by
      obtain ⟨suffix, hSuffix⟩ := hBodyPrefix
      simp [← hSuffix]
    rw [List.take_drop] at hTake
    conv_lhs => rw [← List.take_append_drop first ((X.tr g).take commit)]
    rw [List.take_take, Nat.min_eq_left (by dsimp [commit]; omega), hTake]
  have hNoCommit : ∀ e ∈ body, e.kind ≠ .asyncCommit := by
    rw [hBody]
    exact loaderPacketEventsNoCommit hw ht.ge
  obtain ⟨entry, hFirst, hEntry⟩ := packetEntryIssue site hw ht hReach
  rw [List.getElem?_drop, Nat.add_zero] at hFirst
  have hEmpty : (atPrefix l X g first).pendingCopies = [] := by
    apply pendingEmptyOfSeparation (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hFirst).1)
    intro i hi spec hCopy
    obtain ⟨j, packet, hij, hj, hGet⟩ := packetEntrySeparatesCopies hX site hCopy hFirst hEntry hi
    have hObs : DecodedObservation.observePacket (copyCommitPc packet) false =
        some (DecodedObservation.packetOfSite packet) := by fin_cases packet <;> decide
    exact ⟨j, _, DecodedObservation.packetOfSite packet, hij, hj, hGet, by simp [observe, hObs]⟩
  have hPending : (atPrefix l X g commit).pendingCopies = (body.filterMap vectorOf).reverse := by
    unfold atPrefix at hEmpty ⊢
    rw [hBodyTrace, List.foldl_append, pendingCopiesFold _ _ hNoCommit, hEmpty, List.append_nil]
  have hObsCommit : observe l g ⟨copyCommitPc site, .asyncCommit⟩ = .commit pub.packet := by
    simp [observe, hCommit, hPacket]
  refine ⟨⟨pub, (congrArg D.published (prefixStep he)).trans (advancePublication hPub),
    first, commit, hIndex.symm, indexedCopies first body, ?_, ?_,
    indexedCopiesOrdered first body, ?_, ?_, ?_⟩,site,entry,hFirst,hEntry⟩
  · rw [← show commit + 1 = index from hIndex.symm, prefixStep hc,
      (advanceCommit hObsCommit).2, hPending, List.reverse_reverse, indexedCopiesVectors]
  · rw [← List.length_map (f := Prod.snd), indexedCopiesVectors]
    exact packetBodyVectors ⟨site, t, _, vs, hPacket.symm, ht, hw, hReach, hBody⟩
  · intro j ev target parity ok acquire scope hLo hHi hGet
    have hIndex : j - first < body.length := by dsimp [commit] at hHi; omega
    have hBodyGet := hEvent (List.getElem?_eq_getElem hIndex)
    rw [Nat.add_sub_of_le hLo, hGet] at hBodyGet
    obtain rfl := Option.some.inj hBodyGet
    have hSubset : body ⊆ (vs.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev :=
      fun _ h => hBody ▸ h
    have hm := hSubset (List.getElem_mem (l := body) hIndex)
    exact (loaderPacketEventsBodyKind hw ht.ge _ hm).2 target parity ok acquire scope
  · intro j spec
    rw [memIndexedCopies]
    constructor
    · rintro ⟨hle, e, hj, hk⟩
      have hl := (List.getElem?_eq_some_iff.mp hj).1
      have hGet := hEvent hj
      obtain ⟨pc, kind⟩ := e
      change kind = .copy spec at hk
      subst kind
      exact ⟨hle, by dsimp [commit]; omega, pc, by rwa [Nat.add_sub_of_le hle] at hGet⟩
    · rintro ⟨hle, hlt, pc, hc⟩
      have hl : j - first < body.length := by dsimp [commit] at hlt; omega
      let e := body[j - first]
      have h := List.getElem?_eq_getElem hl
      have hGet := hEvent h
      rw [Nat.add_sub_of_le hle, hc] at hGet
      exact ⟨hle, e, h, (congrArg Event.kind (Option.some.inj hGet)).symm⟩
  · intro i j a b hi hj hij
    obtain ⟨hiFirst, e, hiGet, heKind⟩ := memIndexedCopies.mp hi
    obtain ⟨hjFirst, f, hjGet, hfKind⟩ := memIndexedCopies.mp hj
    rw [hBody] at hiGet hjGet
    have h := loaderPacketSameGroup (begin := first) hX site hw ht.ge
      (by exact ⟨[], by simp⟩) hiGet hjGet
      heKind hfKind (by omega)
    rwa [Nat.add_sub_of_le hiFirst, Nat.add_sub_of_le hjFirst] at h

/-- Recover the 32 ordinary issues closed by the commit adjoining an actual publication. -/
theorem publishedCopyGroup {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {loc : Loc} (hIssue : X.AsyncArrive issue loc true) :
    Nonempty (PublishedCopyGroup l X issue) :=
  ⟨(publishedCopyGroupWithEntry hp hX hIssue).choose⟩

/-- The role state supplies the producer's per-slot ordinal used by the history proof. -/
theorem publicationOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (g index : Nat) (slot : Fin 3) :
    ((atPrefix l X g index).published.countP (fun pub => pub.slot == slot)) =
      readyOrdinal X (readyObject l g slot) (g, index) := by
  let loc := readyObject l g slot
  let pubs := (atPrefix l X g index).published
  have hEqSlot (s : Fin 3) : decide (readyObject l g s = loc) = (s == slot) := by
    by_cases h : s = slot
    · subst s
      simp [loc]
    · have hDiff : readySlot s ≠ readySlot slot := by
        intro hEq
        apply h
        have hVal := congrArg Fin.val hEq
        change 4 + s.val = 4 + slot.val at hVal
        exact Fin.ext (by omega)
      have hLoc : readyObject l g s ≠ loc :=
        Prologue.initObject_ne hDiff
      simp [hLoc, h]
  have hLift (e : Event) : (((readyTarget e).map (fun t => decide (t = loc))).getD false) =
      namesReady loc e := by
    obtain ⟨pc, kind⟩ := e
    cases kind <;> try rfl
    case asyncArrive addr noinc => cases noinc <;> rfl
  have hTrack := congrArg (List.countP (fun t => decide (t = loc)))
    (prefixPublications hp hX g index)
  rw [List.countP_map, List.countP_filterMap] at hTrack
  change pubs.reverse.countP (fun pub => decide (readyObject l g pub.slot = loc)) =
    (((X.tr g).take index).countP
      (fun e => (((readyTarget e).map (fun t => decide (t = loc))).getD false))) at hTrack
  simpa only [hEqSlot, List.countP_reverse, hLift, readyOrdinal, pubs, loc] using hTrack

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
