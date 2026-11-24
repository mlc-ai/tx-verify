-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFinalCacheUseOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
public import Kernels.TmlFa4Fwd.Proof.MmaLoopIterations
public import Kernels.TmlFa4Fwd.Proof.MmaSingleVisitSchedule
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
import Lemmas.Flow.Determinism
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma

private def endpointReadyAt (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => e.pc == 2145 || e.pc == 2545
  | _ => false

private theorem allReadyMarks (e : Event) :
    (steadyReadyAt 0 e).toNat + (steadyReadyAt 1 e).toNat + (endpointReadyAt e).toNat =
      (readyEvent e).isSome.toNat := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try (solve | simp [steadyReadyAt, endpointReadyAt, readyEvent])
  case wait loc parity ok causal scope =>
    cases ok
    · simp [steadyReadyAt, endpointReadyAt, readyEvent]
    · by_cases hSite : pc = 2145 ∨ pc = 2294 ∨ pc = 2352 ∨ pc = 2545
      · have hMark : (List.finRange 4).any (fun i => readyHead i == pc) = true := by
          rcases hSite with rfl | rfl | rfl | rfl <;> decide
        rcases hSite with rfl | rfl | rfl | rfl <;>
          simp [steadyReadyAt, steadyReadySite, endpointReadyAt, readyEvent, hMark]
      · have hNo (x : Nat) (h : x = 2145 ∨ x = 2294 ∨ x = 2352 ∨ x = 2545) :
            (pc == x) = false := Bool.eq_false_iff.mpr (fun he => hSite (beq_iff_eq.mp he ▸ h))
        have hMark : (List.finRange 4).any (fun i => readyHead i == pc) = false := by
          by_contra hYes
          obtain ⟨i,_,hi⟩ := List.any_eq_true.mp (Bool.eq_true_of_ne_false hYes)
          have hTags : ∀ i : Fin 4, readyHead i = 2145 ∨ readyHead i = 2294 ∨
              readyHead i = 2352 ∨ readyHead i = 2545 := by decide
          exact hSite ((beq_iff_eq.mp hi) ▸ hTags i)
        simp [steadyReadyAt,steadyReadySite,endpointReadyAt,readyEvent,hMark,
          hNo 2145 (by decide),hNo 2294 (by decide),hNo 2352 (by decide),hNo 2545 (by decide)]

private theorem markCountsBeforeReadyCount (es : List Event) :
    es.countP (steadyReadyAt 0) + es.countP (steadyReadyAt 1) + es.countP endpointReadyAt =
      (es.filterMap readyEvent).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hMark := allReadyMarks e
    rw [List.length_filterMap_eq_countP] at ih ⊢
    simp only [List.countP_cons]
    cases hV : steadyReadyAt 0 e <;> cases hK : steadyReadyAt 1 e <;>
      cases hOpen : endpointReadyAt e <;> cases hReady : (readyEvent e).isSome <;>
      simp only [hV, hK, hOpen, hReady, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero] at hMark ⊢ <;> omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem endpointReadyCount {final : EvId} {spec : TcCommit.Spec}
    (hFinal : Thread.SecondOutputCommit X final spec) :
    2 ≤ ((X.tr final.1).take final.2).countP endpointReadyAt := by
  obtain ⟨base, hInitial⟩ := Thread.initialCanonicalQkIssuesBeforeSecondOutputCommit hp hX hFinal 0
  obtain ⟨_, hFirst, hPrior, _, _, _⟩ := hInitial 0
  obtain ⟨i, hi, loc, parity, hFirstReady, _⟩ :=
    readyWaitBeforeGate hp hX 0 hFirst (by dsimp only [qkIssueEvent]; decide)
  obtain ⟨j, hj, target, q, hTailReady, _⟩ := tailValueWaitBeforeSecondOutput hp hX hFinal.decoded
  have hOpen : X.get (final.1, i) = some ⟨2145, .wait loc parity true true .cta⟩ := hFirstReady
  have hNot : i ≠ j := by
    intro hSame
    rw [hSame, hTailReady] at hOpen
    have hPc := congrArg Event.pc (Option.some.inj hOpen)
    simp at hPc
  have hIo : i < final.2 := by
    have hLt := hPrior.2.1
    change base + (0 : Fin 8).val < final.2 at hLt
    omega
  have pair {a b : Nat} {e f : Event}
      (ha : X.get (final.1, a) = some e) (ha' : endpointReadyAt e = true)
      (hb : X.get (final.1, b) = some f) (hb' : endpointReadyAt f = true)
      (hab : a < b) (hBefore : b < final.2) :
      2 ≤ ((X.tr final.1).take final.2).countP endpointReadyAt := by
    have hLo := countP_take_succ ha ha'
    have hMid := countP_take_mono endpointReadyAt (X.tr final.1) (show a + 1 ≤ b by omega)
    have hHi := countP_take_succ hb hb'
    have hAll := countP_take_mono endpointReadyAt (X.tr final.1)
      (show b + 1 ≤ final.2 by omega)
    omega
  rcases Nat.lt_or_gt_of_ne hNot with hij | hji
  · exact pair hOpen rfl hTailReady rfl hij hj
  · exact pair hTailReady rfl hOpen rfl hji hIo

/-- The actual O1 commit is after every steady traversal of the initialized
counter. Its thread cursor has observed at least two acquisitions per traversal. -/
theorem steadyReadyLowerBeforeSecondOutputCommit {final : EvId} {spec : TcCommit.Spec}
    (hFinal : Thread.SecondOutputCommit X final spec) {start n : Nat} {s : TState}
    {out : Option TState} (hStart : start ≤ final.2) (hN : 2 ≤ n) (hWord : n ≤ 2 ^ 32 + 1)
    (hCounter : At s 2291 [(7204, wideCounterWord n)])
    (hRun : Run kernel Assumptions.all l final.1 s ((X.tr final.1).drop start) out) :
    let st := atPrefix l X final.1 final.2
    2 * n ≤ st.kvAcquires 0 + st.kvAcquires 1 + st.kvAcquires 2 := by
  let events := (X.tr final.1).drop start
  let finish := final.2 + 1 - start
  let front := events.take finish
  have hSplit : Run kernel Assumptions.all l final.1 s (front ++ events.drop finish) out := by
    simpa only [front, List.take_append_drop, events] using hRun
  obtain ⟨out, hPrefix⟩ := hSplit.prefix
  obtain ⟨visits, hWalk⟩ := walkFromRun hPrefix
  have hGet : front[final.2 - start]? = some ⟨2646, .tc (.commit spec)⟩ := by
    dsimp only [front, finish, events]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hStart]
    exact hFinal.decoded
  have hEnd : ⟨2646, .tc (.commit spec)⟩ ∈ front := List.mem_of_getElem? hGet
  have hTailPc : 2534 ≤ 2646 := by decide
  have hV := steadyReadyAcquiresBeforeTailEvent hWalk hN hWord hCounter hEnd hTailPc 0
  have hK := steadyReadyAcquiresBeforeTailEvent hWalk hN hWord hCounter hEnd hTailPc 1
  have hEnds := endpointReadyCount hp hX hFinal
  have hFront : front = ((X.tr final.1).take (final.2 + 1)).drop start := by
    simp only [front, events, finish, List.drop_take]
  have hCut := List.drop_sublist start ((X.tr final.1).take (final.2 + 1))
  rw [← hFront] at hCut
  have hVLe := hCut.countP_le (p := steadyReadyAt 0)
  have hKLe := hCut.countP_le (p := steadyReadyAt 1)
  have hDecoded :
      (X.tr final.1)[final.2]? = some ⟨2646, .tc (.commit spec)⟩ := hFinal.decoded
  have hFinish : ((X.tr final.1).take (final.2 + 1)) = (X.tr final.1).take final.2 ++
      [⟨2646, .tc (.commit spec)⟩] := by rw [List.take_add_one, hDecoded]; rfl
  rw [hFinish] at hVLe hKLe
  simp only [List.countP_append, List.countP_singleton, steadyReadyAt, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero] at hVLe hKLe
  have hUpper := markCountsBeforeReadyCount ((X.tr final.1).take final.2)
  have hTotal := readyUsesAtPrefix hp hX (event_thread_lt hX hFinal.decoded)
    (hFinal.issuerWarp hp hX) final.2
  rw [hTotal] at hUpper
  omega

private theorem readyOccurrenceOfLower {final : EvId} {spec : TcCommit.Spec}
    (hFinal : Thread.SecondOutputCommit X final spec) {use : Nat}
    (hUse : use < (((X.tr final.1).take final.2).filterMap readyEvent).length) :
    ∃ wait, TraceBefore X (final.1, wait) final ∧
      ReadyPoll l X final.1 wait (readyStage use) (readyWord use) true .cta ∧
      (atPrefix l X final.1 wait).kvAcquires (readyStage use) = use / 3 := by
  have hg := event_thread_lt hX hFinal.decoded
  have hw := hFinal.issuerWarp hp hX
  obtain ⟨wait, hBefore, hReady, hOccur⟩ :=
    readyPollAtOrdinalBefore hp hX hg hw hUse
  have hExact := (hReady.exactOccurrence hp hX hw).2.1
  rw [← readyUsesAtPrefix hp hX hg hw wait, hOccur] at hExact
  exact ⟨wait, ⟨rfl, hBefore, len_of_get hFinal.decoded⟩, hReady, hExact⟩

/-- Every use below the initialized trip count's cache extent has its
actual successful observation before the second output commit. -/
theorem readyOccurrenceBeforeSecondOutputCommit {final : EvId} {spec : TcCommit.Spec}
    (hFinal : Thread.SecondOutputCommit X final spec) {start n use : Nat} {s : TState}
    {out : Option TState} (hStart : start ≤ final.2) (hN : 2 ≤ n) (hWord : n ≤ 2 ^ 32 + 1)
    (hCounter : At s 2291 [(7204, wideCounterWord n)])
    (hRun : Run kernel Assumptions.all l final.1 s ((X.tr final.1).drop start) out)
    (hUse : use < 2 * n) :
    ∃ wait, TraceBefore X (final.1, wait) final ∧
      ReadyPoll l X final.1 wait (readyStage use) (readyWord use) true .cta ∧
      (atPrefix l X final.1 wait).kvAcquires (readyStage use) = use / 3 := by
  have hBound := steadyReadyLowerBeforeSecondOutputCommit hp hX hFinal hStart hN hWord hCounter hRun
  dsimp only at hBound
  rw [← readyUsesAtPrefix hp hX (event_thread_lt hX hFinal.decoded)
    (hFinal.issuerWarp hp hX) final.2] at hBound
  exact readyOccurrenceOfLower hp hX hFinal (hUse.trans_le hBound)

/-- The selected real request's entire K/V extent is acquired before O1,
with the exact physical generation of each successful poll. -/
theorem selectedReadyOccurrenceBeforeSecondOutputCommitInPrefix (hFrame : OutputFootprint p X)
    {final : EvId} {spec : TcCommit.Spec} (hFinal : Thread.SecondOutputCommit X final spec)
    {pos batch tile use : Nat} (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    {s : TState} {ending : Option TState}
    (hs : At s 2109
      [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)])
    (hRun : Run kernel Assumptions.all l final.1 s ((X.tr final.1).drop pos) ending)
    (hReaches : ending = none ∨ pos ≤ final.2) (hUse : use < 2 * trips p batch tile) :
    ∃ wait, TraceBefore X (final.1, wait) final ∧
      ReadyPoll l X final.1 wait (readyStage use) (readyWord use) true .cta ∧
      (atPrefix l X final.1 wait).kvAcquires (readyStage use) = use / 3 := by
  by_cases hSmall : trips p batch tile = 1
  · rw [hSmall] at hUse
    have hEnds := endpointReadyCount hp hX hFinal
    have hTotal := markCountsBeforeReadyCount ((X.tr final.1).take final.2)
    apply readyOccurrenceOfLower hp hX hFinal
    omega
  have hTrips : 2 ≤ trips p batch tile := by
    have := (trips_bounds hp hb hTile).1
    omega
  have hWord : trips p batch tile ≤ 2 ^ 32 + 1 := by
    have h := (trips_bounds hp hb hTile).2.1
    have hKeys := (hp.lengths batch hb).2.2
    change trips p batch tile ≤ (p.kLength batch + 127) / 128 at h
    omega
  obtain ⟨start, t, out, hBefore, ht, hTrace⟩ := selectedSteadyCursorInPrefix hp hX
    hb hTile hTrips hs (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
    hRun hFinal.decoded hReaches (show 2279 < 2646 by decide) (by simp [Ends])
  exact readyOccurrenceBeforeSecondOutputCommit hp hX hFinal hBefore hTrips hWord ht hTrace hUse

/-- The terminal V acquire of an initialized steady traversal consumes the final
odd-numbered cache use, including in a prefix ending at the acquire itself. -/
theorem terminalValueOrdinalOfSteady {g wait parity start n : Nat} {loc : Loc} {s : TState}
    {out : Option TState} (hw : Prologue.warpIndex l g = 12) (hStart : start ≤ wait)
    (hWait : X.get (g,wait) = some ⟨2545,.wait loc parity true true .cta⟩)
    (hInitial : (((X.tr g).take start).filterMap readyEvent).length = 1) (hN : 2 ≤ n)
    (hWord : n ≤ 2 ^ 32 + 1) (hCounter : At s 2291 [(7204, wideCounterWord n)])
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop start) out) :
    (((X.tr g).take wait).filterMap readyEvent).length = 2*n-1 := by
  let tail := (X.tr g).drop start
  let seen := tail.take (wait-start)
  let last : Event := ⟨2545,.wait loc parity true true .cta⟩
  have hLast : tail[wait-start]? = some last := by
    dsimp only [tail]
    rw [List.getElem?_drop, Nat.add_sub_of_le hStart]
    exact hWait
  have hCut : tail.take (wait-start+1) = seen ++ [last] := by
    simp [seen,List.take_add_one,hLast]
  have hJoin : Run kernel Assumptions.all l g s
      (tail.take (wait-start+1) ++ tail.drop (wait-start+1)) out := by
    simpa only [List.take_append_drop,tail] using hRun
  obtain ⟨_,hPrefix⟩ := hJoin.prefix
  rw [hCut] at hPrefix
  obtain ⟨_,hWalk⟩ := walkFromRun hPrefix
  have hTail : last ∈ seen ++ [last] := by simp
  have hTailPc : 2534 ≤ last.pc := show 2534 ≤ 2545 by decide
  have hV := steadyReadyAcquireCountBeforeTailEvent hWalk hN hWord hCounter hTail hTailPc 0
  have hK := steadyReadyAcquireCountBeforeTailEvent hWalk hN hWord hCounter hTail hTailPc 1
  simp only [List.countP_append,List.countP_singleton,last,steadyReadyAt,steadyReadySite,
    show (2545 == 2294) = false by decide, show (2545 == 2352) = false by decide,
    Bool.false_eq_true,↓reduceIte,Nat.add_zero] at hV hK
  have hEndpoints : seen.countP endpointReadyAt = 0 := by
    apply List.countP_eq_zero.mpr
    rintro ⟨site,kind⟩ hm
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hm
    have hjLt := (List.getElem?_eq_some_iff.mp hj).1
    have hPos : j < wait-start := by simp [seen] at hjLt; omega
    change (tail.take (wait-start))[j]? = some ⟨site,kind⟩ at hj
    rw [List.getElem?_take_of_lt hPos,List.getElem?_drop] at hj
    have he : X.get (g,start+j) = some ⟨site,kind⟩ := hj
    cases kind <;> try (solve | simp [endpointReadyAt])
    case wait addr q ok acq scope =>
      cases ok
      · simp [endpointReadyAt]
      intro hBad
      have hOr := Bool.or_eq_true_iff.mp (show (site == 2145 || site == 2545) = true from hBad)
      have hSome : (List.finRange 4).any (fun i => readyHead i == site) = true := by
        rcases hOr with hPc | hPc
        · rw [beq_iff_eq.mp hPc]; decide
        · rw [beq_iff_eq.mp hPc]; decide
      have hMark : readyEvent ⟨site,.wait addr q true acq scope⟩ = some (addr,q) := by
        simp [readyEvent,hSome]
      have hKind : acq = true ∧ scope = .cta := by
        rcases hOr with hPc | hPc
        · apply readyGateAcquireFlags hX 0
          rw [show (slotWait (0 : Fin 4)).pc = 2145 by decide, ← beq_iff_eq.mp hPc]
          exact he
        · apply readyGateAcquireFlags hX 3
          rw [show (slotWait (3 : Fin 4)).pc = 2545 by decide, ← beq_iff_eq.mp hPc]
          exact he
      obtain ⟨rfl,rfl⟩ := hKind
      rcases hOr with hFirst | hLast
      · obtain ⟨slot,hLoc⟩ := readySlotOfProjection hp hX hw he hMark
        subst addr
        have hPoll : ReadyPoll l X g (start+j) slot q true .cta := ⟨_,he,rfl⟩
        obtain ⟨observed,hGet,hUse⟩ := hPoll.useSite hp hX hw
        have hAt : observed = site := congrArg Event.pc (Option.some.inj (hGet.symm.trans he))
        have hZero : (((X.tr g).take (start+j)).filterMap readyEvent).length = 0 := by
          simpa [hAt,beq_iff_eq.mp hFirst,ReadyUseSite,readyHead] using hUse
        have hMono := ((List.take_sublist_take_left (l := X.tr g)
          (show start ≤ start+j by omega)).filterMap readyEvent).length_le
        omega
      · rw [beq_iff_eq.mp hLast] at he
        have hEq := Thread.tailValueAcquireUnique hp hX hw he hWait
        omega
  have hMarkCount := markCountsBeforeReadyCount seen
  have hTake : (X.tr g).take wait = (X.tr g).take start ++ seen := by
    conv_lhs => rw [← Nat.add_sub_of_le hStart,List.take_add]
  rw [hTake,List.filterMap_append,List.length_append,hInitial]
  omega

/-- The final MMA commit observes exactly the last selected request's V use.
This ties the terminal ready ordinal to the trip count read by the issuer. -/
theorem selectedTerminalValueOrdinal (hFrame : OutputFootprint p X) {final : EvId}
    {spec : TcCommit.Spec} (hFinal : Thread.SecondOutputCommit X final spec) {pos batch tile : Nat}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch) {s : TState}
    (hs : At s 2109
      [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)])
    (hRun : Run kernel Assumptions.all l final.1 s ((X.tr final.1).drop pos) none) :
    ∃ wait loc parity, X.get (final.1,wait) = some ⟨2545,.wait loc parity true true .cta⟩ ∧
      TraceBefore X (final.1,wait) final ∧
      (((X.tr final.1).take wait).filterMap readyEvent).length = 2 * trips p batch tile - 1 := by
  obtain ⟨wait,_,loc,parity,hWait,hTrace⟩ := tailValueWaitBeforeSecondOutput hp hX hFinal.decoded
  refine ⟨wait,loc,parity,hWait,hTrace.1,?_⟩
  have hw := hFinal.issuerWarp hp hX
  by_cases hSingle : trips p batch tile = 1
  · obtain ⟨j,hPoll,_,hRank⟩ := Thread.initialValueAcquireBeforeSecondOutputCommit hp hX hFinal
    obtain ⟨site,hEvent,hTag⟩ := hPoll.useSite hp hX hw
    have hV : site = 2294 ∨ site = 2545 := by
      rw [hRank] at hTag
      simpa [ReadyUseSite,readyHead] using hTag
    have hRange := selectedOneVisitNoSteadyEvents hp hX hb hTile hSingle hs
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hRun j _ hEvent (by simp [Ends])
    have hSite : site = 2545 := by
      change site < 2279 ∨ 2534 ≤ site at hRange
      omega
    rw [hSite] at hEvent
    have hSame := Thread.tailValueAcquireUnique hp hX hw hEvent hWait
    simpa [hSame,hSingle] using hRank
  · have hTrips : 2 ≤ trips p batch tile := by
      have := (trips_bounds hp hb hTile).1
      omega
    have hWord : trips p batch tile ≤ 2 ^ 32 + 1 := by
      have h := (trips_bounds hp hb hTile).2.1
      have hKeys := (hp.lengths batch hb).2.2
      change trips p batch tile ≤ (p.kLength batch + 127) / 128 at h
      omega
    obtain ⟨start,t,out,hStart,hCounter,hRest,hInitial⟩ :=
      selectedSteadyCursorAndInitialReady hp hX hb hTile hTrips hs
        (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hRun hWait (.inl rfl)
        (show 2279 < 2545 by decide) (by simp [Ends])
    exact terminalValueOrdinalOfSteady hp hX hw hStart hWait hInitial hTrips hWord hCounter hRest

/-- Every terminal PV fragment uses the last V packet of the selected request. -/
theorem tailFragmentUseOfSelectedTerminal (hFrame : OutputFootprint p X) {final : EvId}
    {spec : TcCommit.Spec} (hFinal : Thread.SecondOutputCommit X final spec) {pos batch tile : Nat}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch) {s : TState}
    (hs : At s 2109
      [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)])
    (hRun : Run kernel Assumptions.all l final.1 s ((X.tr final.1).drop pos) none) {g index d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {stage : Fin 2} {step : Fin 8}
    (hCta : g / l.block = final.1 / l.block)
    (hFragment : PvInstruction X (g,index) (firstPvBlock false stage) step d op accum mask) :
    let use := 2 * trips p batch tile - 1
    LatestValueReadyUse l X g index use ∧
      op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 ∧ PvShape l g op := by
  have hThread : g = final.1 :=
    (mmaBeforeSameCtaSecondOutputCommit hp hX ⟨_,hFragment.decoded⟩ hFinal hCta).1
  subst g
  obtain ⟨use,_,wait,hDesc,hOperand,hShape,hPoll,hObs,_,hRank,hBefore,hOnly⟩ :=
    actualValueReadyOfFragment hp hX hFragment
  have hWait : X.get (final.1,wait) = some ⟨2545,
      .wait (Observation.readyObject l final.1 (readyStage use)) (readyWord use)
        true true .cta⟩ := by
    have hSite : (slotWait (releaseIndex (valueReleaseForm false))).pc = 2545 := by decide
    simpa [firstPvBlock, ReleaseReadyObservation, hSite] using hObs
  obtain ⟨terminal,_,_,hTerminal,_,hOrdinal⟩ :=
    selectedTerminalValueOrdinal hp hX hFrame hFinal hb hTile hs hRun
  have hSame := Thread.tailValueAcquireUnique hp hX (hFinal.issuerWarp hp hX) hWait hTerminal
  subst terminal
  have hUse : use = 2 * trips p batch tile - 1 := hRank.symm.trans hOrdinal
  dsimp only
  rw [← hUse]
  exact ⟨⟨wait,hPoll,hRank,hDesc.2.2,hBefore,hOnly⟩,hOperand,hShape⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
