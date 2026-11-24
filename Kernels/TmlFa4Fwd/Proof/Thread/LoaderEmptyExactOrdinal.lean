-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyChronology
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.AsyncCopy PTX.MbarRing
open PTX.Kernels.TmlFa4Fwd.Loader
  (DrainWaitSite LoaderWaitCode loaderWaitTemplate loaderLinear loaderEventAfterLocal
    pollBeforeSliceEvent actualPrimingEmptyPrefix loaderSliceEvents readySlot readySlot_address
    emptySlot_address loaderStartupAsyncAddress actualAsyncArrival)

noncomputable section

/-- The two fixed empty waits for the initial K and V publications. -/
def primingEmptySite : Fin 2 → DrainWaitSite
  | 0 => ⟨517, 9606, 1848, 1849⟩
  | 1 => ⟨782, 9611, 1925, 1926⟩

/-- The code for the fixed priming spins. -/
theorem primingEmptyCode (stage : Fin 2) : LoaderWaitCode (primingEmptySite stage) := by
  fin_cases stage
  · exact ⟨Flow.code_517, Flow.code_518, Flow.code_519⟩
  · exact ⟨Flow.code_782, Flow.code_783, Flow.code_784⟩

/-- Prepare the fixed empty address and initial parity for a priming spin. -/
theorem primingPollPrep {l : Launch} {g : Nat} (stage : Fin 2)
    (hWidth : l.sharedBase + 8 * stage + 56 < 2 ^ 32) :
    Seg kernel Assumptions.all l g 2 (if stage = 0 then 515 else 780) [(2535, b32 l.sharedBase)]
      (primingEmptySite stage).pc
      [((primingEmptySite stage).base, b32 (l.sharedBase + 8 * stage + 56)),
       ((primingEmptySite stage).phase, b32 1)] := by
  let start := if stage = 0 then 515 else 780
  have hCore : Seg kernel [] l g 2 start [(2535, b32 l.sharedBase)]
      (primingEmptySite stage).pc
      [((primingEmptySite stage).base, b32 (l.sharedBase + 8 * stage + 56)),
       ((primingEmptySite stage).phase, b32 1)] := by
    fin_cases stage
    · change l.sharedBase + 56 < 2 ^ 32 at hWidth
      change Seg kernel [] l g 2 515 [(2535, b32 l.sharedBase)] 517
        [(1848, b32 (l.sharedBase + 56)), (1849, b32 1)]
      intro t ht
      seg_fp ht using norm_bits
    · change l.sharedBase + 8 + 56 < 2 ^ 32 at hWidth
      change Seg kernel [] l g 2 780 [(2535, b32 l.sharedBase)] 782
        [(1925, b32 (l.sharedBase + 8 + 56)), (1926, b32 1)]
      intro t ht
      seg_fp ht using norm_bits
  have hLo : 174 ≤ start := by fin_cases stage <;> decide
  have hHi : start + 2 ≤ 1906 := by fin_cases stage <;> decide
  have hSeq : ((kernel.code.drop start).take 1).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)
  intro t ht
  obtain ⟨u, hr, hu⟩ := hCore t ht
  exact ⟨u, (loaderLinear (regs := []) hLo hHi ht.1 (by simp) hSeq hr).1, hu⟩

/-- The actual initial K or V publication has a successful empty acquire of its slot at parity 1. -/
theorem primingEmptyBeforePublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨(if stage = 0 then 674 else 904), .asyncArrive loc true⟩) :
    let slot : Fin 3 := ⟨stage, by have := stage.isLt; omega⟩
    loc = readyObject l g slot ∧
      ∃ i < index, EmptyAcquire l X (g, i) slot 1 := by
  dsimp only
  let slot : Fin 3 := ⟨stage, by have := stage.isLt; omega⟩
  have hReady := loaderStartupAsyncAddress hp hX he (by fin_cases stage <;> decide)
  have hLoc : loc = readyObject l g slot := by
    rw [hReady]
    fin_cases stage <;> rfl
  refine ⟨hLoc, ?_⟩
  obtain ⟨start, s, vs, hStart, hs, hw, hTarget⟩ := actualPrimingEmptyPrefix hp hX stage he
  let site := primingEmptySite stage
  let addr := l.sharedBase + 8 * stage.val + 56
  have hBound : addr < 2 ^ 32 := by have := hp.shared.2.1; have := stage.isLt; dsimp [addr]; omega
  have hAlign : addr % 8 = 0 := by have := hp.shared.1; dsimp [addr]; omega
  obtain ⟨t, hRun, ht⟩ := primingPollPrep stage hBound s hs
  obtain ⟨tail, hWalk, _, hSaw⟩ := loaderEventAfterLocal hRun hw (List.mem_of_getElem? hTarget)
  have hRange : 174 ≤ site.pc ∧ site.pc + 3 < 1906 := by fin_cases stage <;> decide
  have hLower : (if stage = 0 then 515 else 780) ≤ site.pc := by fin_cases stage <;> decide
  have hUpper : site.pc < (if stage = 0 then 675 else 905) := by fin_cases stage <;> decide
  have hBefore : site.pc < (if stage = 0 then 674 else 904) := by fin_cases stage <;> decide
  have hFresh : ∀ pair ∈ [(site.base, b32 addr), (site.phase, b32 1)], pair.1 ≠ site.result := by
    intro pair hm
    fin_cases stage <;> simp [site, primingEmptySite] at hm
    all_goals rcases hm with rfl | rfl <;> simp [site, primingEmptySite]
  obtain ⟨n, u, rest, later, hEvents, hu, hw', hSeen⟩ :=
    pollBeforeSliceEvent site (primingEmptyCode stage) hRange hLower hUpper hFresh
      (fun _ hAt => loaderWaitTemplate site (primingEmptyCode stage) hRange hBound hAlign
        (by decide) hAt.1 hAt.2.2.2.1 hAt.2.2.2.2.1 hAt.2.2.2.2.2.1)
      ht hWalk hBefore hSaw
  have hIndex : n < index - start := by
    by_contra! hLe
    have hGet : ((X.tr g).drop start)[index - start]? =
        some ⟨(if stage = 0 then 674 else 904), .asyncArrive loc true⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hStart]
      exact he
    rcases hLe.eq_or_lt with hEq | hLt
    · rw [hEq, hEvents, List.getElem?_append_right (by simp), List.length_replicate,
        Nat.sub_self] at hGet
      have hPc := congrArg Event.pc (Option.some.inj hGet)
      exact (Nat.ne_of_lt hBefore) hPc
    · rw [hEvents, List.getElem?_append_left (by simpa using hLt),
        List.getElem?_replicate_of_lt hLt] at hGet
      have hPc := congrArg Event.pc (Option.some.inj hGet)
      exact (Nat.ne_of_lt hBefore) hPc
  have hGet : X.get (g, start + n) = some
      ⟨site.pc, .wait ⟨.shared, g / l.block, addr⟩ 1 true true .cta⟩ := by
    change (X.tr g)[start + n]? = _
    rw [← List.getElem?_drop, hEvents, List.getElem?_append_right (by simp),
      List.length_replicate, Nat.sub_self]
    rfl
  refine ⟨start + n, by omega, _, hGet, ?_⟩
  change Kind.wait ⟨.shared, g / l.block, addr⟩ 1 true true .cta =
    .wait (emptyObject l g slot) 1 true true .cta
  rw [emptyObject, emptySlot_address]

private theorem earlierEmptyOfPublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner g index : Nat} {slot : Fin 3}
    (he : X.AsyncArrive (g, index) (readyObject l owner slot) true) :
    ∃ i < index, ∃ parity, EmptyAcquire l X (g, i) slot parity := by
  obtain ⟨pc, hGet⟩ := he
  obtain ⟨⟨site, rfl⟩, _, _, _⟩ := actualAsyncArrival hX hGet
  have startup (stage : Fin 2) (hAt : X.get (g, index) =
      some ⟨(if stage = 0 then 674 else 904), .asyncArrive (readyObject l owner slot) true⟩) :
      ∃ i < index, ∃ parity, EmptyAcquire l X (g, i) slot parity := by
    obtain ⟨hLoc, i, hi, hEmpty⟩ := primingEmptyBeforePublication hp hX stage hAt
    have hAddr := congrArg Loc.addr hLoc
    simp only [readyObject, readySlot_address] at hAddr
    have hEq : (⟨stage.val, by have := stage.isLt; omega⟩ : Fin 3) = slot :=
      Fin.ext (by dsimp only at hAddr ⊢; omega)
    exact ⟨i, hi, 1, hEq ▸ hEmpty⟩
  have recurring (h : RecurringPublication X (g, index) (readyObject l owner slot)) :
      ∃ i < index, ∃ parity, EmptyAcquire l X (g, i) slot parity := by
    obtain ⟨guard⟩ := recurringGuard hp hX h
    have hSame : guard.acquire.1 = g := guard.guarded.1.1.trans guard.tracked.1
    have hi : guard.acquire.2 < index := guard.guarded.1.2.1.trans guard.tracked.2.1
    refine ⟨guard.acquire.2, hi, guard.parity, ?_⟩
    exact (congrArg (fun a => (a, guard.acquire.2)) hSame) ▸ guard.empty
  fin_cases site
  · exact startup 0 hGet
  · exact startup 1 hGet
  · exact recurring ⟨0, hGet⟩
  · exact recurring ⟨1, hGet⟩
  · exact recurring ⟨2, hGet⟩
  · exact recurring ⟨3, hGet⟩

/-- Every prior same-slot publication contributes an earlier successful empty acquire,
including the two priming packets. -/
theorem OrderedGuardedReuse.exactOrdinalLower {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner : Nat} {publication : EvId} {slot : Fin 3}
    (he : X.AsyncArrive publication (readyObject l owner slot) true)
    (h : OrderedGuardedReuse l X publication slot) :
    (atPrefix l X publication.1 publication.2).published.countP (fun pub => pub.slot == slot) ≤
      emptyOrdinal l X h.acquire slot := by
  generalize hN :
    (atPrefix l X publication.1 publication.2).published.countP (fun pub => pub.slot == slot) = n
  induction n using Nat.strong_induction_on generalizing publication with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨i, hi, hearlier, hiOrdinal⟩ :=
        earlierPublication hp hX he (n := n) (hN.symm ▸ Nat.lt_succ_self n)
      have afterPub := h.afterEarlier i _ hi hearlier
      have more {g j q : Nat} (hSame : g = h.acquire.1) (hBefore : j < h.acquire.2)
          (ha : EmptyAcquire l X (g, j) slot q) :
          emptyOrdinal l X (g, j) slot + 1 ≤ emptyOrdinal l X h.acquire slot := by
        obtain ⟨⟨pc, kind⟩, hEvent, hKind⟩ := ha
        dsimp only at hKind
        subst kind
        have hOne := PTX.MbarRing.Poll.okPoll_get hEvent
        unfold emptyOrdinal
        rw [← hOne, hSame]
        exact PTX.MbarRing.Poll.okPolls_mono _ _ (Nat.succ_le_of_lt hBefore)
      cases n with
      | zero =>
        obtain ⟨j, hj, q, ha⟩ := earlierEmptyOfPublication hp hX hearlier
        have := more h.issuer.symm (hj.trans afterPub) ha
        omega
      | succ n =>
        obtain ⟨earlier⟩ := positiveGenerationOrderedGuard hp hX hearlier
          (hiOrdinal.symm ▸ Nat.succ_pos n)
        have hBound := ih (n + 1) (Nat.lt_succ_self _) hearlier earlier hiOrdinal
        have hSame : earlier.acquire.1 = h.acquire.1 := earlier.issuer.trans h.issuer.symm
        have hRank : emptyOrdinal l X earlier.acquire slot + 1 ≤
            emptyOrdinal l X h.acquire slot :=
          more hSame (earlier.before.trans afterPub) earlier.empty
        omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
