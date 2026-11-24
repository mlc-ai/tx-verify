-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyRoundEntry
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

/-- Register facts for the two steady scratch passes. -/
def steadySlotFrame (p : Params) (l : Launch)
    (batch head trips warp tid tile : Nat) (slot : Fin 2) (more : Bool) : List (Nat × Value) :=
  [(7182, b32 slot.val), (11, .pred more), (1148, b32 (primingLaneRow tile tid))] ++
    steadyCacheFrame p l batch head trips warp tid

/-- One actual steady slot updates the selected page word and its lane-local row word in order. -/
structure SteadyPageWords (p : Params) (l : Launch) (X : Execution)
    (g pos batch row : Nat) (slot : Fin 2) : Prop where
  read : row < p.kLength batch →
    X.get (g, pos) = some ⟨(recurringPageReadSite 1).pc,
      .rd {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
        ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩
  page : X.get (g, pos + primingScratchReads p batch row) =
    some ⟨pageRefreshPc 1,
      .wr (pageRefreshAccess l g 1 false slot) (b32 (primingScratchPage p batch row)).toBytes⟩
  rowWord : X.get (g, pos + primingScratchReads p batch row + 1) =
    some ⟨rowRefreshPc 1, .wr (pageRefreshAccess l g 1 true slot) (b32 (row % 16)).toBytes⟩

private theorem SteadyPageWords.advance {p : Params} {l : Launch} {X : Execution}
    {g pos batch row : Nat} {slot : Fin 2} (h : SteadyPageWords p l X g pos batch row slot)
    {ending : Option TState} (hDemand : PrefixDemand X g pos (rowRefreshPc 1) ending) :
    PrefixDemand X g (pos + primingScratchReads p batch row + 2) (rowRefreshPc 1) ending := by
  have hAt : PrefixDemand X g (pos + primingScratchReads p batch row) (rowRefreshPc 1) ending := by
    by_cases hLive : row < p.kLength batch
    · simpa [primingScratchReads, hLive] using hDemand.advance (h.read hLive)
        (show (recurringPageReadSite 1).pc ≤ rowRefreshPc 1 by decide)
    · simpa [primingScratchReads, hLive] using hDemand
  have hPagePc : pageRefreshPc 1 ≤ rowRefreshPc 1 := by decide
  simpa only [Nat.add_assoc] using ((hAt.advance h.page hPagePc).advance h.rowWord le_rfl)

private theorem SteadyPageWords.shuffleRank {p : Params} {l : Launch} {X : Execution}
    {g pos batch row : Nat} {slot : Fin 2} (h : SteadyPageWords p l X g pos batch row slot) :
    ((X.tr g).take (pos + primingScratchReads p batch row + 2)).countP Execution.isShfl =
      ((X.tr g).take pos).countP Execution.isShfl := by
  have hRank :
      ((X.tr g).take (pos + primingScratchReads p batch row)).countP Execution.isShfl =
        ((X.tr g).take pos).countP Execution.isShfl := by
    by_cases hLive : row < p.kLength batch
    · simpa only [primingScratchReads, ite_eq_left hLive, Nat.add_zero] using
        countShuffleTakeOfNonshuffle (h.read hLive) rfl
    · simp only [primingScratchReads, ite_eq_right hLive, Nat.add_zero]
  have hPage := countShuffleTakeOfNonshuffle h.page rfl
  have hRow := countShuffleTakeOfNonshuffle h.rowWord rfl
  rw [Nat.add_succ, hRow, hPage, hRank]

private theorem SteadyPageWords.beforeLater {p : Params} {l : Launch} {X : Execution}
    {g pos j batch row : Nat} {slot : Fin 2} (h : SteadyPageWords p l X g pos batch row slot)
    {e : Event} (he : X.get (g, j) = some e) (hBefore : pos ≤ j) (hLate : rowRefreshPc 1 < e.pc) :
    pos + primingScratchReads p batch row + 2 ≤ j := by
  have avoid {k : Nat} {f : Event} (hf : X.get (g, k) = some f)
      (hPc : f.pc ≤ rowRefreshPc 1) : k ≠ j := by
    intro hEq
    subst j
    exact (Nat.not_le_of_lt hLate) ((Option.some.inj (hf.symm.trans he)) ▸ hPc)
  have hPage : pageRefreshPc 1 ≤ rowRefreshPc 1 := by decide
  have hRead : (recurringPageReadSite 1).pc ≤ rowRefreshPc 1 := by decide
  have hFirst := avoid h.page hPage
  have hSecond := avoid h.rowWord le_rfl
  by_cases hLive : row < p.kLength batch
  · have hReadHere := avoid (h.read hLive) hRead
    simp only [primingScratchReads, ite_eq_left hLive] at hFirst hSecond ⊢
    omega
  · simp only [primingScratchReads, ite_eq_right hLive] at hFirst hSecond ⊢
    omega

variable {p : Params}

private theorem steadyPageSlotGuard {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch head trips warp tid tile : Nat} (hb : batch < p.batch) (slot : Fin 2) (more : Bool)
    (hBound : primingLaneRow tile tid + 64 < 2 ^ 31) {s : TState}
    (hs : At s 1403 ([(1148, b32 (primingLaneRow tile tid)), (2131, b32 (64 * slot.val))] ++
      steadySlotFrame p l batch head trips warp tid tile slot more)) :
    let row := primingLaneRow tile tid + 64 * slot.val
    let F := steadySlotFrame p l batch head trips warp tid tile slot more
    ∃ u, run kernel Assumptions.all l g 10 s = some u ∧
      At u 1413 (recurringPageGuardInput p l 1 slot batch row ++ F) ∧
      RecurringRefreshFrame 1 F := by
  let base := primingLaneRow tile tid
  let row := base + 64 * slot.val
  let F := steadySlotFrame p l batch head trips warp tid tile slot more
  have hSlot := slot.isLt
  have hRow : row < 2 ^ 31 := by dsimp [row, base]; omega
  have hLen : p.kLength batch < 2 ^ 31 := by have := (hp.lengths batch hb).2.2; omega
  have hInput : At s 1403 (recurringPageIndexInput 1 base (p.kLength batch) slot) := by
    apply hs.mono
    simp only [recurringPageIndexInput, recurringPageSite, Holds]
    repeat' apply And.intro
    all_goals first | trivial | exact holds_lookup hs.2.2.2.2 rfl
  obtain ⟨u, hu, hU⟩ := recurringPageIndexCore (l := l) (g := g) 1 slot hRow hLen s hInput
  obtain ⟨huA, huF⟩ := loaderLinear (regs := F.map Prod.fst) (lo := 1403) (n := 10)
    (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hCarry := holdsSchedulerFrame (show Holds s.regs F from hs.2.2.2.2.2.2)
    huF (fun _ hm => List.mem_map_of_mem hm)
  have hGuard : At u 1413 (recurringPageGuardInput p l 1 slot batch row ++ F) := by
    apply hU.mono
    apply (holds_append ..).mpr
    refine ⟨(holds_append ..).mpr ⟨hU.2.2.2.2, ?_⟩, hCarry⟩
    simp only [pageStoreCarry, recurringPageBatchInputs, recurringPageStoreSite,
      recurringPageSite, List.cons_append, Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | exact holds_lookup hCarry rfl
      | exact holds_lookup hU.2.2.2.2 rfl
  have hExtra : RecurringRefreshFrame 1 F := by
    constructor
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
    · rintro ⟨reg, value⟩ hm
      simp [F, steadySlotFrame, steadyCacheFrame, warmStartFrame, warmPageRoots, warmLaneRoots,
        primingVScratchAbi, recurringPageSite] at hm ⊢
      aesop
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
  exact ⟨u, huA, hGuard, hExtra⟩

private theorem steadyPageSlotRun {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g pos batch head trips warp tid tile : Nat} (hb : batch < p.batch) (slot : Fin 2) (more : Bool)
    (hBound : primingLaneRow tile tid + 64 < 2 ^ 31) {s : TState} {ending : Option TState}
    (hs : At s 1403 ([(1148, b32 (primingLaneRow tile tid)), (2131, b32 (64 * slot.val))] ++
      steadySlotFrame p l batch head trips warp tid tile slot more))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hDemand : PrefixDemand X g pos (rowRefreshPc 1) ending) :
    let row := primingLaneRow tile tid + 64 * slot.val
    SteadyPageWords p l X g pos batch row slot ∧
      ∃ u, At u 1424 (steadySlotFrame p l batch head trips warp tid tile slot more) ∧
        Run kernel Assumptions.all l g u
          ((X.tr g).drop (pos + primingScratchReads p batch row + 2)) ending := by
  let row := primingLaneRow tile tid + 64 * slot.val
  have hRow : row < 2 ^ 31 := by
    have := slot.isLt
    dsimp [row]
    omega
  obtain ⟨u, huA, hGuard, hExtra⟩ := steadyPageSlotGuard hp hb slot more hBound hs
  obtain ⟨hRead, hPage, hRowWord, tail, hAt, hTail⟩ :=
    recurringPageRefreshObservedInPrefixWithFrame hp hX hFrame hb hRow 1 slot hExtra hGuard
      (hr.after_local_nonempty (run_rtg huA) (hDemand.nonempty hr)) hDemand
  exact ⟨⟨hRead, hPage, hRowWord⟩, tail, hAt, hTail⟩

private theorem steadyPageSlotRoute {l : Launch} {g tile tid : Nat} {s : TState}
    {F : List (Nat × Value)} (more : Bool)
    (hKeep : ((kernel.code.drop 1424).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 1424 ([(11, .pred more), (1148, b32 (primingLaneRow tile tid))] ++ F)) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      At u (if more then 1401 else 1427)
        ([(7182, b32 1), (778, .pred false), (1148, b32 (primingLaneRow tile tid))] ++ F) := by
  have hCore : Seg kernel [] l g 2 1424 [] 1426 [(7182, b32 1), (778, .pred false)] := by
    intro t ht
    seg_fp ht using rfl
  obtain ⟨a, ha, hA⟩ := hCore s (hs.mono (G := []) trivial)
  have hReg := (holds_append ..).mp hs.2.2.2.2
  have hExtra : ((kernel.code.drop 1424).take 2).all
      (fun ins => (11 :: 1148 :: F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
      true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hCoreKeep : ((kernel.code.drop 1424).take 2).all
        (fun i => [11, 1148].all (fun r => !(writesRegs i.op).contains r)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hOwn := List.all_eq_true.mp hCoreKeep ins hm
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hOwn ⊢
    exact ⟨hOwn.1, hOwn.2, List.all_eq_true.mp hKeep ins hm⟩
  obtain ⟨haA, haFrame⟩ := loaderLinear (regs := 11 :: 1148 :: F.map Prod.fst)
    (by decide) (by decide) hs.1 hExtra (by set_option maxRecDepth 100000 in kernel_rfl) ha
  have hPred := (haFrame 11 (by simp)).trans hReg.1.1
  have hWord := (haFrame 1148 (by simp)).trans hReg.1.2.1
  have hF := holdsSchedulerFrame hReg.2 haFrame
    (fun r hm => .tail 11 (.tail 1148 (List.mem_map_of_mem hm)))
  have hAt : At a 1426
      ([(7182, b32 1), (778, .pred false), (1148, b32 (primingLaneRow tile tid))] ++ F) :=
    hA.mono ⟨hA.2.2.2.2.1, hA.2.2.2.2.2.1, hWord, hF⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1426 more hAt hPred (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hAt.1 (by simp) rfl hu
  exact ⟨u, run_comp haA huA, hU⟩

set_option maxRecDepth 100000 in
/-- Materialize the actual inner-slot offset before the steady page index arithmetic. -/
theorem steadyPageSlotInput {l : Launch} {g batch head trips warp tid tile : Nat} (slot : Fin 2)
    (more : Bool) {s : TState}
    (hs : At s 1401 ([(7182, b32 slot.val), (778, .pred more),
      (1148, b32 (primingLaneRow tile tid))] ++ steadyCacheFrame p l batch head trips warp tid)) :
    ∃ t, run kernel Assumptions.all l g 2 s = some t ∧
      At t 1403 ([(1148, b32 (primingLaneRow tile tid)), (2131, b32 (64 * slot.val))] ++
        steadySlotFrame p l batch head trips warp tid tile slot more) := by
  let F := steadyCacheFrame p l batch head trips warp tid
  let G := [(7182, b32 slot.val), (1148, b32 (primingLaneRow tile tid))] ++ F
  have hCore : Seg kernel [] l g 2 1401 [(7182, b32 slot.val), (778, .pred more)] 1403
      [(11, .pred more), (2131, b32 (64 * slot.val))] := by
    fin_cases slot <;> intro u hu <;> seg_fp hu using rfl
  obtain ⟨t, ht, hT⟩ := hCore s (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩)
  obtain ⟨htA, htF⟩ := loaderLinear (regs := G.map Prod.fst) (by decide) (by decide) hs.1
    (by kernel_rfl) (by kernel_rfl) ht
  have hKeep := holdsSchedulerFrame
    (show Holds s.regs G from ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.2⟩) htF
    (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨t, htA, hT.mono ⟨hKeep.2.1, hT.2.2.2.2.2.1, hKeep.1, hT.2.2.2.2.1,
    hKeep.2.1, hKeep.2.2⟩⟩

private theorem steadySecondPageInput {l : Launch} {thread batch head trips warp tid tile : Nat}
    {a : TState} (hA : At a 1424 (steadySlotFrame p l batch head trips warp tid tile 0 true)) :
    ∃ c, Relation.ReflTransGen (Tau kernel Assumptions.all l thread) a c ∧
      At c 1403 ([(1148, b32 (primingLaneRow tile tid)), (2131, b32 64)] ++
        steadySlotFrame p l batch head trips warp tid tile 1 false) := by
  let F := steadyCacheFrame p l batch head trips warp tid
  have hRoute : At a 1424 ([(11, .pred true), (1148, b32 (primingLaneRow tile tid))] ++ F) :=
    hA.mono hA.2.2.2.2.2
  obtain ⟨b, hbRun, hB⟩ := steadyPageSlotRoute (l := l) (g := thread) true
    (by set_option maxRecDepth 100000 in kernel_rfl) hRoute
  have hB' : At b 1401 ([(7182, b32 (1 : Fin 2).val), (778, .pred false),
      (1148, b32 (primingLaneRow tile tid))] ++ F) := hB
  obtain ⟨c, hc, hC⟩ := steadyPageSlotInput (g := thread) 1 false hB'
  exact ⟨c, run_rtg (run_comp hbRun hc), hC⟩

set_option maxRecDepth 10000 in
/-- One actual steady traversal refreshes both page cells and their lane row
words before leaving the inner scratch loop. -/
theorem steadyPageWordsFromIndex {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {thread pos j batch head trips warp tid tile : Nat} (hb : batch < p.batch)
    (hRow : primingLaneRow tile tid + 64 < 2 ^ 31) {s : TState} {ending : Option TState}
    (hInput : At s 1403 ([(1148, b32 (primingLaneRow tile tid)),
      (2131, b32 (64 * (0 : Fin 2).val))] ++
      steadySlotFrame p l batch head trips warp tid tile 0 true))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending) {e : Event}
    (he : X.get (thread, j) = some e) (hBefore : pos ≤ j) (hLate : 1423 < e.pc) :
    let base := primingLaneRow tile tid
    let second := pos + primingScratchReads p batch base + 2
    let next := second + primingScratchReads p batch (base + 64) + 2
    SteadyPageWords p l X thread pos batch base 0 ∧
      SteadyPageWords p l X thread second batch (base + 64) 1 ∧ next ≤ j ∧
      ∃ u, At u 1424 (steadySlotFrame p l batch head trips warp tid tile 1 false) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop next) ending ∧
        PrefixDemand X thread next (rowRefreshPc 1) ending ∧
        ((X.tr thread).take next).countP Execution.isShfl =
          ((X.tr thread).take pos).countP Execution.isShfl := by
  let base := primingLaneRow tile tid
  have hDemand : PrefixDemand X thread pos (rowRefreshPc 1) ending :=
    .inr ⟨j, e, hBefore, hLate, he⟩
  obtain ⟨hFirst, a, hA, ha⟩ := steadyPageSlotRun hp hX hFrame hb 0 true hRow hInput hr hDemand
  have hFirst' : SteadyPageWords p l X thread pos batch base 0 := by
    simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hFirst
  let second := pos + primingScratchReads p batch base + 2
  have ha' : Run kernel Assumptions.all l thread a ((X.tr thread).drop second) ending := by
    simpa only [second, Fin.val_zero, Nat.mul_zero, Nat.add_zero] using ha
  have haDemand := hFirst'.advance hDemand
  obtain ⟨c, hc, hC⟩ := steadySecondPageInput hA
  have hcRun := ha'.after_local_nonempty hc (haDemand.nonempty ha')
  obtain ⟨hSecond, d, hD, hd⟩ := steadyPageSlotRun hp hX hFrame hb 1 false hRow hC hcRun haDemand
  have hSecond' : SteadyPageWords p l X thread second batch (base + 64) 1 := by
    simpa only [Fin.val_one, Nat.mul_one] using hSecond
  have hDemand' := hSecond'.advance haDemand
  have haBefore := hFirst'.beforeLater he hBefore hLate
  have hDBefore := hSecond'.beforeLater he haBefore hLate
  refine ⟨hFirst', hSecond', hDBefore, d, hD, ?_, hDemand', ?_⟩
  · simpa only [Fin.val_one, Nat.mul_one] using hd
  · exact hSecond'.shuffleRank.trans hFirst'.shuffleRank

/-- Once the second steady slot is refreshed the actual lane leaves the two-slot loop. -/
theorem steadyPageLoopExit {l : Launch} {g batch head trips warp tid tile : Nat} {s : TState}
    (hs : At s 1424 (steadySlotFrame p l batch head trips warp tid tile 1 false)) :
    ∃ t, run kernel Assumptions.all l g 3 s = some t ∧
      At t 1427 (steadyCacheFrame p l batch head trips warp tid) := by
  obtain ⟨t, ht, hT⟩ := steadyPageSlotRoute (l := l) (g := g) false
    (F := steadyCacheFrame p l batch head trips warp tid)
    (by set_option maxRecDepth 100000 in kernel_rfl) (hs.mono hs.2.2.2.2.2)
  exact ⟨t, ht, hT.mono hT.2.2.2.2.2.2.2⟩

/-- Both live page lookups of this traversal have their launch-backed address. -/
theorem steadyPageWordOfRankedRead {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {thread pos j batch head trips warp tid tile : Nat} (hb : batch < p.batch)
    (hRow : primingLaneRow tile tid + 64 < 2 ^ 31) {s : TState} {ending : Option TState}
    (hInput : At s 1403 ([(1148, b32 (primingLaneRow tile tid)), (2131, b32 0)] ++
      steadySlotFrame p l batch head trips warp tid tile 0 true))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending) {a : Acc}
    {bytes : List (Option Byte)} (he : X.get (thread, j) = some ⟨1416, .rd a bytes⟩)
    (hBefore : pos ≤ j)
    (hRank : ((X.tr thread).take j).countP Execution.isShfl =
      ((X.tr thread).take pos).countP Execution.isShfl) :
    ∃ row < p.kLength batch,
      a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4} := by
  let base := primingLaneRow tile tid
  have lookup (slot : Fin 2) (more : Bool) {startPos : Nat} {before : TState}
      (hFrom : startPos ≤ j)
      (hAt : At before 1403 ([(1148, b32 base), (2131, b32 (64 * slot.val))] ++
        steadySlotFrame p l batch head trips warp tid tile slot more))
      (hRun : Run kernel Assumptions.all l thread before ((X.tr thread).drop startPos) ending) :
      let row := base + 64 * slot.val
      (row < p.kLength batch ∧
        a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}) ∨
      ∃ next ≤ j, ∃ u, At u 1424 (steadySlotFrame p l batch head trips warp tid tile slot more) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop next) ending ∧
        ((X.tr thread).take next).countP Execution.isShfl =
          ((X.tr thread).take startPos).countP Execution.isShfl := by
    have hBound : base + 64 * slot.val < 2 ^ 31 := by have := slot.isLt; omega
    obtain ⟨u, hu, hU, hExtra⟩ := steadyPageSlotGuard hp hb slot more hRow hAt
    exact recurringPageLookupOrNextSlot hp hX hFrame hb hBound 1 slot hExtra hU
      (hRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hFrom)) hFrom he
  rcases lookup 0 true hBefore hInput hr with h | ⟨next, hNext, u, hu, hU, hNextRank⟩
  · exact ⟨_, h.1, h.2⟩
  obtain ⟨v, hv, hV⟩ := steadySecondPageInput hu
  have hVRun := hU.after_local_nonempty hv (traceAfterObservedEvent he hNext)
  rcases lookup 1 false hNext hV hVRun with h | ⟨last, hLast, w, hw, hW, hLastRank⟩
  · exact ⟨_, h.1, h.2⟩
  obtain ⟨exit, hLocal, hExit⟩ := steadyPageLoopExit hw
  have hSuffix := hW.after_local_nonempty (run_rtg hLocal) (traceAfterObservedEvent he hLast)
  exact (noPageAfterSlotsAtSameRank 1 hExit.1 hExit.2.1 hExit.2.2.1 hExit.2.2.2.1
    hSuffix hLast he (hRank.trans (hLastRank.trans hNextRank).symm)).elim

end
end PTX.Kernels.TmlFa4Fwd.Loader
