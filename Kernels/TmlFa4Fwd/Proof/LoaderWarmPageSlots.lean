-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmFirstObserved
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

/-- Recurring copy arithmetic keeps the column word computed in the lane's row prelude. -/
def warmCacheFrame (p : Params) (l : Launch) (batch head trips warp tid : Nat) :
    List (Nat × Value) :=
  (1119, b32 (8 * (tid % 8))) :: warmStartFrame p l batch head trips warp tid

/-- Register facts for the two warm scratch passes. -/
def warmSlotFrame (p : Params) (l : Launch)
    (batch head trips warp tid tile : Nat) (slot : Fin 2) (more : Bool) : List (Nat × Value) :=
  [(7175, b32 slot.val), (8, .pred more), (1118, b32 (128 * tile))] ++
    warmCacheFrame p l batch head trips warp tid

/-- One actual warm slot updates the selected page word and its lane-local row word in order. -/
structure WarmPageWords (p : Params) (l : Launch) (X : Execution)
    (g pos batch row : Nat) (slot : Fin 2) : Prop where
  read : row < p.kLength batch →
    X.get (g, pos) = some ⟨(recurringPageReadSite 0).pc,
      .rd {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
        ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩
  page : X.get (g, pos + primingScratchReads p batch row) =
    some ⟨pageRefreshPc 0,
      .wr (pageRefreshAccess l g 0 false slot) (b32 (primingScratchPage p batch row)).toBytes⟩
  rowWord : X.get (g, pos + primingScratchReads p batch row + 1) =
    some ⟨rowRefreshPc 0, .wr (pageRefreshAccess l g 0 true slot) (b32 (row % 16)).toBytes⟩

private theorem WarmPageWords.advance {p : Params} {l : Launch} {X : Execution}
    {g pos batch row : Nat} {slot : Fin 2} (h : WarmPageWords p l X g pos batch row slot)
    {ending : Option TState} (hDemand : PrefixDemand X g pos (rowRefreshPc 0) ending) :
    PrefixDemand X g (pos + primingScratchReads p batch row + 2) (rowRefreshPc 0) ending := by
  have hAt : PrefixDemand X g (pos + primingScratchReads p batch row) (rowRefreshPc 0) ending := by
    by_cases hLive : row < p.kLength batch
    · simpa [primingScratchReads, hLive] using hDemand.advance (h.read hLive)
        (show (recurringPageReadSite 0).pc ≤ rowRefreshPc 0 by decide)
    · simpa [primingScratchReads, hLive] using hDemand
  have hPagePc : pageRefreshPc 0 ≤ rowRefreshPc 0 := by decide
  simpa only [Nat.add_assoc] using ((hAt.advance h.page hPagePc).advance h.rowWord le_rfl)

/-- An ordinary event does not change the observed shuffle ordinal. -/
theorem countShuffleTakeOfNonshuffle {X : Execution} {g j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (h : Execution.isShfl e = false) :
    ((X.tr g).take (j + 1)).countP Execution.isShfl =
      ((X.tr g).take j).countP Execution.isShfl := by
  have hGet : (X.tr g)[j]? = some e := he
  rw [List.take_add_one, hGet, Option.toList_some, List.countP_append]
  simp [h]

private theorem WarmPageWords.shuffleRank {p : Params} {l : Launch} {X : Execution}
    {g pos batch row : Nat} {slot : Fin 2} (h : WarmPageWords p l X g pos batch row slot) :
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

private theorem WarmPageWords.beforeLater {p : Params} {l : Launch} {X : Execution}
    {g pos j batch row : Nat} {slot : Fin 2} (h : WarmPageWords p l X g pos batch row slot)
    {e : Event} (he : X.get (g, j) = some e) (hBefore : pos ≤ j) (hLate : rowRefreshPc 0 < e.pc) :
    pos + primingScratchReads p batch row + 2 ≤ j := by
  have avoid {k : Nat} {f : Event} (hf : X.get (g, k) = some f)
      (hPc : f.pc ≤ rowRefreshPc 0) : k ≠ j := by
    intro hEq
    subst j
    exact (Nat.not_le_of_lt hLate) ((Option.some.inj (hf.symm.trans he)) ▸ hPc)
  have hPage : pageRefreshPc 0 ≤ rowRefreshPc 0 := by decide
  have hRead : (recurringPageReadSite 0).pc ≤ rowRefreshPc 0 := by decide
  have hFirst := avoid h.page hPage
  have hSecond := avoid h.rowWord le_rfl
  by_cases hLive : row < p.kLength batch
  · have hReadHere := avoid (h.read hLive) hRead
    simp only [primingScratchReads, ite_eq_left hLive] at hFirst hSecond ⊢
    omega
  · simp only [primingScratchReads, ite_eq_right hLive] at hFirst hSecond ⊢
    omega

private theorem warmPageSlotGuard {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m)
    {g batch head trips warp tid tile : Nat} (hb : batch < p.batch) (slot : Fin 2) (more : Bool)
    (hBound : primingLaneRow tile tid + 64 < 2 ^ 31) {s : TState}
    (hs : At s 929 ([(1969, b32 (primingLaneRow tile tid)), (1964, b32 (64 * slot.val))] ++
      warmSlotFrame p l batch head trips warp tid tile slot more)) :
    let row := primingLaneRow tile tid + 64 * slot.val
    let F := warmSlotFrame p l batch head trips warp tid tile slot more
    ∃ u, run kernel Assumptions.all l g 10 s = some u ∧
      At u 939 (recurringPageGuardInput p l 0 slot batch row ++ F) ∧
      RecurringRefreshFrame 0 F := by
  let base := primingLaneRow tile tid
  let row := base + 64 * slot.val
  let F := warmSlotFrame p l batch head trips warp tid tile slot more
  have hSlot := slot.isLt
  have hRow : row < 2 ^ 31 := by dsimp [row, base]; omega
  have hLen : p.kLength batch < 2 ^ 31 := by have := (hp.lengths batch hb).2.2; omega
  have hInput : At s 929 (recurringPageIndexInput 0 base (p.kLength batch) slot) := by
    apply hs.mono
    simp only [recurringPageIndexInput, recurringPageSite, Holds]
    repeat' apply And.intro
    all_goals first | trivial | exact holds_lookup hs.2.2.2.2 rfl
  obtain ⟨u, hu, hU⟩ := recurringPageIndexCore (l := l) (g := g) 0 slot hRow hLen s hInput
  obtain ⟨huA, huF⟩ := loaderLinear (regs := F.map Prod.fst) (lo := 929) (n := 10)
    (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hCarry := holdsSchedulerFrame (show Holds s.regs F from hs.2.2.2.2.2.2)
    huF (fun _ hm => List.mem_map_of_mem hm)
  have hGuard : At u 939 (recurringPageGuardInput p l 0 slot batch row ++ F) := by
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
  have hExtra : RecurringRefreshFrame 0 F := by
    constructor
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
    · rintro ⟨reg, value⟩ hm
      simp [F, warmSlotFrame, warmCacheFrame, warmStartFrame, warmPageRoots, warmLaneRoots,
        primingVScratchAbi, recurringPageSite] at hm ⊢
      aesop
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
  exact ⟨u, huA, hGuard, hExtra⟩

private theorem warmPageSlotRun {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g pos batch head trips warp tid tile : Nat} (hb : batch < p.batch) (slot : Fin 2) (more : Bool)
    (hBound : primingLaneRow tile tid + 64 < 2 ^ 31) {s : TState} {ending : Option TState}
    (hs : At s 929 ([(1969, b32 (primingLaneRow tile tid)), (1964, b32 (64 * slot.val))] ++
      warmSlotFrame p l batch head trips warp tid tile slot more))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hDemand : PrefixDemand X g pos (rowRefreshPc 0) ending) :
    let row := primingLaneRow tile tid + 64 * slot.val
    WarmPageWords p l X g pos batch row slot ∧
      ∃ u, At u 954 (warmSlotFrame p l batch head trips warp tid tile slot more) ∧
        Run kernel Assumptions.all l g u
          ((X.tr g).drop (pos + primingScratchReads p batch row + 2)) ending := by
  let row := primingLaneRow tile tid + 64 * slot.val
  have hRow : row < 2 ^ 31 := by
    have := slot.isLt
    dsimp [row]
    omega
  obtain ⟨u, huA, hGuard, hExtra⟩ := warmPageSlotGuard hp hb slot more hBound hs
  obtain ⟨hRead, hPage, hRowWord, tail, hAt, hTail⟩ :=
    recurringPageRefreshObservedInPrefixWithFrame hp hX hFrame hb hRow 0 slot hExtra hGuard
      (hr.after_local_nonempty (run_rtg huA) (hDemand.nonempty hr)) hDemand
  exact ⟨⟨hRead, hPage, hRowWord⟩, tail, hAt, hTail⟩

private theorem warmPageSlotRoute {l : Launch} {g tile : Nat} {s : TState}
    {F : List (Nat × Value)} (more : Bool)
    (hKeep : ((kernel.code.drop 954).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 954 ([(8, .pred more), (1118, b32 (128 * tile))] ++ F)) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      At u (if more then 921 else 957)
        ([(7175, b32 1), (775, .pred false), (1118, b32 (128 * tile))] ++ F) := by
  have hCore : Seg kernel [] l g 2 954 [] 956 [(7175, b32 1), (775, .pred false)] := by
    intro t ht
    seg_fp ht using rfl
  obtain ⟨a, ha, hA⟩ := hCore s (hs.mono (G := []) trivial)
  have hReg := (holds_append ..).mp hs.2.2.2.2
  have hExtra : ((kernel.code.drop 954).take 2).all
      (fun ins => (8 :: 1118 :: F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
      true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hCoreKeep : ((kernel.code.drop 954).take 2).all
        (fun i => [8, 1118].all (fun r => !(writesRegs i.op).contains r)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hOwn := List.all_eq_true.mp hCoreKeep ins hm
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hOwn ⊢
    exact ⟨hOwn.1, hOwn.2, List.all_eq_true.mp hKeep ins hm⟩
  obtain ⟨haA, haFrame⟩ := loaderLinear (regs := 8 :: 1118 :: F.map Prod.fst)
    (by decide) (by decide) hs.1 hExtra (by set_option maxRecDepth 100000 in kernel_rfl) ha
  have hPred := (haFrame 8 (by simp)).trans hReg.1.1
  have hWord := (haFrame 1118 (by simp)).trans hReg.1.2.1
  have hF := holdsSchedulerFrame hReg.2 haFrame
    (fun r hm => .tail 8 (.tail 1118 (List.mem_map_of_mem hm)))
  have hAt : At a 956 ([(7175, b32 1), (775, .pred false), (1118, b32 (128 * tile))] ++ F) :=
    hA.mono ⟨hA.2.2.2.2.1, hA.2.2.2.2.2.1, hWord, hF⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_956 more hAt hPred (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hAt.1 (by simp) rfl hu
  exact ⟨u, run_comp haA huA, hU⟩

private theorem warmSecondPageInput {p : Params} {l : Launch}
    {thread batch head trips warp tid tile : Nat}
    (hTile : 128 * tile + 127 < 2 ^ 31) (hTid : tid < 512)
    {a : TState} (hA : At a 954
      (warmSlotFrame p l batch head trips warp tid tile 0 true)) :
    ∃ c, Relation.ReflTransGen (Tau kernel Assumptions.all l thread) a c ∧
      At c 929 ([(1969, b32 (primingLaneRow tile tid)), (1964, b32 64)] ++
        warmSlotFrame p l batch head trips warp tid tile 1 false) := by
  let F := warmCacheFrame p l batch head trips warp tid
  have hRoute : At a 954 ([(8, .pred true), (1118, b32 (128 * tile))] ++ F) :=
    hA.mono hA.2.2.2.2.2
  obtain ⟨b, hbRun, hB⟩ := warmPageSlotRoute (l := l) (g := thread) true
    (by set_option maxRecDepth 100000 in kernel_rfl) hRoute
  have hB' : At b 921 ([(1118, b32 (128 * tile)), (1061, b32 tid),
      (7175, b32 (1 : Fin 2).val), (775, .pred false)] ++ F) :=
    hB.mono ⟨hB.2.2.2.2.2.2.1, holds_lookup hB.2.2.2.2 rfl,
      hB.2.2.2.2.1, hB.2.2.2.2.2.1, hB.2.2.2.2.2.2.2⟩
  let R := warmStartFrame p l batch head trips warp tid
  have hBSeed : At b 921 ([(1118, b32 (128 * tile)), (1061, b32 tid),
      (7175, b32 (1 : Fin 2).val), (775, .pred false)] ++ R) :=
    hB'.mono ⟨hB'.2.2.2.2.1, hB'.2.2.2.2.2.1, hB'.2.2.2.2.2.2.1, hB'.2.2.2.2.2.2.2.1,
      hB'.2.2.2.2.2.2.2.2.2⟩
  obtain ⟨c, hc, hC⟩ := warmPageIndexRunFromSlot (l := l) (g := thread) hTile hTid 1 false
    (by set_option maxRecDepth 100000 in kernel_rfl) hBSeed
  exact ⟨c, run_rtg (run_comp hbRun hc), hC⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hX hFrame

set_option maxRecDepth 10000 in
/-- One actual warm traversal refreshes both page cells and their lane row
words before leaving the inner scratch loop. -/
theorem warmPageWordsFromIndex {thread pos j batch head trips warp tid tile : Nat}
    (hb : batch < p.batch) (hTile : 128 * tile + 127 < 2 ^ 31) (hTid : tid < 512)
    (hRow : primingLaneRow tile tid + 64 < 2 ^ 31) {s : TState} {ending : Option TState}
    (hInput : At s 929 ([(1969, b32 (primingLaneRow tile tid)),
      (1964, b32 (64 * (0 : Fin 2).val))] ++
      warmSlotFrame p l batch head trips warp tid tile 0 true))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending) {e : Event}
    (he : X.get (thread, j) = some e) (hBefore : pos ≤ j) (hLate : 953 < e.pc) :
    let base := primingLaneRow tile tid
    let second := pos + primingScratchReads p batch base + 2
    let next := second + primingScratchReads p batch (base + 64) + 2
    WarmPageWords p l X thread pos batch base 0 ∧
      WarmPageWords p l X thread second batch (base + 64) 1 ∧ next ≤ j ∧
      ∃ u, At u 954 (warmSlotFrame p l batch head trips warp tid tile 1 false) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop next) ending ∧
        PrefixDemand X thread next (rowRefreshPc 0) ending ∧
        ((X.tr thread).take next).countP Execution.isShfl =
          ((X.tr thread).take pos).countP Execution.isShfl := by
  let base := primingLaneRow tile tid
  have hDemand : PrefixDemand X thread pos (rowRefreshPc 0) ending :=
    .inr ⟨j, e, hBefore, hLate, he⟩
  obtain ⟨hFirst, a, hA, ha⟩ := warmPageSlotRun hp hX hFrame hb 0 true hRow hInput hr hDemand
  have hFirst' : WarmPageWords p l X thread pos batch base 0 := by
    simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hFirst
  let second := pos + primingScratchReads p batch base + 2
  have ha' : Run kernel Assumptions.all l thread a ((X.tr thread).drop second) ending := by
    simpa only [second, Fin.val_zero, Nat.mul_zero, Nat.add_zero] using ha
  have haDemand := hFirst'.advance hDemand
  obtain ⟨c, hc, hC⟩ := warmSecondPageInput hTile hTid hA
  have hcRun := ha'.after_local_nonempty hc (haDemand.nonempty ha')
  obtain ⟨hSecond, d, hD, hd⟩ := warmPageSlotRun hp hX hFrame hb 1 false hRow hC hcRun haDemand
  have hSecond' : WarmPageWords p l X thread second batch (base + 64) 1 := by
    simpa only [Fin.val_one, Nat.mul_one] using hSecond
  have hDemand' := hSecond'.advance haDemand
  have haBefore := hFirst'.beforeLater he hBefore hLate
  have hDBefore := hSecond'.beforeLater he haBefore hLate
  refine ⟨hFirst', hSecond', hDBefore, d, hD, ?_, hDemand', ?_⟩
  · simpa only [Fin.val_one, Nat.mul_one] using hd
  · exact hSecond'.shuffleRank.trans hFirst'.shuffleRank

omit hp hX hFrame in
/-- Once the second warm slot is refreshed the actual lane leaves the two-slot loop. -/
theorem warmPageLoopExit {p : Params} {l : Launch} {g batch head trips warp tid tile : Nat}
    {s : TState} (hs : At s 954 (warmSlotFrame p l batch head trips warp tid tile 1 false)) :
    ∃ t, run kernel Assumptions.all l g 3 s = some t ∧
      At t 957 (warmCacheFrame p l batch head trips warp tid) := by
  obtain ⟨t, ht, hT⟩ := warmPageSlotRoute (l := l) (g := g) false
    (F := warmCacheFrame p l batch head trips warp tid)
    (by set_option maxRecDepth 100000 in kernel_rfl) (hs.mono hs.2.2.2.2.2)
  exact ⟨t, ht, hT.mono hT.2.2.2.2.2.2.2⟩

/-- Both live page lookups of this traversal have their launch-backed address. -/
theorem warmPageWordOfRankedRead {thread pos j batch head trips warp tid tile : Nat}
    (hb : batch < p.batch) (hTile : 128 * tile + 127 < 2 ^ 31) (hTid : tid < 512)
    (hRow : primingLaneRow tile tid + 64 < 2 ^ 31) {s : TState} {ending : Option TState}
    (hInput : At s 929 ([(1969, b32 (primingLaneRow tile tid)), (1964, b32 0)] ++
      warmSlotFrame p l batch head trips warp tid tile 0 true))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending) {a : Acc}
    {bytes : List (Option Byte)} (he : X.get (thread, j) = some ⟨946, .rd a bytes⟩)
    (hBefore : pos ≤ j)
    (hRank : ((X.tr thread).take j).countP Execution.isShfl =
      ((X.tr thread).take pos).countP Execution.isShfl) :
    ∃ row < p.kLength batch,
      a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4} := by
  let base := primingLaneRow tile tid
  have lookup (slot : Fin 2) (more : Bool) {startPos : Nat} {before : TState}
      (hFrom : startPos ≤ j)
      (hAt : At before 929 ([(1969, b32 base), (1964, b32 (64 * slot.val))] ++
        warmSlotFrame p l batch head trips warp tid tile slot more))
      (hRun : Run kernel Assumptions.all l thread before ((X.tr thread).drop startPos) ending) :
      let row := base + 64 * slot.val
      (row < p.kLength batch ∧
        a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}) ∨
      ∃ next ≤ j, ∃ u, At u 954 (warmSlotFrame p l batch head trips warp tid tile slot more) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop next) ending ∧
        ((X.tr thread).take next).countP Execution.isShfl =
          ((X.tr thread).take startPos).countP Execution.isShfl := by
    have hBound : base + 64 * slot.val < 2 ^ 31 := by have := slot.isLt; omega
    obtain ⟨u, hu, hU, hExtra⟩ := warmPageSlotGuard hp hb slot more hRow hAt
    exact recurringPageLookupOrNextSlot hp hX hFrame hb hBound 0 slot hExtra hU
      (hRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hFrom)) hFrom he
  rcases lookup 0 true hBefore hInput hr with h | ⟨next, hNext, u, hu, hU, hNextRank⟩
  · exact ⟨_, h.1, h.2⟩
  obtain ⟨v, hv, hV⟩ := warmSecondPageInput hTile hTid hu
  have hVRun := hU.after_local_nonempty hv (traceAfterObservedEvent he hNext)
  rcases lookup 1 false hNext hV hVRun with h | ⟨last, hLast, w, hw, hW, hLastRank⟩
  · exact ⟨_, h.1, h.2⟩
  obtain ⟨exit, hLocal, hExit⟩ := warmPageLoopExit hw
  have hSuffix := hW.after_local_nonempty (run_rtg hLocal) (traceAfterObservedEvent he hLast)
  exact (noPageAfterSlotsAtSameRank 0 hExit.1 hExit.2.1 hExit.2.2.1 hExit.2.2.2.1
    hSuffix hLast he (hRank.trans (hLastRank.trans hNextRank).symm)).elim

end
end PTX.Kernels.TmlFa4Fwd.Loader
