-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchSave
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Flow.Code.Part015
import Lemmas.Flow.NotClc
import Lemmas.Flow.NotRmw
import Lemmas.Flow.NotShfl
import Lemmas.Flow.Final
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue

noncomputable section

private def notPointerEvent (e : Event) : Bool :=
  match e.kind with
  | .wr .. | .rmw .. | .shfl .. => true
  | _ => false

private theorem warmPointerWindowNoWrite {l : Launch} {g : Nat} {s u : TState}
    {e : Event} {lo hi : Nat} (hLo : lo ≤ s.pc) (hHi : s.pc < hi)
    (hAudit : ((kernel.code.drop lo).take (hi - lo)).all
      (fun i => !writeOp i.op && !atomicOp i.op && !i.op.isShfl) = true)
    (hStep : EStep kernel Assumptions.all l g s e (some u)) :
    notPointerEvent e = false := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
  have hm : ins ∈ (kernel.code.drop lo).take (hi - lo) := by
    apply List.mem_of_getElem? (i := s.pc - lo)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  have hSafe := List.all_eq_true.mp hAudit ins hm
  cases hk : e.kind <;> simp only [notPointerEvent, hk]
  case wr a bs => simp [fires_write_op hf hk] at hSafe
  case rmw a old new => simp [fires_rmw_op hf hk] at hSafe
  case shfl mode input select clamp out checked =>
    have hShfl : Execution.isShfl e = true := by
      obtain ⟨pc, kind⟩ := e
      change kind = _ at hk
      subst kind
      rfl
    simp [fires_shfl_op hf hShfl] at hSafe

private theorem shuffleRankOfPointerFreeEvents {X : Execution} {g index : Nat}
    {front : List Event} (hTrace :
      (X.tr g).drop index = front ++ (X.tr g).drop (index + front.length))
    (hEvents : front.countP notPointerEvent = 0) :
    ((X.tr g).take (index + front.length)).countP Execution.isShfl =
      ((X.tr g).take index).countP Execution.isShfl := by
  have hShuffles : front.countP Execution.isShfl = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hm
    have hn := List.countP_eq_zero.mp hEvents e hm
    obtain ⟨pc, kind⟩ := e
    cases kind <;> simp_all [notPointerEvent, Execution.isShfl]
  rw [List.take_add, hTrace, List.take_append_length, List.countP_append, hShuffles, Nat.add_zero]

private theorem noAccessInUnwrittenSpan {X : Execution} {g start : Nat}
    {front : List Event} (hTrace :
      (X.tr g).drop start = front ++ (X.tr g).drop (start + front.length))
    (hWrites : front.countP notPointerEvent = 0) :
    ∀ j, start ≤ j → j < start + front.length → ∀ a, ¬ X.Access (g, j) a true := by
  intro j hLe hLt a hAcc
  have impossible {e : Event} (he : X.get (g, j) = some e)
      (hk : notPointerEvent e = true) : False := by
    have hGet : ((X.tr g).drop start)[j - start]? = some e := by
      rwa [List.getElem?_drop, Nat.add_sub_of_le hLe]
    rw [hTrace, List.getElem?_append_left (by omega)] at hGet
    exact List.countP_eq_zero.mp hWrites e (List.mem_of_getElem? hGet) hk
  rcases hAcc with ⟨_, _, hTruth⟩ | ⟨bytes, ⟨pc, he⟩, _⟩ | ⟨old, new, pc, he⟩
  · cases hTruth
  · exact impossible he rfl
  · exact impossible he rfl

private theorem warmPointerSeed {l : Launch} {g : Nat} :
    Seg kernel [] l g 3 963 [] 966 [(9537, b64 0), (776, .pred true), (9, .pred true)] := by
  intro s hs
  seg_fp hs using rfl

variable {p : Params}

set_option maxRecDepth 10000 in
/-- After refreshing the page cells, the real wait leaves both of them untouched
and reaches the first pointer save with the same shuffle ordinal. -/
theorem warmKeyPointerCursorFromPages {l : Launch} {X : Execution}
    {thread nextIndex j batch head trips warp tid tile : Nat} {s : TState} {ending : Option TState}
    (hs : At s 954 (warmSlotFrame p l batch head trips warp tid tile 1 false))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop nextIndex) ending) {e : Event}
    (he : X.get (thread, j) = some e) (hBefore : nextIndex ≤ j) (hLate : 977 < e.pc)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ index, nextIndex ≤ index ∧ index ≤ j ∧
      (∀ k, nextIndex ≤ k → k < index → ∀ a, ¬ X.Access (thread, k) a true) ∧
      ((X.tr thread).take index).countP Execution.isShfl =
        ((X.tr thread).take nextIndex).countP Execution.isShfl ∧
      ∃ t ending',
        At t 966 ([(9537, b64 0), (776, .pred true), (9, .pred true)] ++
          warmCacheFrame p l batch head trips warp tid) ∧
        Run kernel Assumptions.all l thread t ((X.tr thread).drop index) ending' := by
  let F := warmCacheFrame p l batch head trips warp tid
  obtain ⟨t, ht, hT⟩ := warmPageLoopExit (g := thread) hs
  have htRun := hr.after_local_nonempty (run_rtg ht) (traceAfterObservedEvent he hBefore)
  have hAudit : ∀ branch, ((kernel.code.drop 957).take (963 - 957)).all
      (fun ins => loaderPipelineCutOp 957 963 branch (F.map Prod.fst) ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨u, front, stop, hTrace, hU, huRun, hWrites, huBefore⟩ :=
    prefixStableCut (stop := 963) (by decide) hAudit hT htRun he hBefore hSafe
      (fun _ => 0) notPointerEvent (.inl (by omega))
      (by
        intro t e hs
        obtain ⟨tm, _, hf⟩ := hs
        rcases fires_none_ends hf with ⟨f, h⟩ | h <;> simp [notPointerEvent, h])
      (by intros; rfl)
      (by
        intro v w ev hLo hHi _ _ h
        rcases h with ⟨rfl, _⟩ | ⟨_, rfl, hs⟩
        · rfl
        · have hAudit : ((kernel.code.drop 957).take (963 - 957)).all
              (fun i => !writeOp i.op && !atomicOp i.op && !i.op.isShfl) = true := by
            set_option maxRecDepth 100000 in kernel_rfl
          simp [warmPointerWindowNoWrite hLo hHi hAudit hs])
  obtain ⟨v, hv, hV⟩ := warmPointerSeed (l := l) (g := thread) u (hU.mono (G := []) trivial)
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) hU.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hVF := holdsSchedulerFrame hU.2.2.2.2 hvFrame (fun _ hm => List.mem_map_of_mem hm)
  have hvRun := huRun.after_local_nonempty (run_rtg hvA) (traceAfterObservedEvent he huBefore)
  let index := nextIndex + front.length
  refine ⟨index, Nat.le_add_right _ _,
    huBefore, noAccessInUnwrittenSpan hTrace hWrites,
    shuffleRankOfPointerFreeEvents hTrace hWrites, v, stop, ?_, hvRun⟩
  exact hV.mono ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hVF⟩

private theorem accessOfObservedWrite {X : Execution} {i : EvId} {a dst : Acc}
    {pc : Nat} {words : List Byte} (h : X.get i = some ⟨pc, .wr a words⟩)
    (hw : X.Access i dst true) : dst = a := by
  rcases hw with ⟨_, _, hf⟩ | ⟨_, ⟨_, hGet⟩, _⟩ | ⟨_, _, _, hGet⟩
  · cases hf
  · exact (Kind.wr.inj (congrArg Event.kind (Option.some.inj (hGet.symm.trans h)))).1
  · cases Option.some.inj (hGet.symm.trans h)

private theorem WarmPageWords.writtenInSlot {l : Launch} {X : Execution} {g pos batch row j : Nat}
    {slot : Fin 2} {a : Acc} (h : WarmPageWords p l X g pos batch row slot) (hLo : pos ≤ j)
    (hHi : j < pos + primingScratchReads p batch row + 2) (hw : X.Access (g, j) a true) :
    (j = pos + primingScratchReads p batch row ∧ a = pageRefreshAccess l g 0 false slot) ∨
    (j = pos + primingScratchReads p batch row + 1 ∧ a = pageRefreshAccess l g 0 true slot) := by
  let skips := primingScratchReads p batch row
  have hFirst : pos + skips ≤ j := by
    by_cases hlive : row < p.kLength batch
    · by_contra! hPast
      have hj : j = pos := by simp [skips, primingScratchReads, hlive] at hPast; omega
      subst j
      exact observedReadNoWrite (h.read hlive) hw
    · simpa [skips, primingScratchReads, hlive] using hLo
  rcases Nat.eq_or_lt_of_le hFirst with hEq | hLater
  · exact .inl ⟨hEq.symm, accessOfObservedWrite h.page (hEq ▸ hw)⟩
  · have hEq : j = pos + skips + 1 := by change j < pos + skips + 2 at hHi; omega
    exact .inr ⟨hEq, accessOfObservedWrite h.rowWord (hEq ▸ hw)⟩

private theorem laterScratchWordApart (l : Launch) (g k : Nat) (hk : k < 4)
    (write target : Bool) (slot : Fin 2) (hDifferent : write ≠ target ∨ slot ≠ 0) :
    ¬ (pageRefreshAccess l g 0 write slot).Covers
      ((pageRefreshAccess l g 0 target 0).loc.at k) := by
  cases write <;> cases target <;> fin_cases slot <;>
    simp [pageRefreshAccess, recurringPageStoreSite, scratchReloadAccess, recurringScratchWord,
      kvLocalOffset, Acc.Covers, Loc.InRange, Loc.at] at hDifferent ⊢ <;> omega

private theorem firstWarmWordLatest {l : Launch} {X : Execution} {g pos batch row index : Nat}
    (target : Bool) (hFirst : WarmPageWords p l X g pos batch row 0)
    (hSecond : WarmPageWords p l X g (pos + primingScratchReads p batch row + 2) batch (row + 64) 1)
    (hUnwritten : let second := pos + primingScratchReads p batch row + 2
      let next := second + primingScratchReads p batch (row + 64) + 2
      ∀ k, next ≤ k → k < index → ∀ a, ¬ X.Access (g, k) a true) :
    ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((pageRefreshAccess l g 0 target 0).loc.at k) →
      j ≤ pos + primingScratchReads p batch row + (if target then 1 else 0) ∨ index ≤ j := by
  intro k hk j dst ha hc
  let idx := pos + primingScratchReads p batch row
  let second := idx + 2
  let nextIndex := second + primingScratchReads p batch (row + 64) + 2
  by_contra! hPast
  by_cases hTail : nextIndex ≤ j
  · exact hUnwritten j hTail hPast.2 dst ha
  by_cases hSecondStart : second ≤ j
  · rcases hSecond.writtenInSlot hSecondStart (by omega) ha with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact laterScratchWordApart l g k hk false target 1 (.inr (by decide)) hc
    · exact laterScratchWordApart l g k hk true target 1 (.inr (by decide)) hc
  have hFirstOrd : idx < j := by
    have hWord := hPast.1
    change idx + (if target then 1 else 0) < j at hWord
    omega
  have hFirstStart : pos ≤ j := by dsimp [idx] at hFirstOrd; omega
  rcases hFirst.writtenInSlot hFirstStart (Nat.lt_of_not_ge hSecondStart) ha with
      ⟨hEq, _⟩ | ⟨hEq, rfl⟩
  · exact Nat.ne_of_lt hFirstOrd hEq.symm
  have hTarget : target = false := by
    cases target
    · rfl
    · have hWord : idx + 1 < j := by simpa only [↓reduceIte] using hPast.1
      omega
  exact laterScratchWordApart l g k hk true target 0 (.inl (by simp [hTarget])) hc

set_option maxRecDepth 10000 in
/-- The selected warm page words determine the saved pointer and the next slot state. -/
theorem warmKeyPointerSave {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pos index batch head trips warp tid row : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (slot : Fin 2) (more : Bool)
    (hMeta : WarmPageWords p l X g pos batch row slot)
    (hBefore : pos + primingScratchReads p batch row + 2 ≤ index) {s : TState}
    {ending : Option TState}
    (hs : At s 966 ([(9537, b64 slot.val), (9, .pred more)] ++
      warmCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index 977 ending)
    (hLast : ∀ (target : Bool), ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((pageRefreshAccess l g 0 target slot).loc.at k) →
      j ≤ pos + primingScratchReads p batch row + (if target then 1 else 0) ∨ index ≤ j) :
    let ptr := primingKRowPointer p batch head row
    X.get (g, index) = some ⟨968,
      .rd (pageRefreshAccess l g 0 false slot)
        ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (g, index + 1) = some ⟨970,
      .rd (pageRefreshAccess l g 0 true slot) ((b32 (row % 16)).toBytes.map some)⟩ ∧
    X.get (g, index + 2) =
      some ⟨977, .wr (pointerSaveAccess l g 0 slot) (b64 ptr).toBytes⟩ ∧
    ∃ u, At u 978 ((9, .pred more) :: warmCacheFrame p l batch head trips warp tid) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 3)) ending := by
  let page := primingScratchPage p batch row
  let ps := p.kLayout.pageStride
  let rs := p.kLayout.rowStride
  let base := p.kLayout.base + 2 * (head * p.kLayout.headStride)
  let pw := pos + primingScratchReads p batch row
  let rw := pw + 1
  let F := (9, .pred more) :: warmCacheFrame p l batch head trips warp tid
  have hPageBound : page < p.pages := primingScratchPageBound hp hb
  have hPageSigned : page < 2 ^ 31 := by
    dsimp [page, primingScratchPage]
    split
    · exact ((hp.pageTable batch hb).2 (row / 16) (by omega)).2
    · decide
  have hRow := Nat.mod_lt row (show 0 < 16 by decide)
  have hPS : ps < 2 ^ 64 := (hp.objectBytes 1 40 8 ps (by simp [ps, Params.objectWords])).1
  have hRS : rs < 2 ^ 64 := (hp.objectBytes 1 24 8 rs (by simp [rs, Params.objectWords])).1
  obtain ⟨hPointer, hFit, _⟩ := sourceScratchPayload_live hp 0 hPageBound hRow hh
  change sourceScratchPayload page (row % 16) ps rs base = primingKRowPointer p batch head row
    at hPointer
  have hAt : At s 966 (recurringScratchSaveInput l 0 slot ps rs base ++ F) := by
    apply hs.mono
    apply (holds_append ..).mpr
    refine ⟨?_, hs.2.2.2.2.2⟩
    simp only [recurringScratchSaveInput, recurringScratchCarry, recurringSaveInputs,
      pointerReloadBase, pointerReloadAddress, List.cons_append, List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first | trivial | exact holds_lookup hs.2.2.2.2 rfl
  have hExtra : RecurringSaveFrame 0 F := by
    have hFresh : (F.map Prod.fst).all (fun r => decide (r ≠ 7656 ∧ r ≠ 7658)) = true := rfl
    have hf (pair : Nat × Value) (hm : pair ∈ F) : pair.1 ≠ 7656 ∧ pair.1 ≠ 7658 :=
      of_decide_eq_true (List.all_eq_true.mp hFresh _ (List.mem_map_of_mem hm))
    exact ⟨by set_option maxRecDepth 100000 in kernel_rfl, fun pair hm => (hf pair hm).1,
      by set_option maxRecDepth 100000 in kernel_rfl, fun pair hm => (hf pair hm).2,
      by set_option maxRecDepth 100000 in kernel_rfl⟩
  obtain ⟨hReadPage, hReadRow, hWrite, hTail⟩ :=
    recurringScratchSaveObservedInPrefixWithFrame hp hX 0 slot (pw := pw) (rw := rw)
      (g := g) (page := page) (row := row % 16) (ps := ps) (rs := rs) (base := base)
      (by dsimp only [pw]; omega) (by dsimp only [rw, pw]; omega) hPageSigned
      (by omega : row % 16 < 2 ^ 31) hPS hRS hFit hExtra hAt hr hDemand hMeta.page hMeta.rowWord
      (by simpa [pw, pageRefreshAccess, recurringPageStoreSite] using hLast false)
      (by simpa [rw, pw, pageRefreshAccess, recurringPageStoreSite] using hLast true)
  change X.get (g, index + 2) =
    some ⟨977, .wr (pointerSaveAccess l g 0 slot)
      (b64 (sourceScratchPayload page (row % 16) ps rs base)).toBytes⟩ at hWrite
  rw [hPointer] at hWrite
  exact ⟨hReadPage, hReadRow, hWrite, hTail⟩

private theorem warmPointerRoute {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} (more : Bool)
    (hKeep : ((kernel.code.drop 978).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 978 ((9, .pred more) :: F)) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      At u (if more then 965 else 981) ((9537, b64 1) :: (776, .pred false) :: F) := by
  have hCore : Seg kernel [] l g 2 978 [] 980 [(9537, b64 1), (776, .pred false)] := by
    intro t ht
    seg_fp ht using rfl
  obtain ⟨a, ha, hA⟩ := hCore s (hs.mono (G := []) trivial)
  have hExtra : ((kernel.code.drop 978).take 2).all
      (fun ins => (9 :: F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hNine : ((kernel.code.drop 978).take 2).all
        (fun i => !(writesRegs i.op).contains 9) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨List.all_eq_true.mp hNine ins hm, List.all_eq_true.mp hKeep ins hm⟩
  obtain ⟨haA, haFrame⟩ := loaderLinear (regs := 9 :: F.map Prod.fst)
    (by decide) (by decide) hs.1 hExtra (by set_option maxRecDepth 100000 in kernel_rfl) ha
  have hPred := (haFrame 9 (by simp)).trans hs.2.2.2.2.1
  have hF := holdsSchedulerFrame hs.2.2.2.2.2 haFrame
    (fun r hm => .tail 9 (List.mem_map_of_mem hm))
  have hAt : At a 980 ((9537, b64 1) :: (776, .pred false) :: F) :=
    hA.mono ⟨hA.2.2.2.2.1, hA.2.2.2.2.2.1, hF⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_980 more hAt hPred (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hAt.1 (by simp) rfl hu
  exact ⟨u, run_comp haA huA, hU⟩

private theorem warmPointerSecondEntry {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)}
    (hCode : ((kernel.code.drop 965).take 1).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 965 ((9537, b64 1) :: (776, .pred false) :: F)) :
    ∃ u, run kernel Assumptions.all l g 1 s = some u ∧
      At u 966 ((9537, b64 1) :: (9, .pred false) :: F) := by
  have hCore : Seg kernel [] l g 1 965 [(776, .pred false)] 966 [(9, .pred false)] := by
    intro t ht
    let u := next (setReg t 9 (.pred false))
    have hU : At u 966 [(9, .pred false)] := (ht.mono (G := []) trivial).set (by simp)
    refine ⟨u, run_local Flow.code_965 rfl ht ?_, hU⟩
    rw [execLocalA_nil]
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, readPred, readReg,
      ht.2.2.2.2.1, u,
      bind, Except.bind, pure, Except.pure]
  obtain ⟨u, hu, hU⟩ := hCore s (hs.mono ⟨hs.2.2.2.2.2.1, trivial⟩)
  have hKeep : ((kernel.code.drop 965).take 1).all
      (fun ins => (9537 :: F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
      true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hIdx : ((kernel.code.drop 965).take 1).all
        (fun i => !(writesRegs i.op).contains 9537) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨List.all_eq_true.mp hIdx ins hm, List.all_eq_true.mp hCode ins hm⟩
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := 9537 :: F.map Prod.fst)
    (by decide) (by decide) hs.1 hKeep rfl hu
  exact ⟨u, huA, hU.mono ⟨(huFrame 9537 (by simp)).trans hs.2.2.2.2.1,
    hU.2.2.2.2.1, holdsSchedulerFrame hs.2.2.2.2.2.2 huFrame
      (fun r hm => .tail 9537 (List.mem_map_of_mem hm))⟩⟩

private theorem secondWarmWordLatest {l : Launch} {X : Execution} {g pos batch row index : Nat}
    (target : Bool) (hSecond : WarmPageWords p l X g pos batch row 1)
    (hUnwritten : ∀ k, pos + primingScratchReads p batch row + 2 ≤ k → k < index →
      ∀ a, ¬ X.Access (g, k) a true) :
    ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((pageRefreshAccess l g 0 target 1).loc.at k) →
      j ≤ pos + primingScratchReads p batch row + (if target then 1 else 0) ∨ index ≤ j := by
  intro k hk j dst ha hc
  let idx := pos + primingScratchReads p batch row
  by_contra! hPast
  by_cases hTail : idx + 2 ≤ j
  · exact hUnwritten j hTail hPast.2 dst ha
  have hFirstOrd : idx < j := by
    have hWord := hPast.1
    change idx + (if target then 1 else 0) < j at hWord
    omega
  have hFirstStart : pos ≤ j := by dsimp [idx] at hFirstOrd; omega
  rcases hSecond.writtenInSlot hFirstStart (Nat.lt_of_not_ge hTail) ha with
      ⟨hEq, _⟩ | ⟨hEq, rfl⟩
  · exact Nat.ne_of_lt hFirstOrd hEq.symm
  have hTarget : target = false := by
    cases target
    · rfl
    · have hWord : idx + 1 < j := by simpa only [↓reduceIte] using hPast.1
      omega
  have hAddr : ¬ (pageRefreshAccess l g 0 true 1).Covers
        ((pageRefreshAccess l g 0 target 1).loc.at k) := by
    subst target
    simp [pageRefreshAccess, recurringPageStoreSite, scratchReloadAccess, recurringScratchWord,
      kvLocalOffset, Acc.Covers, Loc.InRange, Loc.at]
    omega
  exact hAddr hc

/-- Each refreshed metadata word remains the latest covering write when the
two-entry warm page loop finishes. -/
theorem warmPageWordsLatestAtExit {l : Launch} {X : Execution} {g pos batch row : Nat}
    (hFirst : WarmPageWords p l X g pos batch row 0)
    (hSecond : WarmPageWords p l X g (pos + primingScratchReads p batch row + 2) batch (row + 64) 1)
    (slot : Fin 2) (target : Bool) :
    let second := pos + primingScratchReads p batch row + 2
    let stop := second + primingScratchReads p batch (row + 64) + 2
    let write := (if slot.val = 0 then pos + primingScratchReads p batch row
        else second + primingScratchReads p batch (row + 64)) + if target then 1 else 0
    ∀ k < 4, ∀ j < stop, ∀ a, X.Access (g, j) a true →
      a.Covers ((pageRefreshAccess l g 0 target slot).loc.at k) → j ≤ write := by
  dsimp only
  intro k hk j hj a hAccess hCover
  fin_cases slot
  · have h := firstWarmWordLatest (index :=
      pos + primingScratchReads p batch row + 2 + primingScratchReads p batch (row + 64) + 2)
      target hFirst hSecond (by intro _ hLo hHi; omega)
      k hk j a hAccess hCover
    exact h.resolve_right (Nat.not_le.mpr hj)
  · have h := secondWarmWordLatest (index :=
      pos + primingScratchReads p batch row + 2 + primingScratchReads p batch (row + 64) + 2)
      target hSecond (by intros n hLo hHi; omega) k hk j a hAccess hCover
    exact h.resolve_right (Nat.not_le.mpr hj)

private theorem pointerSavesApart (l : Launch) (g byte : Nat) (hb : byte < 8) :
    ¬ (pointerSaveAccess l g 0 1).Covers ((pointerSaveAccess l g 0 0).loc.at byte) := by
  simp [pointerSaveAccess, pointerSaveAddress, pointerReloadAddress,
    Acc.Covers, Loc.InRange, Loc.at]
  omega

private theorem pointerSaveApartFromPageWord (l : Launch) (g k : Nat) (hk : k < 4)
    (target : Bool) :
    ¬ (pointerSaveAccess l g 0 0).Covers ((pageRefreshAccess l g 0 target 1).loc.at k) := by
  cases target <;> simp [pointerSaveAccess, pointerSaveAddress, pointerReloadAddress,
    pageRefreshAccess, recurringPageStoreSite, scratchReloadAccess, recurringScratchWord,
    kvLocalOffset, Acc.Covers, Loc.InRange, Loc.at] <;> omega

/-- A later record cannot be any of the two scratch reads or the pointer save. -/
theorem afterObservedPointerSave {X : Execution} {g start j bound : Nat}
    {target low high save : Event}
    (he : X.get (g, j) = some target) (hBefore : start ≤ j)
    (hLow : X.get (g, start) = some low) (hHigh : X.get (g, start + 1) = some high)
    (hSave : X.get (g, start + 2) = some save)
    (hLate : bound < target.pc) (hL : low.pc ≤ bound) (hH : high.pc ≤ bound)
    (hS : save.pc ≤ bound) :
    start + 3 ≤ j := by
  have avoid {i : Nat} {ev : Event} (hf : X.get (g, i) = some ev)
      (hPc : ev.pc ≤ bound) : i ≠ j := by
    intro heq
    subst j
    exact (Nat.not_le_of_lt hLate) ((Option.some.inj (hf.symm.trans he)) ▸ hPc)
  have := avoid hLow hL
  have := avoid hHigh hH
  have := avoid hSave hS
  omega

set_option maxRecDepth 10000 in
/-- The two true K pointer saves and the following empty-acquire window leave
both per-lane cells ready for the first load of the packet. -/
theorem warmKeyPointersAtReloadFromCursor {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    {thread pos first batch head trips warp tid row j : Nat} (hb : batch < p.batch)
    (hh : head < p.kvHeads) (hFirst : WarmPageWords p l X thread pos batch row 0)
    (hSecond : WarmPageWords p l X thread (pos + primingScratchReads p batch row + 2)
      batch (row + 64) 1)
    (hLoIndex : pos + primingScratchReads p batch row + 2 +
      primingScratchReads p batch (row + 64) + 2 ≤ first)
    (hUnwritten : ∀ k, pos + primingScratchReads p batch row + 2 +
      primingScratchReads p batch (row + 64) + 2 ≤ k → k < first →
      ∀ a, ¬ X.Access (thread, k) a true) {s : TState} {ending : Option TState}
    (hs' : At s 966 ([(9537, b64 0), (9, .pred true)] ++
      warmCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop first) ending) {e : Event}
    (he : X.get (thread, j) = some e) (hBefore : first ≤ j) (hLate : 1003 < e.pc)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ index, index ≤ j ∧
      ((X.tr thread).take index).countP Execution.isShfl =
        ((X.tr thread).take first).countP Execution.isShfl ∧
      ∃ u ending',
        At u 1003 (warmCacheFrame p l batch head trips warp tid) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop index) ending' ∧
        ∀ slot : Fin 2, ∃ write < index,
          X.Writes (thread, write) (pointerSaveAccess l thread 0 slot)
            (b64 (primingKRowPointer p batch head (row + 64 * slot.val))).toBytes ∧
          ∀ byte < 8, ∀ k < index, ∀ a, X.Access (thread, k) a true →
            a.Covers ((pointerSaveAccess l thread 0 slot).loc.at byte) → k ≤ write := by
  let F := warmCacheFrame p l batch head trips warp tid
  let pos2 := pos + primingScratchReads p batch row + 2
  let nextIndex := pos2 + primingScratchReads p batch (row + 64) + 2
  have hAtNext : nextIndex ≤ first := hLoIndex
  have hLate' : 977 < e.pc := by omega
  have hDemand : PrefixDemand X thread first 977 ending := .inr ⟨j, e, hBefore, hLate', he⟩
  obtain ⟨hReadPage0, hReadRow0, hWrite0, a, hA, haRun⟩ :=
    warmKeyPointerSave hp hX hb hh 0 true hFirst
      (by change pos2 ≤ first; dsimp [nextIndex] at hAtNext; omega) hs' hr hDemand
      (fun target => firstWarmWordLatest target hFirst hSecond hUnwritten)
  let second := first + 3
  have haBefore : second ≤ j := afterObservedPointerSave he hBefore hReadPage0 hReadRow0 hWrite0
    hLate' (show 968 ≤ 977 by decide) (show 970 ≤ 977 by decide) (show 977 ≤ 977 by decide)
  obtain ⟨b, hbRoute, hB⟩ := warmPointerRoute (l := l) (g := thread) true
    (by set_option maxRecDepth 100000 in kernel_rfl) hA
  obtain ⟨c, hc, hC⟩ := warmPointerSecondEntry (l := l) (g := thread)
    (by set_option maxRecDepth 100000 in kernel_rfl) hB
  have hcRun := haRun.after_local_nonempty (run_rtg (run_comp hbRoute hc))
    (traceAfterObservedEvent he haBefore)
  have hNewUnwritten : ∀ target k, k < 4 → ∀ ord dst, nextIndex ≤ ord → ord < second →
      X.Access (thread, ord) dst true →
      ¬ dst.Covers ((pageRefreshAccess l thread 0 target 1).loc.at k) := by
    intro target k hk ord dst hLo hHi hAccess hCover
    by_cases hFirstOrder : ord < first
    · exact hUnwritten ord hLo hFirstOrder dst hAccess
    have hSelected : ord = first ∨ ord = first + 1 ∨ ord = first + 2 := by
      dsimp [second] at hHi
      omega
    rcases hSelected with rfl | rfl | rfl
    · exact observedReadNoWrite hReadPage0 hAccess
    · exact observedReadNoWrite hReadRow0 hAccess
    · have hDst := accessOfObservedWrite hWrite0 hAccess
      exact pointerSaveApartFromPageWord l thread k hk target (hDst ▸ hCover)
  have hDemand2 : PrefixDemand X thread second 977 ending := .inr ⟨j, e, haBefore, hLate', he⟩
  have hLast2 (target : Bool) (k : Nat) (hk : k < 4) (ord : Nat) (dst : Acc)
      (hAccess : X.Access (thread, ord) dst true)
      (hCover : dst.Covers ((pageRefreshAccess l thread 0 target 1).loc.at k)) :
      ord ≤ pos2 + primingScratchReads p batch (row + 64) + (if target then 1 else 0) ∨
        second ≤ ord := by
    by_contra! hBad
    by_cases hTail : nextIndex ≤ ord
    · exact hNewUnwritten target k hk ord dst hTail hBad.2 hAccess hCover
    have h := secondWarmWordLatest target hSecond (index := nextIndex)
      (fun _ hLo hHi _ _ => (Nat.not_lt_of_ge hLo hHi).elim) k hk ord dst hAccess hCover
    change ord ≤ pos2 + primingScratchReads p batch (row + 64) +
      (if target then 1 else 0) ∨ nextIndex ≤ ord at h
    exact h.elim (not_le_of_gt hBad.1) hTail
  obtain ⟨hReadPage1, hReadRow1, hWrite1, d, hD, hdRun⟩ :=
    warmKeyPointerSave hp hX hb hh 1 false hSecond
      (by change nextIndex ≤ second; dsimp [second]; omega) hC hcRun hDemand2 hLast2
  let tail := second + 3
  have hDBefore : tail ≤ j := afterObservedPointerSave he haBefore hReadPage1 hReadRow1 hWrite1
    hLate' (show 968 ≤ 977 by decide) (show 970 ≤ 977 by decide) (show 977 ≤ 977 by decide)
  obtain ⟨t, htRoute, ht⟩ := warmPointerRoute (l := l) (g := thread) false
    (by set_option maxRecDepth 100000 in kernel_rfl) hD
  have htRun := hdRun.after_local_nonempty (run_rtg htRoute) (traceAfterObservedEvent he hDBefore)
  have htF : At t 981 F := ht.mono ht.2.2.2.2.2.2
  have hCutCode : ∀ branch, ((kernel.code.drop 981).take (1003 - 981)).all
      (fun ins => loaderPipelineCutOp 981 1003 branch (F.map Prod.fst) ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  have hNoStores : ((kernel.code.drop 981).take (1003 - 981)).all
      (fun i => !writeOp i.op && !atomicOp i.op && !i.op.isShfl) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨u, front, stop, hTrace, hU, hu, hWrites, huBefore⟩ :=
    prefixStableCut (by decide) hCutCode htF htRun he hDBefore hSafe
      (fun _ => 0) notPointerEvent (.inl (by omega))
      (by
        intro t ev ht
        obtain ⟨tm, _, hf⟩ := ht
        rcases fires_none_ends hf with ⟨f, h⟩ | h <;> simp [notPointerEvent, h])
      (by intros; rfl)
      (by
        intro v w ev hLo hHi _ _ h
        rcases h with ⟨rfl, _⟩ | ⟨_, rfl, hs⟩
        · rfl
        · simp [warmPointerWindowNoWrite hLo hHi hNoStores hs])
  let index := tail + front.length
  have hUnwrittenTail := noAccessInUnwrittenSpan hTrace hWrites
  have hRankTail : ((X.tr thread).take tail).countP Execution.isShfl =
      ((X.tr thread).take first).countP Execution.isShfl := by
    have h0 := countShuffleTakeOfNonshuffle hReadPage0 rfl
    have h1 := countShuffleTakeOfNonshuffle hReadRow0 rfl
    have h2 := countShuffleTakeOfNonshuffle hWrite0 rfl
    have h3 := countShuffleTakeOfNonshuffle hReadPage1 rfl
    have h4 := countShuffleTakeOfNonshuffle hReadRow1 rfl
    have h5 := countShuffleTakeOfNonshuffle hWrite1 rfl
    change ((X.tr thread).take (second + 2 + 1)).countP Execution.isShfl = _
    rw [h5, show second + 2 = second + 1 + 1 by omega, h4, h3]
    change ((X.tr thread).take (first + 2 + 1)).countP Execution.isShfl = _
    rw [h2, show first + 2 = first + 1 + 1 by omega, h1, h0]
  refine ⟨index, huBefore,
    (shuffleRankOfPointerFreeEvents hTrace hWrites).trans hRankTail, u, stop, hU, hu, ?_⟩
  intro slot
  by_cases hSlot : slot = 0
  · subst slot
    refine ⟨first + 2, by dsimp [index, tail, second]; omega, ⟨977, ?_⟩, ?_⟩
    · simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hWrite0
    intro byte hByte k hKI dst hAccess hCover
    by_contra! hBad
    by_cases hAfter : tail ≤ k
    · exact hUnwrittenTail k hAfter hKI dst hAccess
    have hK : k = second ∨ k = second + 1 ∨ k = second + 2 := by
      dsimp [tail, second] at hAfter ⊢
      omega
    rcases hK with rfl | rfl | rfl
    · exact observedReadNoWrite hReadPage1 hAccess
    · exact observedReadNoWrite hReadRow1 hAccess
    · have hDst := accessOfObservedWrite hWrite1 hAccess
      exact pointerSavesApart l thread byte hByte (hDst ▸ hCover)
  · have hOne : slot = 1 := Fin.ext (by
      have hNonzero : slot.val ≠ 0 := fun h => hSlot (Fin.ext h)
      have := slot.isLt
      omega)
    subst slot
    refine ⟨second + 2, by dsimp [index, tail]; omega, ⟨977, ?_⟩, ?_⟩
    · simpa only [Fin.val_one, Nat.mul_one] using hWrite1
    intro byte hByte k hKI dst hAccess _
    by_contra! hBad
    have hTailOrder : tail ≤ k := by change second + 3 ≤ k; omega
    exact hUnwrittenTail k hTailOrder hKI dst hAccess

end
end PTX.Kernels.TmlFa4Fwd.Loader
