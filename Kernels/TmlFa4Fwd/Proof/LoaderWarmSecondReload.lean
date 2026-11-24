-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
import Kernels.TmlFa4Fwd.Flow.Code.Part016
import Lemmas.Flow.NotRmw
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue

noncomputable section

private def warmKSecondReload : SavedPointerReload := ⟨1072, 7293, 8, 2019, 2020⟩

private theorem noScratchWriteBeforeSecondRead {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i : Nat} {a : Acc}
    (hAccess : X.Access (g, i) a true) {e : Event}
    (he : X.get (g, i) = some e) (hPc : 1003 ≤ e.pc ∧ e.pc < 1074) : False := by
  have hAudit : ((kernel.code.drop 1003).take (1074 - 1003)).all
      (fun ins => !writeOp ins.op && !atomicOp ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have impossible {ev : Event} (hGet : X.get (g, i) = some ev) (hs : ∀ f, ev.kind ≠ .ub f)
      (hWrite : ∀ {t : TState} {ins : Instr} {o : Option TState},
        Fires ev.pc (eventTmpl Assumptions.all l g t ins.op) ev o →
          writeOp ins.op = true ∨ atomicOp ins.op = true) : False := by
    obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases get_source hX he with ⟨f, hFault⟩ | ⟨t, ins, o, _, hCode, hf⟩
    · exact hs f hFault
    have hMember : ins ∈ (kernel.code.drop 1003).take (1074 - 1003) := by
      apply List.mem_of_getElem? (i := e.pc - 1003)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hPc.1]
      exact hCode
    have ha := List.all_eq_true.mp hAudit ins hMember
    rcases hWrite hf with h | h <;> simp [h] at ha
  rcases hAccess with ⟨_, _, hFalse⟩ | ⟨data, ⟨pc, hGet⟩, _⟩ | ⟨old, new, pc, hGet⟩
  · cases hFalse
  · exact impossible hGet (by intro f h; cases h) (fun hf => .inl (fires_write_op hf rfl))
  · exact impossible hGet (by intro f h; cases h) (fun hf => .inr (fires_rmw_op hf rfl))

private theorem warmKeyColumnCore {l : Launch} {g tid : Nat} :
    Seg kernel [] l g 1 1007 [(1119, b32 (8 * (tid % 8)))] 1008
      [(7666, b64 (16 * (tid % 8)))] := by
  have hFit : 8 * (tid % 8) < 2 ^ 32 := by omega
  intro s hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hFit, show 8 * (tid % 8) * 2 = 16 * (tid % 8) by omega]

set_option maxRecDepth 100000 in
/-- The one column multiply carries any register frame it does not overwrite. -/
theorem warmKeyColumnPrepared {l : Launch} {g tid : Nat} {s : TState}
    {F : List (Nat × Value)} (hs : At s 1007 F)
    (hColumn : (1119, b32 (8 * (tid % 8))) ∈ F)
    (hFrame : ((kernel.code.drop 1007).take 1).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 1008 ((7666, b64 (16 * (tid % 8))) :: F) := by
  obtain ⟨u, hu, hU⟩ := warmKeyColumnCore (g := g) s
    (hs.mono ⟨holds_mem hs.2.2.2.2 hColumn, trivial⟩)
  obtain ⟨hRun, hKeep⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    hFrame rfl hu
  have hF := holdsSchedulerFrame hs.2.2.2.2 hKeep (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, run_rtg hRun, hU.mono ⟨hU.2.2.2.2.1, hF⟩⟩

set_option maxRecDepth 100000 in
/-- Replay the upper pointer load using the earlier lane-local save, and retain
the column shared by all later pairs. -/
theorem warmSecondKeyPointerReloadFromCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {thread index batch head row trips warp tid j : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads)
    {s : TState} {ending : Option TState}
    (hs : At s 1003 (warmCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop index) ending)
    (hSaved : ∃ write < index, X.Writes (thread, write) (pointerSaveAccess l thread 0 1)
        (b64 (primingKRowPointer p batch head row)).toBytes ∧
      ∀ k < 8, ∀ n < index, ∀ a, X.Access (thread, n) a true →
        a.Covers ((pointerSaveAccess l thread 0 1).loc.at k) → n ≤ write)
    {e : Event} (he : X.get (thread, j) = some e) (hBefore : index ≤ j)
    (hLate : 1072 < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    let ptr := primingKRowPointer p batch head row
    ∃ pos, pos + 2 ≤ j ∧
      ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
        ((X.tr thread).take index).countP Execution.isShfl + 16 ∧
      ∃ u stop,
        At u 1073 ([(2019, b32 (ptr % 2 ^ 32)), (2020, b32 (ptr / 2 ^ 32)),
          (7666, b64 (16 * (tid % 8)))] ++ warmCacheFrame p l batch head trips warp tid) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop (pos + 2)) stop := by
  let ptr := primingKRowPointer p batch head row
  let baseFrame := warmCacheFrame p l batch head trips warp tid
  let F := (7666, b64 (16 * (tid % 8))) :: baseFrame
  let site := warmKSecondReload
  have firstAudit (bound : Nat) : ((kernel.code.drop 1003).take (1007 - 1003)).all
      (fun ins => loaderPipelineCutOp 1003 1007 bound (baseFrame.map Prod.fst) ins.op) = true := by
    kernel_rfl
  have firstRanked : (((kernel.code.drop 1003).take (1007 - 1003)).zipIdx 1003).all
      (fun (i, pc) => LoaderRankedInstr 1007 pc i) = true := by kernel_rfl
  obtain ⟨first, early, earlyStop, _, hFirst, firstRun, firstRank, firstBefore⟩ :=
    prefixRankedShuffleCut (by decide) firstAudit firstRanked hs hr he hBefore
      (.inl (by omega)) hSafe
  obtain ⟨column, hLocal, hColumn⟩ :=
    warmKeyColumnPrepared (g := thread) (tid := tid) hFirst
    (by simp [baseFrame, warmCacheFrame]) (by kernel_rfl)
  have hLive := traceAfterObservedEvent he firstBefore
  have columnRun := firstRun.after_local_nonempty hLocal hLive
  have hAudit (bound : Nat) : ((kernel.code.drop 1008).take (1072 - 1008)).all
      (fun ins => loaderPipelineCutOp 1008 1072 bound (F.map Prod.fst) ins.op) = true := by
    kernel_rfl
  have hRanked : (((kernel.code.drop 1008).take (1072 - 1008)).zipIdx 1008).all
      (fun (i, pc) => LoaderRankedInstr 1072 pc i) = true := by kernel_rfl
  obtain ⟨u, later, stop, _, hu, huRun, huRank, huBefore⟩ :=
    prefixRankedShuffleCut (by decide) hAudit hRanked hColumn columnRun he firstBefore
      (.inl hLate.le) hSafe
  let nextIndex := index + early.length + later.length
  have firstCount : loaderShuffleTail 1007 1003 = 2 := by kernel_rfl
  have restCount : loaderShuffleTail 1072 1008 = 14 := by kernel_rfl
  have upperCount : loaderShuffleTail 1074 1003 = 17 := by kernel_rfl
  have upperAudit (n : Nat) : ((kernel.code.drop 1003).take (1074 - 1003)).all
      (fun ins => loaderPipelineCutOp 1003 1074 n [] ins.op) = true := by kernel_rfl
  have upperRanked : (((kernel.code.drop 1003).take (1074 - 1003)).zipIdx 1003).all
      (fun (ins, pc) => LoaderRankedInstr 1074 pc ins) = true := by kernel_rfl
  obtain ⟨write, hOrder, hSaved, hLast⟩ := hSaved
  have hLast' (byte : Nat) (hByte : byte < 8) (k : Nat) (hk : k < nextIndex) (a : Acc)
      (hA : X.Access (thread, k) a true)
      (hc : a.Covers ((site.cell thread (l.localBase + 32)).loc.at byte)) :
      k ≤ write := by
    by_cases hOld : k < index
    · apply hLast byte hByte k hOld a hA
      exact hc
    have hj : j < (X.tr thread).length := (List.getElem?_eq_some_iff.mp he).1
    have hPresent : k < (X.tr thread).length := by change nextIndex ≤ j at huBefore; omega
    let ev := (X.tr thread)[k]
    have hGet : X.get (thread, k) = some ev := List.getElem?_eq_getElem hPresent
    have hMono := countP_take_mono Execution.isShfl (X.tr thread) hk.le
    have hBudget : ((X.tr thread).take k).countP Execution.isShfl <
        ((X.tr thread).take index).countP Execution.isShfl + loaderShuffleTail 1074 1003 := by
      change ((X.tr thread).take k).countP Execution.isShfl ≤
        ((X.tr thread).take nextIndex).countP Execution.isShfl at hMono
      rw [upperCount]
      change ((X.tr thread).take nextIndex).countP Execution.isShfl =
        ((X.tr thread).take (index + early.length)).countP Execution.isShfl +
          loaderShuffleTail 1072 1008 at huRank
      change ((X.tr thread).take (index + early.length)).countP Execution.isShfl =
        ((X.tr thread).take index).countP Execution.isShfl +
          loaderShuffleTail 1007 1003 at firstRank
      rw [huRank, firstRank, firstCount, restCount] at hMono
      omega
    have hBounds := loaderRankedEventBounds (by decide) upperAudit upperRanked
      hs hr hGet (by omega) hBudget
    exact (noScratchWriteBeforeSecondRead hX hA hGet hBounds).elim
  have hFit : ptr < 2 ^ 64 := by
    have hPage := primingScratchPageBound hp (row := row) hb
    obtain ⟨hEq, hFit, _⟩ := sourceScratchPayload_live hp 0 hPage (Nat.mod_lt row (by decide)) hh
    have hEqual : _ = ptr := hEq
    rwa [hEqual] at hFit
  have hCode : kernel.code[site.pc]? = some ⟨none, .mem site.mem⟩ := Flow.code_1072
  have hAddr : l.localBase + 32 + site.offset < 2 ^ 64 := by
    have h := hp.localMemory.2.1
    change l.localBase + 32 + 8 < 2 ^ 64
    omega
  have hAlign : (l.localBase + 32 + site.offset) % 8 = 0 := by
    have h := hp.localMemory.1
    change (l.localBase + 32 + 8) % 8 = 0
    omega
  have hInput : At u site.pc ((site.baseReg, b64 (l.localBase + 32)) :: F) :=
    hu.mono ⟨holds_lookup hu.2.2.2.2 rfl, hu.2.2.2.2⟩
  have hFresh : ∀ pair ∈ F, pair.1 ≠ site.lowReg ∧ pair.1 ≠ site.highReg := by
    intro pair hm
    have ha : (F.map Prod.fst).all (fun r => decide (r ≠ 2019 ∧ r ≠ 2020)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp ha _ (List.mem_map_of_mem hm))
  have hDemand : PrefixDemand X thread nextIndex 1072 stop := .inr ⟨j, e, huBefore, hLate, he⟩
  have hSave : X.Writes (thread, write) (site.cell thread (l.localBase + 32))
      (b64 ptr).toBytes := hSaved
  obtain ⟨v, hv, hvF, hvRun, hLow, hHigh⟩ :=
    site.observedInPrefix hX (index := nextIndex) (bound := 1072)
    (by decide)
    hCode hAddr hAlign (by decide) hFit (by unfold nextIndex; omega)
    hInput hFresh (by decide) huRun hDemand hSave hLast'
  have strictlyAfter {n : Nat} {read : Event} (hGet : X.get (thread, n) = some read)
      (hRead : read.pc = 1072) : n ≠ j := by
    intro hEq
    subst j
    have same := Option.some.inj (hGet.symm.trans he)
    rw [← same, hRead] at hLate
    omega
  have h1 := strictlyAfter hLow rfl
  have h2 := strictlyAfter hHigh rfl
  have hvRank := (countShuffleTakeOfNonshuffle hHigh rfl).trans
    ((countShuffleTakeOfNonshuffle hLow rfl).trans huRank)
  rw [firstRank, firstCount, restCount, Nat.add_assoc] at hvRank
  exact ⟨nextIndex, by omega, hvRank, v, stop,
    hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.1, hvF⟩, hvRun⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
