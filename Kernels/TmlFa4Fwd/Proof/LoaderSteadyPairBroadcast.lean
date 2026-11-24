-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPairSites
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPeerFloor
import Kernels.TmlFa4Fwd.Proof.LoaderWarmShuffleFloor
import Kernels.TmlFa4Fwd.Proof.LoaderSteadyWideColumn
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFirstPrefix
import Kernels.TmlFa4Fwd.Proof.TerminalSite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- The selected subgroup lane contributes the row of the addressed pointer slot. -/
def steadyPairRow (tile tid : Nat) (pair : Fin 16) : Nat :=
  primingLaneRow tile tid + 64 * (steadyPairSlot pair).val

private def steadyPairWords (value : Bool) (pair : Fin 16) (base tid : Nat) :
    List (Nat × Value) :=
  [(steadyPairShuffleIn value pair, b32 (base % 2 ^ 32)),
    (steadyPairShuffleIn value pair + 1, b32 (base / 2 ^ 32)), steadyPairColumn value pair tid]

private def steadyPairInputPc (value : Bool) (pair : Fin 16) : Nat :=
  if value = true ∧ 0 < pair.val ∧ pair.val < 8 then 1637 else
    (steadyPointerReload value (steadyPairSlot pair)).pc + 1

private def steadyPairInputRank (value : Bool) (pair : Fin 16) : Nat :=
  16 * (steadyPairSlot pair).val +
    if value = true ∧ 0 < pair.val ∧ pair.val < 8 then 2 else 0

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

set_option maxRecDepth 100000 in
private theorem steadyPairInputOfSpills (hX : Consistent l kernel Assumptions.all m X)
    {g index j batch head row trips warp tid : Nat} (hb : batch < p.batch) (hh : head < p.kvHeads)
    (value : Bool) (pair : Fin 16) {s : TState} {ending : Option TState}
    (hs : At s (steadySpillExit value) (steadyCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hSaved : ∃ write < index,
      X.Writes (g, write) (pointerSaveAccess l g (steadySpillSite value) (steadyPairSlot pair))
        (b64 (steadyOperandPointer p value batch head row)).toBytes ∧
      ∀ byte < 8, ∀ k < index, ∀ a, X.Access (g, k) a true →
        a.Covers ((pointerSaveAccess l g (steadySpillSite value)
          (steadyPairSlot pair)).loc.at byte) → k ≤ write) {e : Event} (he : X.get (g, j) = some e)
    (hBefore : index ≤ j) (hLate : (steadyPointerReload value (steadyPairSlot pair)).pc < e.pc)
    (hLater : steadyPairShufflePc value pair < e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr g).take j).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 2 * pair.val + 1))
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    let ptr := steadyOperandPointer p value batch head row
    ∃ pos ≤ j, ∃ t finish,
      At t (steadyPairInputPc value pair) (steadyPairWords value pair ptr tid) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) finish ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + steadyPairInputRank value pair := by
  let slot := steadyPairSlot pair
  let load := steadyPointerReload value slot
  let wide := value && decide (8 ≤ pair.val)
  let ptr := steadyOperandPointer p value batch head row
  let F := steadyCacheFrame p l batch head trips warp tid
  let G := [(load.lowReg, b32 (ptr % 2 ^ 32)), (load.highReg, b32 (ptr / 2 ^ 32))] ++
    (steadyReloadColumn wide tid ++ F)
  have hWide : wide = true → value = true ∧ slot = 1 := by
    intro h
    obtain ⟨hValue, hHalf⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨hValue, ite_eq_right (Nat.not_lt_of_ge (of_decide_eq_true hHalf))⟩
  obtain ⟨pos, hPos, t, stop, ht, htRun, htRank⟩ :=
    steadyOperandReloadFromSpillsWithColumn hp hX hb hh value slot wide hWide hs hr
      hSaved he hBefore hLate hSafe
  have ht' : At t (load.pc + 1) G := ht
  have hFrames : Holds t.regs (steadyReloadColumn wide tid) ∧ Holds t.regs F :=
    (holds_append t.regs (steadyReloadColumn wide tid) F).mp ht.2.2.2.2.2.2
  have hHigh : load.highReg = steadyPairShuffleIn value pair + 1 := by
    cases value <;> fin_cases pair <;> rfl
  by_cases hPrepare : value = true ∧ 0 < pair.val ∧ pair.val < 8
  · obtain ⟨rfl, hNW, hHalf⟩ := hPrepare
    have hSlot : slot = 0 := ite_eq_left hHalf
    have hNoWide : wide = false := by simp [wide, Nat.not_le_of_gt hHalf]
    let H := [(2198, b32 (ptr % 2 ^ 32)), (2199, b32 (ptr / 2 ^ 32))] ++ F
    have htAt : At t 1633 H := by
      change At t ((steadyPointerReload true 0).pc + 1)
        ([((steadyPointerReload true 0).lowReg, b32 (ptr % 2 ^ 32)),
          ((steadyPointerReload true 0).highReg, b32 (ptr / 2 ^ 32))] ++ F)
      simpa only [G, hSlot, load, hNoWide, steadyReloadColumn, Bool.false_eq_true,
        ↓reduceIte, List.nil_append] using ht'
    have hCount : loaderShuffleTail 1636 1633 = 2 := by kernel_rfl
    have hAdvance : 1636 ≤ e.pc ∨ (Execution.isShfl e = true ∧
        ((X.tr g).take (pos + 2)).countP Execution.isShfl + loaderShuffleTail 1636 1633 ≤
          ((X.tr g).take j).countP Execution.isShfl) := by
      rcases hLater with h | ⟨hShfl, hOrdinal⟩
      · have hFloor : 1636 ≤ steadyPairShufflePc true pair := by
          fin_cases pair <;> first | contradiction | decide
        exact .inl (hFloor.trans h.le)
      · refine .inr ⟨hShfl, ?_⟩
        rw [htRank, hOrdinal, hCount, hSlot]
        have hZero : (0 : Fin 2).val = 0 := rfl
        rw [hZero]
        omega
    obtain ⟨k, _, hK, u, finish, hu, huRun, huRank⟩ :=
      steadyValueWideColumnOfEvent (tid := tid) (by decide)
        (fun _ => by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
        (by simp [H, F, steadyCacheFrame]) htAt htRun he hPos hAdvance hSafe
    refine ⟨k, hK, u, finish, ?_, huRun, ?_⟩
    · simp only [steadyPairInputPc, true_and, hNW, hHalf, ↓reduceIte]
      have hInput : steadyPairShuffleIn true pair = 2198 := by
        unfold steadyPairShuffleIn steadyPairSlot
        rw [ite_eq_left hHalf]
        rfl
      have hCol : steadyPairColumn true pair tid = (7825, b64 (16 * (tid % 8))) := by
        simp [steadyPairColumn, Nat.ne_of_gt hNW]
      exact hu.mono (by
        rw [steadyPairWords, hInput, hCol]
        exact ⟨hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1, hu.2.2.2.2.1, trivial⟩)
    · rw [huRank, htRank, hCount, steadyPairInputRank, ite_eq_left ⟨rfl, hNW, hHalf⟩, Nat.add_assoc]
  · have hCol : t.regs (steadyPairColumn value pair tid).1 =
        some (steadyPairColumn value pair tid).2 := by
      cases value
      · change t.regs 7781 = some (b64 (16 * (tid % 8)))
        exact holds_lookup hFrames.2 rfl
      · by_cases hZero : pair.val = 0
        · obtain rfl : pair = 0 := Fin.ext hZero
          change t.regs 1147 = some (b32 (8 * (tid % 8)))
          exact holds_lookup hFrames.2 rfl
        · have hHalf : 8 ≤ pair.val := by
            by_contra! hLow
            exact hPrepare ⟨rfl, by omega, hLow⟩
          have hTrue : wide = true := by simp [wide, hHalf]
          have hWord := hFrames.1
          rw [hTrue] at hWord
          have hColumn : steadyPairColumn true pair tid = (7825, b64 (16 * (tid % 8))) := by
            simp [steadyPairColumn, hZero]
          rw [hColumn]
          exact hWord.1
    refine ⟨pos + 2, hPos, t, stop, ?_, htRun, ?_⟩
    · rw [steadyPairInputPc, ite_eq_right hPrepare]
      exact ht.mono (by
        rw [steadyPairWords, ← hHigh]
        exact ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, hCol, trivial⟩)
    · rw [htRank, steadyPairInputRank, ite_eq_right hPrepare, Nat.add_zero]

set_option maxRecDepth 100000 in
private theorem steadyPairObservedLane (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g lane batch iteration j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : lane < 32) (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1)
    (hMin : 9 ≤ iteration) (value : Bool) (pair : Fin 16) {e : Event}
    (he : X.get (warpLane l g lane, j) = some e)
    (hLate : (steadyPointerReload value (steadyPairSlot pair)).pc < e.pc)
    (hRound : SteadyRoundDemand p l X g lane batch iteration j e)
    (hLater : steadyPairShufflePc value pair < e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) +
          steadyOperandRank value + 2 * pair.val + 1)) (hSafe : ∀ f, e.kind ≠ .ub f) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let row := steadyPairRow (Mma.trips p batch co.1 - 2 - iteration) tid pair
    let ptr := steadyOperandPointer p value batch (co.2 / 6) row
    ∃ pos ≤ j, ∃ ending, Nonempty (PointerBroadcastInPrefix l X thread pos
      (primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) +
        steadyOperandRank value + 2 * pair.val)
      (steadyPairShufflePc value pair) ptr (steadyPairShuffleOut value pair) (pair.val % 8)
      (steadyPairWords value pair ptr tid) ending) := by
  let slot := steadyPairSlot pair
  let load := steadyPointerReload value slot
  have hStorePc : pointerSavePc (steadySpillSite value) ≤ load.pc := by
    cases value <;> fin_cases pair <;> decide
  obtain ⟨index, hBefore, s, ending, hs, hr, hsRank, hSaves⟩ :=
    steadyOperandSpillsOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi hMany hMin value
      he (hStorePc.trans_lt hLate) hSafe hRound
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let row := steadyPairRow (Mma.trips p batch co.1 - 2 - iteration) tid pair
  let ptr := steadyOperandPointer p value batch (co.2 / 6) row
  let F := steadyPairWords value pair ptr tid
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by dsimp [co]; unfold Params.heads at hHead; omega
  have hNewLater : steadyPairShufflePc value pair < e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr thread).take j).countP Execution.isShfl =
        ((X.tr thread).take index).countP Execution.isShfl + 2 * pair.val + 1) :=
    hLater.imp_right (fun h => ⟨h.1, by rw [hsRank]; exact h.2⟩)
  obtain ⟨pos, hPos, t, stop, htAt, htRun, htRank⟩ :=
    steadyPairInputOfSpills hp hX (row := row) hb hh value pair hs hr
      (hSaves slot) he hBefore hLate hNewLater hSafe
  let start := steadyPairInputPc value pair
  let cut := steadyPairShufflePc value pair
  have hScope : 174 ≤ start ∧ start ≤ cut ∧ cut ≤ 1901 := by
    cases value <;> fin_cases pair <;> decide
  have hAudit (n : Nat) : ((kernel.code.drop start).take (cut - start)).all
      (fun ins => loaderPipelineCutOp start cut n (F.map Prod.fst) ins.op) = true := by
    cases value <;> fin_cases pair <;> kernel_rfl
  have hRanked : (((kernel.code.drop start).take (cut - start)).zipIdx start).all
      (fun (ins, pc) => LoaderRankedInstr cut pc ins) = true := by
    cases value <;> fin_cases pair <;> kernel_rfl
  have hCount : steadyPairInputRank value pair + loaderShuffleTail cut start = 2 * pair.val := by
    cases value <;> fin_cases pair <;> kernel_rfl
  let rank := primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) +
    steadyOperandRank value + 2 * pair.val
  have hBudget : cut ≤ e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr thread).take pos).countP Execution.isShfl + loaderShuffleTail cut start ≤
        ((X.tr thread).take j).countP Execution.isShfl) := by
    rcases hLater with h | ⟨hShfl, hSeen⟩
    · exact .inl h.le
    · refine .inr ⟨hShfl, ?_⟩
      rw [htRank, hsRank, hSeen]
      change _ + steadyOperandRank value + steadyPairInputRank value pair + _ ≤ _
      omega
  obtain ⟨u, front, finish, _, hu, huRun, huRank, huBefore⟩ :=
    prefixRankedShuffleCut hScope hAudit hRanked htAt htRun he hPos hBudget hSafe
  have hNth : ((X.tr thread).take (pos + front.length)).countP Execution.isShfl = rank := by
    rw [huRank, htRank, hsRank]
    unfold rank
    change _ + steadyOperandRank value + steadyPairInputRank value pair + _ = _
    omega
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hRange : 174 ≤ cut ∧ cut + 1 < 1906 := by cases value <;> fin_cases pair <;> decide
  have hFresh : ∀ r ∈ F, r.1 ≠ steadyPairShuffleOut value pair ∧
      r.1 ≠ steadyPairShuffleOut value pair + 1 := by
    intro r hm
    have hCodes : (F.map Prod.fst).all (fun k => decide
        (k ≠ steadyPairShuffleOut value pair ∧ k ≠ steadyPairShuffleOut value pair + 1)) =
        true := by cases value <;> fin_cases pair <;> kernel_rfl
    exact of_decide_eq_true (List.all_eq_true.mp hCodes _ (List.mem_map_of_mem hm))
  refine ⟨pos + front.length, huBefore, finish, ?_⟩
  refine pointerBroadcastObserved (F := F) (base := ptr) (src := steadyPairShuffleIn value pair)
    hBlock hRange (Nat.mod_lt _ (by decide)) (steadyPairShuffleCode value pair 0)
    (steadyPairShuffleCode value pair 1) hFresh hu
    (by simp [F, steadyPairWords]) (by simp [F, steadyPairWords]) huRun hNth
    (traceAfterObservedEvent he huBefore) ?_
  intro low hGet hLow _
  apply traceAfterObservedEvent he
  by_contra! hNo
  have hEq : pos + front.length = j := by omega
  rw [hEq] at hGet
  have same := Option.some.inj (hGet.symm.trans he)
  rcases hLater with h | ⟨_, h⟩
  · rw [← same, hLow] at h
    exact Nat.lt_irrefl _ h
  · rw [← hEq, hNth] at h
    unfold rank at h
    omega

set_option maxRecDepth 100000 in
/-- An observed steady K or V pair receives its true subgroup pointer. -/
theorem steadyPairBroadcastOfEvent (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g src j batch iteration : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1)
    (hMin : 9 ≤ iteration) (value : Bool) (pair : Fin 16) (upper : Bool) {sp : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) =
      some ⟨packetPlanePc (recurringPacketSite (steadySpillSite value)) pair upper, .copy sp⟩)
    (hRequest : ((X.tr (warpLane l g src)).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) +
        steadyOperandRank value + 2 * pair.val + 2) :
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      let sender := warpLane l g (steadyPairSender src pair)
      let tid := thread % l.block
      let row := steadyPairRow (Mma.trips p batch co.1 - 2 - iteration) (sender % l.block) pair
      let ptr := steadyOperandPointer p value batch (co.2 / 6) row
      ∃ pos ending s, pos + 2 ≤ j ∧
        At s (steadyPairShufflePc value pair + 2) (steadyPairInputs value pair ptr tid) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop (pos + 2)) ending ∧
        ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
          primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) +
            steadyOperandRank value + 2 * pair.val + 2 := by
  let pc := packetPlanePc (recurringPacketSite (steadySpillSite value)) pair upper
  let shflPc := steadyPairShufflePc value pair
  let e : Event := ⟨pc, .copy sp⟩
  let slot := steadyPairSlot pair
  let load := steadyPointerReload value slot
  have hOrdered : load.pc < pc ∧ shflPc + 1 < pc ∧ pc < 1744 := by
    cases value <;> fin_cases pair <;> cases upper <;> decide
  have hFirst : 1396 ≤ pc := by cases value <;> fin_cases pair <;> cases upper <;> decide
  have hExit : load.pc < 9205 ∧ shflPc < 9205 := by cases value <;> fin_cases pair <;> decide
  have hEvent : X.get (warpLane l g src, j) = some e := he
  have writes (w a data loc) (hw : X.MemWrites w a data) (hc : a.Covers loc)
      (hg : loc.space = .global) : p.oRegion.Contains loc ∨ p.lseRegion.Contains loc := by
    rcases hFrame w a data loc hw hc hg with ho | ⟨q, hq, head, hh, k, hk, rfl⟩
    · exact .inl ho
    · exact .inr (lseByte_in hq hh hk)
  have hSafe : ∀ f, e.kind ≠ .ub f := by intro f h; cases h
  have hRound : SteadyRoundDemand p l X g src batch iteration j e :=
    ⟨.inr hOrdered.2.2, .inr (by rw [hRequest]; omega)⟩
  have hIter := (steadyRoundEntryOfEvent hp hX hg hw hSrc writes hCTA hb hLo hHi
    hMany hMin hEvent hFirst hSafe hRound).1
  have hCan : iteration < Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1 := by
    omega
  obtain ⟨b, hb', hlo, hhi, _, cur, _⟩ :=
    loaderPrimingEntryOfActiveEvent hp hX hg hw hSrc (hp.cuQ_protected writes)
      hCTA hEvent (show 308 < pc by omega)
  obtain ⟨_, _, only⟩ := tileBatch_existsUnique p hCTA
  have hbEq : b = batch := (only b ⟨hb', hlo, hhi⟩).trans (only batch ⟨hb, hLo, hHi⟩).symm
  subst b
  obtain ⟨pos, hPos, ending, ⟨recv⟩⟩ :=
    steadyPairObservedLane hp hX hFrame hg hw hSrc hCTA hb hLo hHi hMany hMin value pair
      hEvent hOrdered.1 hRound (.inl (by change shflPc < pc; omega)) hSafe
  let lane := steadyPairSender src pair
  let thread := warpLane l g
  let rank := primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) +
    steadyOperandRank value + 2 * pair.val
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hl : lane < 32 := by unfold lane steadyPairSender pointerBroadcastLane; omega
  have hWarp := Step.sameWarp_trans
    (sameWarp_symm (Step.sameWarp_lane hBlock hg hSrc).1) (Step.sameWarp_lane hBlock hg hl).1
  have hFirstRank : 16 * slot.val ≤ 2 * pair.val + 1 := by fin_cases pair <;> decide
  have hOperand : steadyOperandRank value ≤ 32 := by cases value <;> decide
  have hPair := pair.isLt
  have hPeer : ∃ k peer, X.get (thread lane, k) = some peer ∧ load.pc < peer.pc ∧
      SteadyRoundDemand p l X g lane batch iteration k peer ∧
      (shflPc < peer.pc ∨ (Execution.isShfl peer = true ∧
        ((X.tr (thread lane)).take k).countP Execution.isShfl = rank + 1)) ∧
      ∀ f, peer.kind ≠ .ub f := by
    rcases Step.shfl_lane_of_ready hX recv.second recv.secondOrdinal hWarp with
      ⟨k, ⟨⟨s, mode, input, select, clamp, result, good, hGet⟩, hCount⟩⟩ |
      ⟨k, s, hEnded, _⟩
    · let peer : Event := ⟨s, .shfl mode input select clamp result good⟩
      have hk : ((X.tr (thread lane)).take k).countP Execution.isShfl = rank + 1 := hCount
      have hBefore : cur.pos lane ≤ k := by
        by_contra! h
        have hLe := Flow.countP_take_mono Execution.isShfl (X.tr (thread lane)) h.le
        rw [hk, cur.ordinals.shfl lane hl] at hLe
        dsimp only [rank] at hLe
        omega
      have hLate := firstKPeerAfterMetadata hp hw hl cur hGet hBefore (.inl rfl)
      have hFloor : 805 ≤ peer.pc :=
        primingVPeerFirstBroadcastFloor hp hX hg hw hl writes hb hLo hHi hCTA hGet hLate rfl
          (by rw [hk]; dsimp only [rank]; omega)
      have hWarmFloor : 1004 ≤ peer.pc :=
        warmShuffleFloor hp hX hg hw hl writes hb hLo hHi hCTA hGet hFloor rfl
          (by rw [hk]; dsimp only [rank]; omega)
      have hSteadyFloor : 1396 ≤ peer.pc :=
        steadyShuffleBodyFloor hp hX hg hw hl writes hCTA hb hLo hHi hMany hGet
          (by omega) rfl (by rw [hk]; dsimp only [rank]; omega)
      have hPeerRound : SteadyRoundDemand p l X g lane batch iteration k peer :=
        ⟨.inl hCan, .inr (by rw [hk]; dsimp only [rank]; omega)⟩
      have hHalf :=
        steadyShuffleSlotFloor hp hX hg hw hl writes hCTA hb hLo hHi hMany hMin value slot
          hGet hSteadyFloor rfl hPeerRound
          (by rw [hk]; dsimp only [rank]; omega)
          (by rw [hk]; dsimp only [rank]; omega)
      exact ⟨k, peer, hGet, hHalf, hPeerRound, .inr ⟨rfl, hk⟩, by intro f h; cases h⟩
    · obtain rfl := actualExitPc hX hEnded
      exact ⟨k, ⟨9205, .exit⟩, hEnded, hExit.1, ⟨.inl hCan, .inl (by decide)⟩,
        .inl hExit.2, by intro f h; cases h⟩
  obtain ⟨k, peer, hPeer, hLate, hPeerRound, hLater, hPeerSafe⟩ := hPeer
  obtain ⟨partner, _, _, ⟨sent⟩⟩ :=
    steadyPairObservedLane hp hX hFrame hg hw hl hCTA hb hLo hHi hMany hMin value pair
      hPeer hLate hPeerRound hLater hPeerSafe
  have hSource : (shflSource .idx src (pair.val % 8) 6175).1 = lane := by
    let s : Fin 8 := ⟨pair.val % 8, Nat.mod_lt _ (by decide)⟩
    exact congrArg Prod.fst (kv_shuffle_source ⟨src, hSrc⟩ s)
  have hLane : laneOf l (thread src) = src := (Step.sameWarp_lane hBlock hg hSrc).2
  have hFrom : thread src - laneOf l (thread src) +
      (shflSource .idx (laneOf l (thread src)) (pair.val % 8) 6175).1 = thread lane := by
    rw [hLane, hSource]
    unfold thread warpLane
    omega
  have hThread : thread lane < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  have hLoWord := (Flow.shfl_source_value hX recv.first recv.firstOrdinal
    (by rw [hFrom]; exact sent.first) (by rw [hFrom]; exact sent.firstOrdinal)
    (by rw [hFrom]; exact ShflK.not_exited hX hThread sent.firstOrdinal)).1
  have hHiWord := (Flow.shfl_source_value hX recv.second recv.secondOrdinal
    (by rw [hFrom]; exact sent.second) (by rw [hFrom]; exact sent.secondOrdinal)
    (by rw [hFrom]; exact ShflK.not_exited hX hThread sent.secondOrdinal)).1
  have hAt := recv.checkpoint
  rw [hLoWord, hHiWord] at hAt
  refine ⟨pos, ending, recv.state, ?_, hAt.mono ?_, recv.continuation, ?_⟩
  · by_contra! hClose
    have impossible {ev : Event} (h : X.get (thread src, j) = some ev) (hb : ev.pc < pc) :
        False := by
      obtain rfl := Option.some.inj (hEvent.symm.trans h)
      exact Nat.lt_irrefl _ hb
    rcases (show pos = j ∨ pos + 1 = j by omega) with hA | hB
    · have hGet := congrArg (fun n => X.get (thread src, n)) hA
      exact impossible (hGet.symm.trans recv.first) (show shflPc < pc by omega)
    · have hGet := congrArg (fun n => X.get (thread src, n)) hB
      exact impossible (hGet.symm.trans recv.second) hOrdered.2.1
  · exact ⟨hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, hAt.2.2.2.2.2.2.2.2⟩
  · have hCount := countP_take_succ (p := Execution.isShfl) recv.second rfl
    rw [show pos + 2 = pos + 1 + 1 by omega, hCount, recv.secondOrdinal.2]

end
end PTX.Kernels.TmlFa4Fwd.Loader
