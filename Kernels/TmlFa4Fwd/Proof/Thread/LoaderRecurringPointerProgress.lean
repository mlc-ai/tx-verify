-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderScratchReadProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStoreProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStackHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchSave
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchSave
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchWords
import all Kernels.TmlFa4Fwd.Proof.LoaderPointerStore
import all Kernels.TmlFa4Fwd.Proof.LoaderScratchRows
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringSaveAddress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open Correction (OpeningTripCursor)
open Thread.Loader.LocalAccessCode (DoesNotClobber)

private def carryPointerLocal {l : Launch} {X : Execution} {g start stop : Nat}
    {F G : List (Nat × Value)} (cur : OpeningTripCursor l X g start F) {t : TState}
    (ht : Relation.ReflTransGen (Tau kernel Assumptions.all l g) cur.ready t)
    (hAt : At t stop G) : OpeningTripCursor l X g stop G :=
  ⟨cur.pos,cur.before,t,cur.ending,cur.positive,cur.bounded,cur.released,
    hAt,cur.recorded,cur.remaining,cur.localSteps.trans ht⟩

private theorem recurringWordReadOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g value : Nat} (hg : g < l.threads) (hValue : value < 2^31)
    (site : Fin 4) (isRow : Bool) (slot : Fin 2) {F : List (Nat × Value)} :
    let op := recurringScratchWord site isRow
    let a := scratchReloadAccess l g op slot
    (cur : OpeningTripCursor l X g op.pc ((op.base,b64 a.loc.addr) :: F)) →
    (∀ pair ∈ F, pair.1 ≠ op.destination) →
    PrimingCellValue X g cur.pos op.store a (b32 value).toBytes →
    ∃ done : OpeningTripCursor l X g (op.pc+1) ((op.destination,b64 value) :: F),
      done.pos = cur.pos+1 ∧ done.ending = cur.ending ∧
      X.get (g,cur.pos) = some ⟨op.pc,.rd a ((b32 value).toBytes.map some)⟩ := by
  dsimp only
  intro cur hFresh hValueAt
  let op := recurringScratchWord site isRow
  let a := scratchReloadAccess l g op slot
  have hRange : 174 ≤ op.pc ∧ op.pc < 1906 := by fin_cases site <;> cases isRow <;> decide
  have hArray : ¬ op.array.val < 2 := by fin_cases site <;> cases isRow <;> decide
  have hAt : At cur.ready op.pc [(op.base,b64 a.loc.addr)] :=
    cur.checkpoint.mono ⟨cur.checkpoint.2.2.2.2.1,trivial⟩
  have hn : Next kernel Assumptions.all l g cur.before cur.ready
      (.read a (afterAccessLoad cur.ready (.sign 64) 32 [op.destination])) :=
    ⟨cur.localSteps,scratchReloadTemplate hp op (recurringScratchWordCode site isRow)
      hRange hArray slot hAt⟩
  obtain ⟨he,hPast,hTail⟩ := scratchCellReadOfMaximal hMax hg
    (cell := a) rfl rfl (by simp [a,scratchReloadAccess,b32,Value.toBytes,Value.bytes])
    hValueAt hn cur.recorded cur.remaining cur.bounded cur.released
  rw [scratchReloadReturn hValue op hAt] at hPast hTail
  rw [hAt.1] at he
  refine ⟨⟨cur.pos+1,_,_,cur.ending,Nat.succ_pos _,len_of_get he,?_,
    (cur.checkpoint.mono cur.checkpoint.2.2.2.2.2).set hFresh,hPast,hTail,.refl⟩,rfl,rfl,he⟩
  exact releasedIfLast he (by intro h; cases h)

private theorem recurringPointerWriteOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g page row ps rs base : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (site : Fin 4) (slot : Fin 2)
    (hPage : page < 2^64) (hRow : row < 2^64) (hPS : ps < 2^64) (hRS : rs < 2^64)
    (hFit : sourceScratchPayload page row ps rs base < 2^64) {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop (recurringSaveAddressPc site)).take 6).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (cur : OpeningTripCursor l X g (recurringSaveAddressPc site)
      (recurringSaveAddressFacts l site slot page row ps rs base ++ F)) :
    ∃ done : OpeningTripCursor l X g (pointerSavePc site+1) F,
      done.pos = cur.pos+1 ∧ done.ending = cur.ending ∧
      X.get (g,cur.pos) = some ⟨pointerSavePc site,.wr (pointerSaveAccess l g site slot)
        (b64 (sourceScratchPayload page row ps rs base)).toBytes⟩ := by
  let payload := sourceScratchPayload page row ps rs base
  have hs := cur.checkpoint
  obtain ⟨hCore,hF⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨t,ht,hT⟩ := recurringAddressCore (g := g) site slot hp.localMemory.2.1 hPage hRow hPS hRS
    hFit cur.ready (hs.mono hCore)
  have hLo : 174 ≤ recurringSaveAddressPc site := by fin_cases site <;> decide
  have hHi : recurringSaveAddressPc site+6 ≤ 1906 := by fin_cases site <;> decide
  have hSeq : ((kernel.code.drop (recurringSaveAddressPc site)).take 5).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hRun,hFrame⟩ := loaderLinear (regs := F.map Prod.fst) hLo hHi hs.1 hKeep hSeq ht
  have hn : Next kernel Assumptions.all l g cur.before t
      (.write (pointerSaveAccess l g site slot) (b64 payload).toBytes (next t)) :=
    ⟨cur.localSteps.trans (run_rtg hRun),pointerSaveTemplate hp site slot hT⟩
  obtain ⟨he,hPast,hTail⟩ := plainLoaderStoreOfMaximal hp hMax hg hw rfl hn
    cur.recorded cur.remaining cur.positive cur.bounded cur.released
  rw [hT.1] at he
  have hFrame' := holdsSchedulerFrame hF hFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨⟨cur.pos+1,_,_,cur.ending,Nat.succ_pos _,len_of_get he,
    releasedIfLast he (by intro h; cases h),(hT.mono hFrame').next,hPast,hTail,.refl⟩,rfl,rfl,he⟩

/-- A reached warm or steady lane reads both refreshed words and saves the computed pointer. -/
theorem recurringPointerSaveOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g page row ps rs base : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (site : Fin 4) (entry : Fin 2)
    (hPage : page < 2^31) (hRow : row < 2^31) (hPS : ps < 2^64) (hRS : rs < 2^64)
    (hFit : sourceScratchPayload page row ps rs base < 2^64)
    {F : List (Nat × Value)} (hKeep : RecurringSaveFrame site F)
    (cur : OpeningTripCursor l X g ((recurringScratchWord site false).pc-2)
      (recurringScratchSaveInput l site entry ps rs base ++ F))
    (hPageAt : PrimingCellValue X g cur.pos (recurringScratchWord site false).store
      (scratchReloadAccess l g (recurringScratchWord site false) entry) (b32 page).toBytes)
    (hRowAt : PrimingCellValue X g cur.pos (recurringScratchWord site true).store
      (scratchReloadAccess l g (recurringScratchWord site true) entry) (b32 row).toBytes) :
    ∃ done : OpeningTripCursor l X g (pointerSavePc site+1) F,
      done.pos = cur.pos+3 ∧ done.ending = cur.ending ∧
      X.get (g,cur.pos) = some ⟨(recurringScratchWord site false).pc,
        .rd (scratchReloadAccess l g (recurringScratchWord site false) entry)
          ((b32 page).toBytes.map some)⟩ ∧
      X.get (g,cur.pos+1) = some ⟨(recurringScratchWord site true).pc,
        .rd (scratchReloadAccess l g (recurringScratchWord site true) entry)
          ((b32 row).toBytes.map some)⟩ ∧
      X.get (g,cur.pos+2) = some ⟨pointerSavePc site,.wr (pointerSaveAccess l g site entry)
        (b64 (sourceScratchPayload page row ps rs base)).toBytes⟩ := by
  let pOp := recurringScratchWord site false
  let rOp := recurringScratchWord site true
  let pAcc := scratchReloadAccess l g pOp entry
  let rAcc := scratchReloadAccess l g rOp entry
  let carry := recurringScratchCarry l site entry ps rs base
  have hs := cur.checkpoint
  obtain ⟨hCore,hsF⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨t,hPageCode,ht⟩ := recurringScratchPageAddressCore hp (g := g) site entry cur.ready
    (hs.mono hCore)
  have hPLo : 174 ≤ pOp.pc-2 := by fin_cases site <;> decide
  have hPHi : pOp.pc-2+2 ≤ 1906 := by fin_cases site <;> decide
  have hPSeq : ((kernel.code.drop (pOp.pc-2)).take 1).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hT,hTF⟩ := loaderLinear (regs := F.map Prod.fst) hPLo hPHi hs.1 hKeep.page
    hPSeq hPageCode
  have htF := holdsSchedulerFrame hsF hTF (fun _ hm => List.mem_map_of_mem hm)
  have hPAddr : pAcc.loc.addr = l.localBase+96+4*entry.val := by
    fin_cases site <;> simp [pAcc,pOp,recurringScratchWord,scratchReloadAccess,kvLocalOffset,
      Nat.add_assoc]
  let pMore := [(scratchOffsetReg site,b64 (4*entry.val)),(7294,b64 (l.localBase+64))]
    ++ carry ++ F
  have hPT : At t pOp.pc ((pOp.base,b64 pAcc.loc.addr) :: pMore) := by
    rw [hPAddr]
    exact ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,
      (holds_append ..).mpr ⟨ht.2.2.2.2.2.2.2,htF⟩⟩
  have hPFresh : ∀ pair ∈ pMore, pair.1 ≠ pOp.destination := by
    intro pair hMem
    rcases List.mem_append.mp hMem with hMem | hMem
    · fin_cases site <;>
        simp [carry,pOp,recurringScratchWord,scratchOffsetReg,recurringScratchCarry,
          recurringSaveInputs,pointerReloadBase] at hMem ⊢ <;>
        rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact hKeep.pageFresh pair hMem
  let pStart := carryPointerLocal cur (run_rtg hT) hPT
  obtain ⟨pDone,hPPos,hPEnd,heP⟩ := recurringWordReadOfMaximal hp hMax hg hPage site false entry
    pStart hPFresh hPageAt
  change pDone.pos = cur.pos+1 at hPPos
  change pDone.ending = cur.ending at hPEnd
  change X.get (g,cur.pos) = some ⟨pOp.pc,.rd pAcc ((b32 page).toBytes.map some)⟩ at heP
  have hRAt : PrimingCellValue X g pDone.pos rOp.store rAcc (b32 row).toBytes := by
    rw [hPPos]
    exact hRowAt.step hMax.1 heP (by intro _ _ h; cases h)
  have hU := pDone.checkpoint
  have hRowInput : At pDone.ready (pOp.pc+1)
      (recurringScratchRowInput l site entry page ps rs base) :=
    hU.mono ⟨hU.2.2.2.2.2.1,hU.2.2.2.2.2.2.1,hU.2.2.2.2.1,
      ((holds_append ..).mp hU.2.2.2.2.2.2.2).1⟩
  have huF := ((holds_append ..).mp hU.2.2.2.2.2.2.2).2
  obtain ⟨v,hRowCode,hv⟩ := recurringScratchRowAddressCore hp (g := g) site entry
    pDone.ready hRowInput
  have hRLo : 174 ≤ pOp.pc+1 := by fin_cases site <;> decide
  have hRHi : pOp.pc+1+1 ≤ 1906 := by fin_cases site <;> decide
  obtain ⟨hV,hVF⟩ := loaderLinear (regs := F.map Prod.fst) hRLo hRHi hRowInput.1
    hKeep.row rfl hRowCode
  have hvF := holdsSchedulerFrame huF hVF (fun _ hm => List.mem_map_of_mem hm)
  have hRAddr : rAcc.loc.addr = l.localBase+64+4*entry.val := by
    fin_cases site <;> simp [rAcc,rOp,recurringScratchWord,scratchReloadAccess,kvLocalOffset,
      Nat.add_assoc]
  let rMore := (pOp.destination,b64 page) :: (carry ++ F)
  have hRT : At v rOp.pc ((rOp.base,b64 rAcc.loc.addr) :: rMore) := by
    rw [hRAddr]
    exact hv.mono ⟨hv.2.2.2.2.1,hv.2.2.2.2.2.1,
      (holds_append ..).mpr ⟨hv.2.2.2.2.2.2,hvF⟩⟩
  have hRFresh : ∀ pair ∈ rMore, pair.1 ≠ rOp.destination := by
    intro pair hMem
    rcases List.mem_append.mp (show pair ∈ ((pOp.destination,b64 page) :: carry) ++ F
      from hMem) with hMem | hMem
    · fin_cases site <;>
        simp [pOp,rOp,carry,recurringScratchWord,recurringScratchCarry,
          recurringSaveInputs,pointerReloadBase] at hMem ⊢ <;>
        rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact hKeep.rowFresh pair hMem
  let rStart := carryPointerLocal pDone (run_rtg hV) hRT
  obtain ⟨rDone,hRPos,hREnd,heR⟩ := recurringWordReadOfMaximal hp hMax hg hRow site true entry
    rStart hRFresh hRAt
  change rDone.pos = pDone.pos+1 at hRPos
  change rDone.ending = pDone.ending at hREnd
  change X.get (g,pDone.pos) = some ⟨rOp.pc,.rd rAcc ((b32 row).toBytes.map some)⟩ at heR
  have hPc : rOp.pc+1 = recurringSaveAddressPc site := by fin_cases site <;> decide
  have hIds : rOp.destination = (recurringSaveInputs site).row ∧
      pOp.destination = (recurringSaveInputs site).page := by fin_cases site <;> decide
  have hSaveAt : At rDone.ready (recurringSaveAddressPc site)
      (recurringSaveAddressFacts l site entry page row ps rs base ++ F) := by
    rw [← hPc]
    exact rDone.checkpoint.mono ⟨hIds.2 ▸ rDone.checkpoint.2.2.2.2.2.1,
      hIds.1 ▸ rDone.checkpoint.2.2.2.2.1,rDone.checkpoint.2.2.2.2.2.2⟩
  let sStart := carryPointerLocal rDone .refl hSaveAt
  obtain ⟨done,hDonePos,hDoneEnd,heSave⟩ := recurringPointerWriteOfMaximal hp hMax hg hw site entry
    (by omega) (by omega) hPS hRS hFit hKeep.save sStart
  change done.pos = rDone.pos+1 at hDonePos
  change done.ending = rDone.ending at hDoneEnd
  change X.get (g,rDone.pos) = _ at heSave
  rw [hRPos,hPPos] at heSave
  rw [hPPos] at heR
  exact ⟨done,by omega,hDoneEnd.trans (hREnd.trans hPEnd),heP,heR,
    by simpa only [Nat.add_assoc] using heSave⟩

private theorem wordReadSuffix {X : Execution} {g n : Nat} {e : Event}
    (he : X.get (g,n) = some e) : (X.tr g).drop n = e :: (X.tr g).drop (n+1) := by
  have h := List.getElem?_eq_some_iff.mp he
  rw [List.drop_eq_getElem_cons h.1,h.2]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g ps rs base shuffles votes : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (site : Fin 4) (slot : Fin 2)
    (page row : Nat → Nat) (hPage : ∀ lane < 32, page lane < 2^31)
    (hRow : ∀ lane < 32, row lane < 2^31) (hPS : ps < 2^64) (hRS : rs < 2^64)
    (hFit : ∀ lane < 32, sourceScratchPayload (page lane) (row lane) ps rs base < 2^64)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hKeep : ∀ lane < 32, RecurringSaveFrame site (F lane))
    (cur : SchedulerWarpReached l X g ((recurringScratchWord site false).pc-2)
      (fun lane => recurringScratchSaveInput l site slot ps rs base ++ F lane)
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ isRow,
      let t := warpLane l g lane
      let op := recurringScratchWord site isRow
      PrimingCellValue X t (cur.pos lane) op.store (scratchReloadAccess l t op slot)
        (b32 (if isRow then row lane else page lane)).toBytes)
include hp hMax hg hw site slot page row hPage hRow hPS hRS hFit hKeep cur hCells

/-- Each lane prepares the matching K or V pointer while preserving the warp's collective counts. -/
theorem recurringPointerSaveWarpPreservingOfMaximal :
    ∃ done : SchedulerWarpReached l X g (pointerSavePc site+1) F shuffles votes ends,
      done.pos = (fun lane => cur.pos lane+3) ∧
      ∀ lane < 32,
        (let t := warpLane l g lane
         let dst := pointerSaveAccess l t site slot
         let bs := (b64 (sourceScratchPayload (page lane) (row lane) ps rs base)).toBytes
         PrimingCellValue X t (done.pos lane) (pointerSavePc site) dst bs ∧
         ∀ {saved : Nat} {cell : Acc} {data : List Byte},
           PrimingCellValue X t (cur.pos lane) saved cell data →
           DoesNotClobber cell ⟨pointerSavePc site,.wr dst bs⟩ →
           PrimingCellValue X t (done.pos lane) saved cell data) := by
  classical
  let t := warpLane l g
  let stop := fun lane => cur.pos lane+3
  let data := fun lane => (b64 (sourceScratchPayload (page lane) (row lane) ps rs base)).toBytes
  let read := fun lane flag =>
    let op := recurringScratchWord site flag
    let value := if flag then row lane else page lane
    (⟨op.pc,.rd (scratchReloadAccess l (t lane) op slot) ((b32 value).toBytes.map some)⟩ : Event)
  let es : Nat → List Event := fun lane =>
    [read lane false,read lane true,
      ⟨pointerSavePc site,.wr (pointerSaveAccess l (t lane) site slot) (data lane)⟩]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : ∃ before u,
      (X.tr (t lane)).drop (cur.pos lane) = es lane ++ (X.tr (t lane)).drop (stop lane) ∧
      At u (pointerSavePc site+1) (F lane) ∧
      Run kernel Assumptions.all l (t lane) {} ((X.tr (t lane)).take (stop lane)) (some before) ∧
      Run kernel Assumptions.all l (t lane) before ((X.tr (t lane)).drop (stop lane)) (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (t lane)) before u ∧
      stop lane ≤ (X.tr (t lane)).length ∧
      (stop lane = (X.tr (t lane)).length → Step.Released l X (t lane)) ∧
      PrimingCellValue X (t lane) (stop lane) (pointerSavePc site)
        (pointerSaveAccess l (t lane) site slot) (data lane) ∧
      ∀ {saved : Nat} {cell : Acc} {data₀ : List Byte},
        PrimingCellValue X (t lane) (cur.pos lane) saved cell data₀ →
        DoesNotClobber cell
          ⟨pointerSavePc site,.wr (pointerSaveAccess l (t lane) site slot) (data lane)⟩ →
        PrimingCellValue X (t lane) (stop lane) saved cell data₀ := by
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    let c : OpeningTripCursor l X (t lane)
        ((recurringScratchWord site false).pc-2)
        (recurringScratchSaveInput l site slot ps rs base ++ F lane) :=
      ⟨cur.pos lane,cur.before lane,cur.state lane,ends lane,cur.positive lane hl,
        cur.bounded lane hl,
        cur.released lane hl,cur.checkpoint lane hl,cur.recorded lane hl,cur.continuation lane hl,
        cur.localSteps lane hl⟩
    have hWarp : warpIndex l g = warpIndex l (t lane) := hSame.2
    have hThis : 14 ≤ warpIndex l (t lane) := hWarp ▸ hw
    obtain ⟨done,hPos,hEnd,heP,heR,heW⟩ := recurringPointerSaveOfMaximal hp hMax
      hSame.1.2.1 hThis site slot (hPage lane hl) (hRow lane hl) hPS hRS (hFit lane hl)
      (hKeep lane hl) c (hCells lane hl false) (hCells lane hl true)
    change done.pos = stop lane at hPos
    change done.ending = ends lane at hEnd
    have hPast := done.recorded
    have hTail := done.remaining
    simp only [hPos,hEnd] at hPast hTail
    refine ⟨done.before,done.ready,?_,done.checkpoint,hPast,hTail,done.localSteps,
      hPos ▸ done.bounded,hPos ▸ done.released,?_⟩
    · change X.get (t lane,cur.pos lane) = some (read lane false) at heP
      change X.get (t lane,cur.pos lane+1) = some (read lane true) at heR
      change X.get (t lane,cur.pos lane+2) = some _ at heW
      rw [wordReadSuffix heP,wordReadSuffix heR,show cur.pos lane+1+1 = cur.pos lane+2 by omega,
        wordReadSuffix heW]
      rfl
    · refine ⟨primingCellValue_write heW,?_⟩
      intro saved cell data₀ hCell hDisj
      have h₀ := hCell.step hMax.1 heP (by intro _ _ h; cases h)
      have h₁ := h₀.step hMax.1 heR (by intro _ _ h; cases h)
      rw [show cur.pos lane+1+1 = cur.pos lane+2 by omega] at h₁
      exact h₁.step hMax.1 heW hDisj
  let _ : Inhabited TState := ⟨{}⟩
  choose! before u hTrace hAt hPast hTail hLocal hBound hRelease hSaved using hLane
  have hOrd := cur.ordinals.advance es (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨⟨stop,before,u,hOrd,hTail,hLocal,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,rfl,hSaved⟩

end PTX.Kernels.TmlFa4Fwd.Loader
