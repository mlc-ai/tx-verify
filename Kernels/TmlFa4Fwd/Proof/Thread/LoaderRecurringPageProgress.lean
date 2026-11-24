-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageRefresh
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageRead
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageStore
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageRefresh
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStoreProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Flow.MemTmpl
import Lemmas.Flow.CountTake
import Lemmas.Step.DrainInOrder
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Correction (OpeningTripCursor)
open PTX.Kernels.TmlFa4Fwd.Loader

private def livePageWord (p : Params) (site : Fin 2) (batch row : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  ((recurringPageSite site).physicalPage,b32 (p.page batch (row/16)))::F

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

set_option maxRecDepth 4096 in
private theorem recurringPageReadOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch row : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hr : row < p.kLength batch) (site : Fin 2) {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop ((recurringPageReadSite site).pc-2)).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (recurringPageSite site).physicalPage)
    (cur : OpeningTripCursor l X g ((recurringPageReadSite site).pc-2)
      (recurringPageReadInput p site batch row++F)) :
    ∃ out : OpeningTripCursor l X g ((recurringPageReadSite site).pc+1)
        (livePageWord p site batch row F),
      out.pos = cur.pos+1 ∧ out.ending = cur.ending ∧
        X.get (g,cur.pos) = some ⟨(recurringPageReadSite site).pc,
          .rd {loc := globalLoc (pageWordAddress p batch (row/16)),size := 4}
            ((b32 (p.page batch (row/16))).toBytes.map some)⟩ := by
  let s := recurringPageReadSite site
  let addr := pageWordAddress p batch (row/16)
  let word := b32 (p.page batch (row/16))
  let dst := (recurringPageSite site).physicalPage
  let a : Acc := {loc := globalLoc addr,size := 4}
  have ht := cur.checkpoint
  have hFrames := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨v,hv,hV⟩ := recurringPageAddressCore hp (g := g) hb hr site cur.ready
    (ht.mono hFrames.1)
  have hLo : 174 ≤ s.pc-2 := by fin_cases site <;> decide
  have hHi : s.pc-2+2 ≤ 1906 := by fin_cases site <;> decide
  have hRange : 174 ≤ s.pc ∧ s.pc < 1906 := by fin_cases site <;> decide
  have hSeq : ((kernel.code.drop (s.pc-2)).take 1).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hvA,hVF⟩ := loaderLinear hLo hHi ht.1 hKeep hSeq hv
  have hCode : kernel.code[s.pc]? = some ⟨none,.mem
    {kind := .load,space := some .global,sem := .weak,elem := .int .b 32,
      addr := ⟨.reg s.address 64,0⟩,dsts := [some dst]}⟩ := by
    fin_cases site
    · exact Flow.code_946
    · exact Flow.code_1416
  have hAddr : addr < 2^64 := recurringPageAddressBound hp hb hr
  have hAlign : addr%4 = 0 := by
    have := hp.alignment.2.2.2.2.2.2.2.2.2.2.1
    dsimp [addr,pageWordAddress]
    omega
  have hNext : Next kernel Assumptions.all l g cur.before v (.read a (afterLoad v [dst])) := by
    refine ⟨cur.localSteps.trans (run_rtg hvA),?_⟩
    rw [loaderOutCore (by rw [hV.1]; exact hRange.1) (by rw [hV.1]; exact hRange.2),
      out_event hV.2.2.2.1 (hV.1.symm ▸ hCode) rfl rfl]
    change Out.ev (loadTmpl [] l g v .global false 32 [dst] s.address 0) = _
    exact congrArg Out.ev (loadTmpl_global hV.2.1 hV.2.2.2.2.1 hAddr (by decide) hAlign)
  have hx : row/16 < (p.kLength batch+15)/16 := by omega
  obtain ⟨he,hPrefix,hTail⟩ := Step.protected_read_of_maximal hMax hg
    (a := a) (value := word) rfl (hp.pageBytes batch hb (row/16) hx)
    (fun _ hk _ _ _ hWrite => hFrame.input_unwritten hp (by simp [Params.inputRegions])
      (recurringPageByteInTable hp hb hr hk) hWrite)
    hNext cur.recorded cur.remaining cur.positive cur.bounded cur.released
    (Assumptions.wf_snoc_initial hMax.1)
  have hBytes := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
  have hState : afterLoad v [dst] (word.toBytes.map some) = next (setReg v dst word) := by
    rw [afterLoad_ok hV.2.1 hV.2.2.1 hBytes]
    simp [next,setReg,hV.2.1,hV.2.2.1]
  have hF := holdsSchedulerFrame hFrames.2 hVF (fun _ hm => List.mem_map_of_mem hm)
  have hReady : At (next (setReg v dst word)) (s.pc+1) (livePageWord p site batch row F) :=
    (hV.mono hF).set (fun pair hm => hFresh pair hm)
  rw [hState] at hPrefix hTail
  rw [hV.1] at he
  exact ⟨⟨cur.pos+1,_,_,cur.ending,Nat.succ_pos _,len_of_get he,
    releasedIfLast he (by intro h; cases h),hReady,hPrefix,hTail,.refl⟩,rfl,rfl,he⟩

private theorem finishPageStoresOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    {g page row : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (site slot : Fin 2)
    (hRow : row < 2^31) {F : List (Nat × Value)} (hExtra : RecurringRefreshFrame site F)
    (cur : OpeningTripCursor l X g (pageRefreshPc site-2)
      (recurringPageStoreInput l site slot page row++F)) :
    ∃ out : OpeningTripCursor l X g (rowRefreshPc site+1) F,
      out.pos = cur.pos+2 ∧ out.ending = cur.ending ∧
      X.get (g,cur.pos) = some ⟨pageRefreshPc site,
        .wr (pageRefreshAccess l g site false slot) (b32 page).toBytes⟩ ∧
      X.get (g,cur.pos+1) = some ⟨rowRefreshPc site,
        .wr (pageRefreshAccess l g site true slot) (b32 (row%16)).toBytes⟩ := by
  let q := recurringPageStoreSite site
  let pVal := (recurringPageSite site).physicalPage
  have hs := cur.checkpoint
  obtain ⟨hsCore,hsF⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨u,hu,hU⟩ := pageRefreshPrepCore hp (g := g) site slot cur.ready (hs.mono hsCore)
  have hLo : 174 ≤ pageRefreshPc site-2 := by fin_cases site <;> decide
  have hHi : pageRefreshPc site-2+2 ≤ 1906 := by fin_cases site <;> decide
  have hSeq : ((kernel.code.drop (pageRefreshPc site-2)).take 1).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨huA,huFrame⟩ := loaderLinear (regs := F.map Prod.fst) hLo hHi hs.1 hExtra.page hSeq hu
  have huF := holdsSchedulerFrame hsF huFrame (fun _ hm => List.mem_map_of_mem hm)
  have hPageCode : kernel.code[pageRefreshPc site]? = some ⟨none,.mem {
      kind := .store,space := some .local,sem := .weak,elem := .int .b 32,
      addr := ⟨.reg q.pageAddress 64,0⟩,srcs := [.reg pVal]}⟩ := by
    fin_cases site
    · exact Flow.code_949
    · exact Flow.code_1419
  have hPAccess : pageRefreshAccess l g site false slot =
      {loc := ⟨.local,g,l.localBase+kvLocalOffset 3 slot⟩,size := 4} := by
    fin_cases site <;> rfl
  have hNext : Next kernel Assumptions.all l g cur.before u
      (.write (pageRefreshAccess l g site false slot) (b32 page).toBytes (next u)) := by
    refine ⟨cur.localSteps.trans (run_rtg huA),?_⟩
    rw [hPAccess]
    exact refreshStoreTemplate hp 3 (by decide) slot (by fin_cases site <;> decide) hPageCode
      (hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.1,trivial⟩)
  obtain ⟨he,hRecorded,hRemaining⟩ := plainLoaderStoreOfMaximal hp hMax hg hw
    (by rw [hPAccess]) hNext cur.recorded cur.remaining cur.positive cur.bounded cur.released
  rw [hU.1] at he
  have hUP := (hU.mono hU.2.2.2.2.2.2).next
  obtain ⟨v,hv,hV⟩ := rowRefreshPrepCore hp (g := g) hRow site slot _ hUP
  have hRowLo : 174 ≤ pageRefreshPc site+1 := by fin_cases site <;> decide
  have hRowHi : pageRefreshPc site+1+3 ≤ 1906 := by fin_cases site <;> decide
  have hRowSeq : ((kernel.code.drop (pageRefreshPc site+1)).take 2).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hvA,hvFrame⟩ := loaderLinear (regs := F.map Prod.fst) hRowLo hRowHi hUP.1
    hExtra.row hRowSeq hv
  have hvF := holdsSchedulerFrame (show Holds (next u).regs F from huF) hvFrame
    (fun _ hm => List.mem_map_of_mem hm)
  have hRowCode : kernel.code[rowRefreshPc site]? = some ⟨none,.mem {
      kind := .store,space := some .local,sem := .weak,elem := .int .b 32,
      addr := ⟨.reg q.rowAddress 64,0⟩,srcs := [.reg q.rowValue]}⟩ := by
    fin_cases site
    · exact Flow.code_953
    · exact Flow.code_1423
  have hRAccess : pageRefreshAccess l g site true slot =
      {loc := ⟨.local,g,l.localBase+kvLocalOffset 2 slot⟩,size := 4} := by
    fin_cases site <;> rfl
  have hNextRow : Next kernel Assumptions.all l g (next u) v
      (.write (pageRefreshAccess l g site true slot) (b32 (row%16)).toBytes (next v)) := by
    refine ⟨run_rtg hvA,?_⟩
    rw [hRAccess]
    exact refreshStoreTemplate hp 2 (by decide) slot (by fin_cases site <;> decide) hRowCode hV
  obtain ⟨hr,hPrefix,hTail⟩ := plainLoaderStoreOfMaximal hp hMax hg hw
    (by rw [hRAccess]) hNextRow hRecorded hRemaining (Nat.succ_pos _) (len_of_get he)
      (releasedIfLast he (by intro h; cases h))
  rw [hV.1] at hr
  exact ⟨⟨cur.pos+2,_,_,cur.ending,Nat.succ_pos _,len_of_get hr,
    releasedIfLast hr (by intro h; cases h),(hV.mono hvF).next,hPrefix,hTail,.refl⟩,
    rfl,rfl,he,hr⟩


omit hp in
private def carryLocal {l : Launch} {X : Execution} {g start stop : Nat}
    {F G : List (Nat × Value)} (cur : OpeningTripCursor l X g start F) {t : TState}
    (ht : Relation.ReflTransGen (Tau kernel Assumptions.all l g) cur.ready t)
    (hAt : At t stop G) : OpeningTripCursor l X g stop G :=
  ⟨cur.pos,cur.before,t,cur.ending,cur.positive,cur.bounded,cur.released,
    hAt,cur.recorded,cur.remaining,cur.localSteps.trans ht⟩

set_option maxRecDepth 4096 in
/-- A warm or steady lane refreshes both private scratch words after reading the
protected page when live, or storing the masked value when the row is absent. -/
theorem recurringPageRefreshOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch row : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hRow : row < 2^31) (site slot : Fin 2)
    {F : List (Nat × Value)} (hExtra : RecurringRefreshFrame site F)
    (cur : OpeningTripCursor l X g ((recurringPageSite site).indexPc+10)
      (recurringPageGuardInput p l site slot batch row++F)) :
    let page := primingScratchPage p batch row
    let skip := primingScratchReads p batch row
    ∃ done : OpeningTripCursor l X g (rowRefreshPc site+1) F,
      done.pos = cur.pos+skip+2 ∧ done.ending = cur.ending ∧
      (row < p.kLength batch → X.get (g,cur.pos) = some ⟨(recurringPageReadSite site).pc,
        .rd {loc := globalLoc (pageWordAddress p batch (row/16)),size := 4}
          ((b32 page).toBytes.map some)⟩) ∧
      X.get (g,cur.pos+skip) = some ⟨pageRefreshPc site,
        .wr (pageRefreshAccess l g site false slot) (b32 page).toBytes⟩ ∧
      X.get (g,cur.pos+skip+1) = some ⟨rowRefreshPc site,
        .wr (pageRefreshAccess l g site true slot) (b32 (row%16)).toBytes⟩ := by
  dsimp only
  obtain ⟨t,ht,hT⟩ := recurringPageGuard (g := g) site slot cur.checkpoint
  by_cases hLive : row < p.kLength batch
  · rw [ite_eq_left hLive] at hT
    obtain ⟨u,hu,hU⟩ := recurringLivePagePrep hp (g := g) hb hLive site slot hExtra.live hT
    let carry := pageStoreCarry l site slot row
    have hKeep : ((kernel.code.drop ((recurringPageReadSite site).pc-2)).take 2).all
        (fun ins => ((carry++F).map Prod.fst).all
          (fun r => !(writesRegs ins.op).contains r)) = true := by
      apply List.all_eq_true.mpr
      intro ins hm
      simp only [List.map_append,List.all_append,Bool.and_eq_true]
      refine ⟨?_,List.all_eq_true.mp hExtra.read ins hm⟩
      have hCore : ((kernel.code.drop ((recurringPageReadSite site).pc-2)).take 2).all
          (fun i => (carry.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
        fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
      exact List.all_eq_true.mp hCore ins hm
    have hFresh : ∀ pair ∈ carry++F, pair.1 ≠ (recurringPageSite site).physicalPage := by
      intro pair hm
      rcases List.mem_append.mp hm with h | h
      · fin_cases site
        all_goals
          simp only [carry,pageStoreCarry,recurringPageSite,recurringPageStoreSite,
            List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [recurringPageSite]
      · exact hExtra.fresh pair h
    obtain ⟨v,hPos,hEnd,he⟩ := recurringPageReadOfMaximal hp hMax hFrame hg hb hLive site
      hKeep hFresh (carryLocal cur ((run_rtg ht).trans hu) hU)
    have hV := v.checkpoint
    have hPc : (recurringPageReadSite site).pc+1 = pageRefreshPc site-2 := by
      fin_cases site <;> decide
    have hFields := hV.2.2.2.2
    have hSplit := (holds_append v.ready.regs carry F).mp hFields.2
    have hAt : At v.ready (pageRefreshPc site-2)
        (recurringPageStoreInput l site slot (p.page batch (row/16)) row++F) :=
      hPc ▸ hV.mono ((holds_append ..).mpr ⟨pageStoreFacts ⟨hFields.1,hSplit.1⟩,hSplit.2⟩)
    let start := carryLocal v .refl hAt
    obtain ⟨done,hDone,hEnd',hPage,hRowWord⟩ :=
      finishPageStoresOfMaximal hp hMax hg hw site slot hRow hExtra start
    change v.pos = cur.pos+1 at hPos
    change v.ending = cur.ending at hEnd
    simp only [start,carryLocal,hPos,hEnd] at hDone hEnd' hPage hRowWord
    simp only [primingScratchPage,primingScratchReads,ite_eq_left hLive]
    exact ⟨done,hDone,hEnd',fun _ => he,hPage,hRowWord⟩
  · rw [ite_eq_right hLive] at hT
    obtain ⟨hCore,hF⟩ := (holds_append ..).mp hT.2.2.2.2
    have hCarry := ((holds_append ..).mp ((holds_append ..).mp hCore).2).1
    have hStore : At t (pageRefreshPc site-2)
        (recurringPageStoreInput l site slot 0 row++F) :=
      hT.mono ((holds_append ..).mpr ⟨pageStoreFacts ⟨hCore.2.2.2.1,hCarry⟩,hF⟩)
    obtain ⟨done,hPos,hEnd,hPage,hRowWord⟩ :=
      finishPageStoresOfMaximal hp hMax hg hw site slot hRow hExtra
        (carryLocal cur (run_rtg ht) hStore)
    simp only [primingScratchPage,primingScratchReads,ite_eq_right hLive,Nat.add_zero]
    exact ⟨done,hPos,hEnd,fun h => False.elim (hLive h),hPage,hRowWord⟩


/-- The lane-private page refresh does not alter either full-warp collective ordinal.
The paired write indices are available for later local reads and lane exchanges. -/
theorem recurringPageRefreshWarpOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch shuffles votes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (site slot : Fin 2) (row : Nat → Nat)
    (hRow : ∀ lane < 32, row lane < 2^31) {F : Nat → List (Nat × Value)}
    (hExtra : ∀ lane < 32, RecurringRefreshFrame site (F lane)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g ((recurringPageSite site).indexPc+10)
      (fun lane => recurringPageGuardInput p l site slot batch (row lane)++F lane)
      shuffles votes ends) :
    let thread := warpLane l g
    let skip := fun lane => primingScratchReads p batch (row lane)
    let page := fun lane => primingScratchPage p batch (row lane)
    ∃ done : SchedulerWarpReached l X g (rowRefreshPc site+1) F shuffles votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+skip lane+2 ∧
        X.get (thread lane,cur.pos lane+skip lane) = some ⟨pageRefreshPc site,
          .wr (pageRefreshAccess l (thread lane) site false slot) (b32 (page lane)).toBytes⟩ ∧
        X.get (thread lane,cur.pos lane+skip lane+1) = some ⟨rowRefreshPc site,
          .wr (pageRefreshAccess l (thread lane) site true slot) (b32 (row lane%16)).toBytes⟩ ∧
        (∀ i, cur.pos lane ≤ i → i < done.pos lane →
          ∀ loc, ¬ X.AsyncArrive (thread lane,i) loc true) ∧
        (row lane < p.kLength batch → X.get (thread lane,cur.pos lane) =
          some ⟨(recurringPageReadSite site).pc,
            .rd {loc := globalLoc (pageWordAddress p batch (row lane/16)),size := 4}
              ((b32 (page lane)).toBytes.map some)⟩) := by
  dsimp only
  let thread := warpLane l g
  let skip := fun lane => primingScratchReads p batch (row lane)
  let page := fun lane => primingScratchPage p batch (row lane)
  let Start (lane : Nat) :=
    recurringPageGuardInput p l site slot batch (row lane)++F lane
  have hLane (lane : Nat) (hl : lane < 32) :
      ∃ d : OpeningTripCursor l X (thread lane) (rowRefreshPc site+1) (F lane),
        d.pos = cur.pos lane+skip lane+2 ∧ d.ending = ends lane ∧
        ((X.tr (thread lane)).take d.pos).countP Execution.isShfl = shuffles ∧
        ((X.tr (thread lane)).take d.pos).countP isFullWarpVote = votes ∧
        X.get (thread lane,cur.pos lane+skip lane) = some ⟨pageRefreshPc site,
          .wr (pageRefreshAccess l (thread lane) site false slot) (b32 (page lane)).toBytes⟩ ∧
        X.get (thread lane,cur.pos lane+skip lane+1) = some ⟨rowRefreshPc site,
          .wr (pageRefreshAccess l (thread lane) site true slot) (b32 (row lane%16)).toBytes⟩ ∧
        (∀ i, cur.pos lane ≤ i → i < d.pos →
          ∀ loc, ¬ X.AsyncArrive (thread lane,i) loc true) ∧
        (row lane < p.kLength batch → X.get (thread lane,cur.pos lane) =
          some ⟨(recurringPageReadSite site).pc,
            .rd {loc := globalLoc (pageWordAddress p batch (row lane/16)),size := 4}
              ((b32 (page lane)).toBytes.map some)⟩) := by
    have hs := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
    let begin : OpeningTripCursor l X (thread lane) ((recurringPageSite site).indexPc+10)
        (Start lane) :=
      ⟨cur.pos lane,cur.before lane,cur.state lane,ends lane,cur.positive lane hl,
        cur.bounded lane hl,cur.released lane hl,cur.checkpoint lane hl,cur.recorded lane hl,
        cur.continuation lane hl,cur.localSteps lane hl⟩
    have hWarp : warpIndex l g = warpIndex l (thread lane) := hs.2
    have hw' : 14 ≤ warpIndex l (thread lane) := hWarp ▸ hw
    obtain ⟨d,hPos,hEnd,hRead,hPage,hWord⟩ := recurringPageRefreshOfMaximal hp hMax hFrame
      (g := thread lane) hs.1.2.1 hw' hb (hRow lane hl) site slot (hExtra lane hl) begin
    change d.pos = cur.pos lane+skip lane+2 at hPos
    change d.ending = ends lane at hEnd
    have hSucc : d.pos = cur.pos lane+skip lane+1+1 := hPos
    have hCount (mark : Event → Bool)
        (hReadFalse : ∀ a b pc, mark ⟨pc,.rd a b⟩ = false)
        (hWriteFalse : ∀ a b pc, mark ⟨pc,.wr a b⟩ = false) :
        ((X.tr (thread lane)).take d.pos).countP mark =
          ((X.tr (thread lane)).take (cur.pos lane)).countP mark := by
      rw [hSucc,countP_take_succ_false hWord (hWriteFalse ..),
        countP_take_succ_false hPage (hWriteFalse ..)]
      change ((X.tr (thread lane)).take (cur.pos lane+skip lane)).countP mark = _
      by_cases h : row lane < p.kLength batch
      · simp only [skip,primingScratchReads,ite_eq_left h]
        exact countP_take_succ_false (hRead h) (hReadFalse ..)
      · simp only [skip,primingScratchReads,ite_eq_right h,Nat.add_zero]
    have hQuiet (i : Nat) (hLo : cur.pos lane ≤ i) (hHi : i < d.pos) (loc : Loc) :
        ¬ X.AsyncArrive (thread lane,i) loc true := by
      rintro ⟨pc,he⟩
      rw [hPos] at hHi
      have hs : skip lane ≤ 1 := by dsimp [skip,primingScratchReads]; split <;> decide
      have hi : i = cur.pos lane+skip lane ∨ i = cur.pos lane+skip lane+1 ∨
          (i = cur.pos lane ∧ skip lane = 1) := by omega
      rcases hi with rfl | rfl | ⟨rfl,hOne⟩
      · rw [hPage] at he
        cases he
      · rw [hWord] at he
        cases he
      · have hlive : row lane < p.kLength batch := by
          by_contra! h
          simp [skip,primingScratchReads,Nat.not_lt_of_ge h] at hOne
        rw [hRead hlive] at he
        cases he
    exact ⟨d,hPos,hEnd,(hCount _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)).trans
      (cur.ordinals.shfl lane hl),(hCount _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)).trans
        (cur.ordinals.vote lane hl),hPage,hWord,hQuiet,hRead⟩
  classical
  let d (lane : Nat) (hl : lane < 32) := Classical.choose (hLane lane hl)
  let pos lane := if hl : lane < 32 then (d lane hl).pos else cur.pos lane
  let before lane := if hl : lane < 32 then (d lane hl).before else cur.before lane
  let ready lane := if hl : lane < 32 then (d lane hl).ready else cur.state lane
  let done : SchedulerWarpReached l X g (rowRefreshPc site+1) F shuffles votes ends := by
    refine ⟨⟨pos,before,ready,⟨?_,?_⟩,?_,?_,?_⟩,?_,?_,?_,?_⟩
    · intro lane hl
      simpa only [pos,dite_eq_left hl] using (Classical.choose_spec (hLane lane hl)).2.2.1
    · intro lane hl
      simpa only [pos,dite_eq_left hl] using (Classical.choose_spec (hLane lane hl)).2.2.2.1
    · intro lane hl
      have hEnd : (d lane hl).ending = ends lane := (Classical.choose_spec (hLane lane hl)).2.1
      simpa only [before,pos,dite_eq_left hl,hEnd] using (d lane hl).remaining
    · intro lane hl
      simpa only [before,ready,dite_eq_left hl] using (d lane hl).localSteps
    · intro lane hl
      simpa only [ready,dite_eq_left hl] using (d lane hl).checkpoint
    · intro lane hl
      simpa only [pos,dite_eq_left hl] using (d lane hl).positive
    · intro lane hl
      simpa only [pos,dite_eq_left hl] using (d lane hl).bounded
    · intro lane hl
      simpa only [pos,dite_eq_left hl] using (d lane hl).released
    · intro lane hl
      simpa only [before,pos,dite_eq_left hl] using (d lane hl).recorded
  refine ⟨done,fun lane hl => ?_⟩
  obtain ⟨hPos,_,_,_,hPage,hWord,hQuiet,hRead⟩ := Classical.choose_spec (hLane lane hl)
  refine ⟨?_,hPage,hWord,?_,hRead⟩
  · simpa only [done,pos,dite_eq_left hl] using hPos
  · simpa only [done,pos,dite_eq_left hl] using hQuiet

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
