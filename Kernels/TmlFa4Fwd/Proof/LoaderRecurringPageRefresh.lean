-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageRead
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageStore

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

def pageStoreCarry (l : Launch) (site : Fin 2) (slot : Fin 2) (row : Nat) :
    List (Nat × Value) :=
  let s := recurringPageStoreSite site
  let i := recurringPageSite site
  [(s.entry, b32 slot.val), (7295, b64 (l.localBase + 96)), (7294, b64 (l.localBase + 64)),
   (i.row, b32 row), (i.pageIndex, b32 (row / 16)), (1663, b32 16)]

def recurringPageBatchInputs (p : Params) (site : Fin 2) (batch : Nat) : List (Nat × Value) :=
  if site.val = 0 then
    [(7170, b32 batch), (7505, b64 p.pageTableStride), (7504, b64 p.pageTableBase)]
  else [(7763, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride)))]

/-- Facts at the decoded branch after the page index and row mask arithmetic. -/
def recurringPageGuardInput (p : Params) (l : Launch) (site : Fin 2) (slot : Fin 2)
    (batch row : Nat) : List (Nat × Value) :=
  recurringPageIndexFacts site row (p.kLength batch) ++
    (pageStoreCarry l site slot row ++ recurringPageBatchInputs p site batch)

private theorem pageStoreFacts {l : Launch} {site slot : Fin 2} {row page : Nat}
    {regs : Nat → Option Value}
    (h : Holds regs (((recurringPageSite site).physicalPage, b32 page) ::
      pageStoreCarry l site slot row)) :
    Holds regs (recurringPageStoreInput l site slot page row) := by
  exact ⟨h.2.1, h.2.2.1, h.1, h.2.2.2⟩

private theorem recurringPageGuard {p : Params} {l : Launch}
    {g row batch : Nat} (site : Fin 2) (slot : Fin 2)
    {s : TState} {F : List (Nat × Value)} (hs : At s ((recurringPageSite site).indexPc + 10)
      (recurringPageGuardInput p l site slot batch row ++ F)) :
    ∃ t, run kernel Assumptions.all l g 1 s = some t ∧
      At t (if row < p.kLength batch then (recurringPageSite site).indexPc + 11
        else pageRefreshPc site - 2)
        (recurringPageGuardInput p l site slot batch row ++ F) := by
  let guardPc := (recurringPageSite site).indexPc + 10
  let dstPc := pageRefreshPc site - 2
  let bf := (recurringPageSite site).masked
  have hc : kernel.code[guardPc]? = some ⟨some (bf, false), .bra dstPc false⟩ := by
    fin_cases site
    · exact Flow.code_939
    · exact Flow.code_1413
  have hPred : s.regs bf = some (.pred (decide (p.kLength batch ≤ row))) :=
    holds_mem ((holds_append ..).mp hs.2.2.2.2).1
      (by simp [bf, recurringPageGuardInput, recurringPageIndexFacts])
  obtain ⟨t, ht, hT⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    hc (decide (p.kLength batch ≤ row)) hs hPred (by simp)
  have hLo : 174 ≤ guardPc := by fin_cases site <;> decide
  have hHi : guardPc + 1 ≤ 1906 := by fin_cases site <;> decide
  have het : (if decide (p.kLength batch ≤ row) then dstPc else guardPc + 1) =
      if row < p.kLength batch then (recurringPageSite site).indexPc + 11 else dstPc := by
    by_cases h : row < p.kLength batch
    · simp [h, Nat.not_le_of_gt h, guardPc]
    · simp [h, Nat.le_of_not_gt h]
  exact ⟨t, (loaderLinear (regs := []) hLo hHi hs.1 (by simp) rfl ht).1, het ▸ hT⟩

/-- Warm setup forms the batch-adjusted page base after the guard. Steady setup enters
with that base in a separate register established before its outer loop. -/
private theorem recurringLivePagePrep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch row : Nat} (hb : batch < p.batch) (hRow : row < p.kLength batch)
    (site : Fin 2) (slot : Fin 2)
    {s : TState} {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop ((recurringPageSite site).indexPc + 11)).take
      ((recurringPageReadSite site).pc - 2 - ((recurringPageSite site).indexPc + 11))).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s ((recurringPageSite site).indexPc + 11)
      (recurringPageGuardInput p l site slot batch row ++ F)) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧
      At t ((recurringPageReadSite site).pc - 2)
        (recurringPageReadInput p site batch row ++ (pageStoreCarry l site slot row ++ F)) := by
  have ⟨hFields, hF⟩ := (holds_append ..).mp hs.2.2.2.2
  fin_cases site
  · let addr := p.pageTableBase + 4 * (batch * p.pageTableStride)
    let start := [(7170, b32 batch), (7505, b64 p.pageTableStride), (7504, b64 p.pageTableBase)]
    have hPre : At s 940 start := by
      apply hs.mono
      exact ((holds_append ..).mp ((holds_append ..).mp hFields).2).2
    have hRegion := hp.ranges ⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩
      (by simp [Params.inputRegions])
    have hBig : addr < 2 ^ 64 := by
      have hStride := (hp.pageTable batch hb).1
      have hLive : 0 < p.pageTableStride := by omega
      have hSucc := Nat.mul_le_mul_right p.pageTableStride (show batch + 1 ≤ p.batch by omega)
      rw [Nat.add_mul, Nat.one_mul] at hSucc
      change p.pageTableBase + 4 * p.batch * p.pageTableStride ≤ 2 ^ 64 at hRegion
      rw [Nat.mul_assoc] at hRegion
      dsimp [addr]
      omega
    have hBatch31 : batch < 2 ^ 31 := hb.trans hp.shape.2.1
    have hBatch32 : batch < 2 ^ 32 := by omega
    have hBatch64 : batch < 2 ^ 64 := by omega
    have hBase : p.pageTableBase < 2 ^ 64 := by dsimp [addr] at hBig; omega
    have hStride64 : p.pageTableStride < 2 ^ 64 := by
      have hpz : 1 ≤ p.batch := by omega
      have hm := Nat.mul_le_mul_right p.pageTableStride hpz
      rw [Nat.one_mul] at hm
      change p.pageTableBase + 4 * p.batch * p.pageTableStride ≤ 2 ^ 64 at hRegion
      rw [Nat.mul_assoc] at hRegion
      omega
    have hProd : batch * p.pageTableStride < 2 ^ 64 := by dsimp [addr] at hBig; omega
    have hBytes : 4 * (batch * p.pageTableStride) < 2 ^ 64 := by dsimp [addr] at hBig; omega
    have hSigned : toSigned 32 (BitVec.ofNat 64 batch) = (batch : Int) := by
      simp only [toSigned, toNat_ofNat_lt hBatch64, Nat.mod_eq_of_lt hBatch32,
        ite_eq_left hBatch31]
    have hTwo : (truncBits 32 (BitVec.ofInt 64 2)).toNat = 2 := rfl
    have hCore : ∃ t, run kernel [] l g 4 s = some t ∧ At t 944 [(7648, b64 addr)] := by
      dsimp only [start] at hPre
      seg_fp hPre using
        simp only [b64, cvtIntBits, intBits, intOf, intSat, Bool.not_false, hSigned, addr,
          hTwo, show ¬(2 : Nat) ≥ 64 by decide, ↓reduceIte, BitVec.ofInt_natCast,
          truncBits_ofNat hBatch32 (by decide), truncBits_ofNat hBatch64 (by decide),
          truncBits_ofNat hBase (by decide), truncBits_ofNat hStride64 (by decide),
          ← BitVec.ofNat_mul, Nat.mul_comm p.pageTableStride batch,
          truncBits_ofNat hProd (by decide), nf_shl, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (batch * p.pageTableStride) 4, truncBits_ofNat hBytes (by decide),
          ← BitVec.ofNat_add, truncBits_ofNat hBig (by decide)]
    obtain ⟨t, ht, hT⟩ := hCore
    let carry := pageStoreCarry l 0 slot row
    have hOwn : ((kernel.code.drop 940).take 4).all
        (fun ins => (carry.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
        true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hAudit : ((kernel.code.drop 940).take 4).all
        (fun ins => ((carry ++ F).map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
        true := by
      apply List.all_eq_true.mpr
      intro ins hm
      simp only [List.map_append, List.all_append, Bool.and_eq_true]
      exact ⟨List.all_eq_true.mp hOwn ins hm, List.all_eq_true.mp hKeep ins hm⟩
    obtain ⟨htA, hFrame⟩ := loaderLinear (by decide) (by decide) hPre.1 hAudit
      (by set_option maxRecDepth 100000 in kernel_rfl) ht
    have hC := (holds_append ..).mpr
      ⟨((holds_append ..).mp ((holds_append ..).mp hFields).2).1, hF⟩
    have held := Epilogue.holdsSchedulerFrame hC hFrame (fun _ hm => List.mem_map_of_mem hm)
    have hPage := ((holds_append ..).mp held).1
    exact ⟨t, run_rtg htA, hT.mono ((holds_append ..).mpr
      ⟨⟨hPage.2.2.2.2.1, hT.2.2.2.2.1, trivial⟩, held⟩)⟩
  · refine ⟨s, .refl, hs.mono ((holds_append ..).mpr ⟨?_, ?_⟩)⟩
    · change Holds s.regs (recurringPageReadInput p 1 batch row)
      have hBatch : Holds s.regs (recurringPageBatchInputs p 1 batch) :=
        ((holds_append ..).mp ((holds_append ..).mp hFields).2).2
      exact ⟨holds_mem hFields (by simp [recurringPageGuardInput, recurringPageIndexFacts]),
        hBatch.1, trivial⟩
    · exact (holds_append ..).mpr ⟨((holds_append ..).mp ((holds_append ..).mp hFields).2).1, hF⟩

/-- Registers retained through the optional page lookup and both scratch writes. -/
structure RecurringRefreshFrame (site : Fin 2) (F : List (Nat × Value)) : Prop where
  live : ((kernel.code.drop ((recurringPageSite site).indexPc + 11)).take
      ((recurringPageReadSite site).pc - 2 - ((recurringPageSite site).indexPc + 11))).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  read : ((kernel.code.drop ((recurringPageReadSite site).pc - 2)).take 2).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  fresh : ∀ pair ∈ F, pair.1 ≠ (recurringPageSite site).physicalPage
  page : ((kernel.code.drop (pageRefreshPc site - 2)).take 2).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  row : ((kernel.code.drop (pageRefreshPc site + 1)).take 3).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hX hFrame

/-- The current slot either reads its live page word or skips directly to the stores. -/
theorem recurringPageBeforeStores {g index batch row : Nat} (hb : batch < p.batch) (site : Fin 2)
    (slot : Fin 2) {s : TState} {F : List (Nat × Value)} (hExtra : RecurringRefreshFrame site F)
    (hs : At s ((recurringPageSite site).indexPc + 10)
      (recurringPageGuardInput p l site slot batch row ++ F)) {o : Option TState}
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) o)
    (hNonempty : (X.tr g).drop index ≠ []) :
    let page := primingScratchPage p batch row
    let skip := primingScratchReads p batch row
    (row < p.kLength batch → X.get (g, index) = some ⟨(recurringPageReadSite site).pc,
      .rd {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
        ((b32 page).toBytes.map some)⟩) ∧
    ∃ t, At t (pageRefreshPc site - 2) (recurringPageStoreInput l site slot page row ++ F) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (index + skip)) o := by
  dsimp only
  obtain ⟨t, ht, hT⟩ := recurringPageGuard (g := g) site slot hs
  have hFirst : index < (X.tr g).length := by
    by_contra! hPast
    exact hNonempty (List.drop_eq_nil_of_le hPast)
  have hTail := hRun.after_local_nonempty (run_rtg ht) hNonempty
  by_cases hLive : row < p.kLength batch
  · rw [ite_eq_left hLive] at hT
    obtain ⟨u, hu, hU⟩ := recurringLivePagePrep hp (g := g) hb hLive site slot hExtra.live hT
    have hKeep : ((kernel.code.drop ((recurringPageReadSite site).pc - 2)).take 2).all
        (fun ins => ((pageStoreCarry l site slot row ++ F).map Prod.fst).all
          (fun r => !(writesRegs ins.op).contains r)) = true := by
      apply List.all_eq_true.mpr
      intro ins hm
      simp only [List.map_append, List.all_append, Bool.and_eq_true]
      refine ⟨?_, List.all_eq_true.mp hExtra.read ins hm⟩
      have hCore : ((kernel.code.drop ((recurringPageReadSite site).pc - 2)).take 2).all
          (fun i => ((pageStoreCarry l site slot row).map Prod.fst).all
            (fun r => !(writesRegs i.op).contains r)) = true := by
        fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
      exact List.all_eq_true.mp hCore ins hm
    have hFresh : ∀ pair ∈ pageStoreCarry l site slot row ++ F,
        pair.1 ≠ (recurringPageSite site).physicalPage := by
      intro pair hm
      rcases List.mem_append.mp hm with hCore | hF
      · fin_cases site
        all_goals
          simp only [pageStoreCarry, recurringPageSite, recurringPageStoreSite,
            List.mem_cons, List.not_mem_nil, or_false] at hCore
          rcases hCore with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [recurringPageSite]
      · exact hExtra.fresh pair hF
    obtain ⟨v, hRead, hV, hRest⟩ :=
      recurringPageReadObservedInPrefixWithFrame hp hX hFrame hb hLive site
        hKeep hFresh hU (hTail.after_local_nonempty hu hNonempty) hFirst
    have hPc : (recurringPageReadSite site).pc + 1 = pageRefreshPc site - 2 := by
      fin_cases site <;> decide
    have hVCore := (holds_append ..).mp
      (show Holds v.regs ((((recurringPageSite site).physicalPage, b32 (p.page batch (row / 16))) ::
        pageStoreCarry l site slot row) ++ F) from hV.2.2.2.2)
    simp only [primingScratchPage, primingScratchReads, ite_eq_left hLive]
    exact ⟨fun _ => hRead, _, hPc ▸ hV.mono
      ((holds_append ..).mpr ⟨pageStoreFacts hVCore.1, hVCore.2⟩), hRest⟩
  · rw [ite_eq_right hLive] at hT
    have ⟨hCore, hF⟩ := (holds_append ..).mp hT.2.2.2.2
    have hFrame := ((holds_append ..).mp ((holds_append ..).mp hCore).2).1
    have hStore := hT.mono ((holds_append ..).mpr
      ⟨pageStoreFacts ⟨hCore.2.2.2.1, hFrame⟩, hF⟩)
    simp only [primingScratchPage, primingScratchReads, ite_eq_right hLive, Nat.add_zero]
    exact ⟨fun h => (hLive h).elim, _, hStore, hTail⟩

omit hp hX hFrame in
private theorem afterNonShuffle {X : Execution} {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hn : Execution.isShfl e = false) :
    ((X.tr g).take (k + 1)).countP Execution.isShfl =
      ((X.tr g).take k).countP Execution.isShfl := by
  have hGet : (X.tr g)[k]? = some e := he
  rw [List.take_add_one, hGet, Option.toList_some, List.countP_append]
  simp [hn]

/-- Either this slot contains the recorded page lookup or its two local stores
precede that lookup. The replay preserves the current shuffle ordinal. -/
theorem recurringPageLookupOrNextSlot {g index j batch row : Nat} (hb : batch < p.batch)
    (hRow : row < 2 ^ 31) (site : Fin 2) (slot : Fin 2) {s : TState} {F : List (Nat × Value)}
    (hExtra : RecurringRefreshFrame site F)
    (hs : At s ((recurringPageSite site).indexPc + 10)
      (recurringPageGuardInput p l site slot batch row ++ F)) {o : Option TState}
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) o) {a : Acc}
    {bytes : List (Option Byte)} (hPos : index ≤ j)
    (he : X.get (g, j) = some ⟨(recurringPageReadSite site).pc, .rd a bytes⟩) :
    (row < p.kLength batch ∧
      a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}) ∨
    ∃ pos ≤ j, ∃ t, At t (rowRefreshPc site + 1) F ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl := by
  let pos := index + primingScratchReads p batch row
  obtain ⟨hRead, t, ht, hTail⟩ :=
    recurringPageBeforeStores hp hX hFrame hb site slot hExtra hs hRun
      (traceAfterObservedEvent he hPos)
  by_cases hNow : row < p.kLength batch ∧ j = index
  · obtain ⟨hLive, rfl⟩ := hNow
    have hEq := congrArg Event.kind (Option.some.inj (he.symm.trans (hRead hLive)))
    exact .inl ⟨hLive, (Kind.rd.inj hEq).1⟩
  have hStart : pos ≤ j := by
    by_cases hLive : row < p.kLength batch
    · have hNe : j ≠ index := fun eq => hNow ⟨hLive, eq⟩
      simp only [pos, primingScratchReads, ite_eq_left hLive]
      omega
    · simpa only [pos, primingScratchReads, ite_eq_right hLive, Nat.add_zero] using hPos
  have advance {k : Nat} {sp : Nat} {acc : Acc} {data : List Byte}
      (hk : k ≤ j) (hStore : X.get (g, k) = some ⟨sp, .wr acc data⟩) : k + 1 ≤ j := by
    by_contra hn
    have eq : j = k := by omega
    rw [eq] at he
    cases congrArg Event.kind (Option.some.inj (he.symm.trans hStore))
  obtain ⟨hPage, hWrittenRow, u, hu, hU⟩ :=
    recurringPageStoresObservedWithDemand hp site slot hRow hExtra.page hExtra.row ht hTail
      (traceAfterObservedEvent he hStart)
      (fun _ hStore _ => traceAfterObservedEvent he (advance hStart hStore))
  have hRank : ((X.tr g).take pos).countP Execution.isShfl =
      ((X.tr g).take index).countP Execution.isShfl := by
    by_cases hLive : row < p.kLength batch
    · simpa only [pos, primingScratchReads, ite_eq_left hLive] using
        afterNonShuffle (hRead hLive) rfl
    · simp only [pos, primingScratchReads, ite_eq_right hLive, Nat.add_zero]
  refine .inr ⟨pos + 2, advance (advance hStart hPage) hWrittenRow, u, hu, hU, ?_⟩
  rw [show pos + 2 = pos + 1 + 1 by omega, afterNonShuffle hWrittenRow rfl,
    afterNonShuffle hPage rfl, hRank]

/-- Each warm or steady iteration refreshes the physical page and row words in the
actual trace. A masked row takes the branch over the global page lookup and stores zero. -/
theorem recurringPageRefreshObservedInPrefixWithFrame {g index batch row : Nat}
    (hb : batch < p.batch) (hRow : row < 2 ^ 31) (site : Fin 2) (slot : Fin 2) {s : TState}
    {F : List (Nat × Value)} (hExtra : RecurringRefreshFrame site F)
    (hs : At s ((recurringPageSite site).indexPc + 10)
      (recurringPageGuardInput p l site slot batch row ++ F)) {o : Option TState}
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) o)
    (hSeen : PrefixDemand X g index (rowRefreshPc site) o) :
    let page := if row < p.kLength batch then p.page batch (row / 16) else 0
    let skip := if row < p.kLength batch then 1 else 0
    (row < p.kLength batch → X.get (g, index) = some ⟨(recurringPageReadSite site).pc,
      .rd {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
        ((b32 page).toBytes.map some)⟩) ∧
    X.get (g, index + skip) =
      some ⟨pageRefreshPc site, .wr (pageRefreshAccess l g site false slot) (b32 page).toBytes⟩ ∧
    X.get (g, index + skip + 1) = some ⟨rowRefreshPc site,
      .wr (pageRefreshAccess l g site true slot) (b32 (row % 16)).toBytes⟩ ∧
    ∃ t, At t (rowRefreshPc site + 1) F ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (index + skip + 2)) o := by
  obtain ⟨hRead, t, ht, hTail⟩ :=
    recurringPageBeforeStores hp hX hFrame hb site slot hExtra hs hRun (hSeen.nonempty hRun)
  have hOrder : (recurringPageReadSite site).pc ≤ rowRefreshPc site := by
    fin_cases site <;> decide
  have hAfterRead : PrefixDemand X g (index + primingScratchReads p batch row)
      (rowRefreshPc site) o := by
    by_cases hLive : row < p.kLength batch
    · simpa only [primingScratchReads, ite_eq_left hLive] using hSeen.advance (hRead hLive) hOrder
    · simpa only [primingScratchReads, ite_eq_right hLive, Nat.add_zero] using hSeen
  exact ⟨hRead, recurringPageStoresObservedInPrefixWithFrame hp site slot hRow
    hExtra.page hExtra.row ht hTail hAfterRead⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
