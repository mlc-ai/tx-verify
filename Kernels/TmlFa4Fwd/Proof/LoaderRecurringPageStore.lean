-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageIndex
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchWords
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixDemand

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

structure RecurringPageStoreSite where
  kPacket : Fin 4
  entry : Nat
  byteOffset : Nat
  pageAddress : Nat
  rowAddress : Nat
  rowValue : Nat

def recurringPageStoreSite : Fin 2 → RecurringPageStoreSite
  | 0 => ⟨0, 7175, 7651, 7652, 7653, 1975⟩
  | 1 => ⟨2, 7182, 7766, 7767, 7768, 2137⟩

def pageRefreshPc (site : Fin 2) : Nat :=
  (recurringScratchWord (recurringPageStoreSite site).kPacket false).store

def rowRefreshPc (site : Fin 2) : Nat :=
  (recurringScratchWord (recurringPageStoreSite site).kPacket true).store

def pageRefreshAccess (l : Launch) (g : Nat) (site : Fin 2) (isRow : Bool)
    (slot : Fin 2) : Acc :=
  scratchReloadAccess l g (recurringScratchWord (recurringPageStoreSite site).kPacket isRow) slot

/-- The decoded local-store prelude follows either the physical page read or its masked arm. -/
def recurringPageStoreInput (l : Launch) (site : Fin 2) (slot : Fin 2) (page row : Nat) :
    List (Nat × Value) :=
  let s := recurringPageStoreSite site
  let i := recurringPageSite site
  [(s.entry, b32 slot.val), (7295, b64 (l.localBase + 96)),
   (i.physicalPage, b32 page), (7294, b64 (l.localBase + 64)),
   (i.row, b32 row), (i.pageIndex, b32 (row / 16)), (1663, b32 16)]

private def recurringRowStoreCarry (l : Launch) (site : Fin 2) (slot : Fin 2) (row : Nat) :
    List (Nat × Value) :=
  let s := recurringPageStoreSite site
  let i := recurringPageSite site
  [(s.byteOffset, b64 (4 * slot.val)), (7294, b64 (l.localBase + 64)),
   (i.row, b32 row), (i.pageIndex, b32 (row / 16)), (1663, b32 16)]

private theorem pageRefreshPrepCore {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g page row : Nat} (site : Fin 2) (slot : Fin 2) :
    Seg kernel [] l g 2 (pageRefreshPc site - 2)
      (recurringPageStoreInput l site slot page row) (pageRefreshPc site)
      (((recurringPageStoreSite site).pageAddress, b64 (l.localBase + kvLocalOffset 3 slot)) ::
       ((recurringPageSite site).physicalPage, b32 page) ::
       recurringRowStoreCarry l site slot row) := by
  have hStack := hp.localMemory.2.1
  have hSlot := slot.isLt
  have hLoc : l.localBase + 96 < 2 ^ 64 := by omega
  have hOff : 4 * slot.val < 2 ^ 64 := by omega
  have hBound : l.localBase + 96 + 4 * slot.val < 2 ^ 64 := by omega
  have hOffset : kvLocalOffset 3 slot = 96 + 4 * slot.val := by rfl
  have h32 : slot.val < 2 ^ 32 := by omega
  have h64 : slot.val < 2 ^ 64 := by omega
  have hI4 : (truncBits 32 (BitVec.ofInt 64 4)).toNat = 4 := rfl
  have hc : Seg kernel [] l g 2 (pageRefreshPc site - 2)
      (recurringPageStoreInput l site slot page row) (pageRefreshPc site)
      (((recurringPageStoreSite site).pageAddress, b64 (l.localBase + kvLocalOffset 3 slot)) ::
       ((recurringPageSite site).physicalPage, b32 page) ::
       recurringRowStoreCarry l site slot row) := by
    fin_cases site <;> intro t ht <;>
      simp only [pageRefreshPc, recurringPageStoreSite, recurringPageSite, recurringScratchWord,
        recurringPageStoreInput, recurringRowStoreCarry] at ht ⊢ <;>
      seg_fp ht using
        simp only [b64, kind_u_beq_s, Bool.false_eq_true, ↓reduceIte, toNat_ofNat_lt h64, hI4,
          truncBits_ofNat h32 (by decide), truncBits_ofNat hOff (by decide),
          truncBits_ofNat hLoc (by decide), ← BitVec.ofNat_add, truncBits_ofNat hBound (by decide),
          hOffset, ← Nat.add_assoc, Nat.mul_comm slot.val 4]
  exact hc

private theorem rowRefreshPrepCore {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g row : Nat} (hRow : row < 2 ^ 31) (site : Fin 2) (slot : Fin 2) :
    Seg kernel [] l g 3 (pageRefreshPc site + 1)
      (recurringRowStoreCarry l site slot row) (rowRefreshPc site)
      [((recurringPageStoreSite site).rowAddress, b64 (l.localBase + kvLocalOffset 2 slot)),
       ((recurringPageStoreSite site).rowValue, b32 (row % 16))] := by
  have hStack := hp.localMemory.2.1
  have hSlot := slot.isLt
  have hLoc : l.localBase + 64 < 2 ^ 64 := by omega
  have hOff : 4 * slot.val < 2 ^ 64 := by omega
  have hBound : l.localBase + 64 + 4 * slot.val < 2 ^ 64 := by omega
  have h32 : row < 2 ^ 32 := by omega
  have h64 : row < 2 ^ 64 := by omega
  have hPage : row / 16 < 2 ^ 32 := by omega
  have hMul : row / 16 * 16 < 2 ^ 32 := by omega
  have hMul64 : row / 16 * 16 < 2 ^ 64 := by omega
  have hMod : row - row / 16 * 16 = row % 16 := by omega
  have hOffset : kvLocalOffset 2 slot = 64 + 4 * slot.val := by rfl
  have hc : Seg kernel [] l g 3 (pageRefreshPc site + 1)
      (recurringRowStoreCarry l site slot row) (rowRefreshPc site)
      [((recurringPageStoreSite site).rowAddress, b64 (l.localBase + kvLocalOffset 2 slot)),
       ((recurringPageStoreSite site).rowValue, b32 (row % 16))] := by
    fin_cases site <;> intro t ht <;>
      simp only [pageRefreshPc, rowRefreshPc, recurringPageStoreSite, recurringPageSite,
        recurringScratchWord, recurringRowStoreCarry] at ht ⊢ <;>
      seg_fp ht using
        norm_bits [Nat.mod_eq_of_lt hLoc, Nat.mod_eq_of_lt hOff, Nat.mod_eq_of_lt hBound,
          Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hPage,
          Nat.mod_eq_of_lt hMul, Nat.mod_eq_of_lt hMul64, hMod,
          hOffset, Nat.mul_comm 16 (row / 16), Nat.add_assoc]
  exact hc

private theorem refreshStoreTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g pc base source value : Nat} (array : Fin 4) (hArray : ¬ array.val < 2) (slot : Fin 2)
    (hRange : 174 ≤ pc ∧ pc < 1906)
    (hCode : kernel.code[pc]? = some ⟨none, .mem {
      kind := .store, space := some .local, sem := .weak, elem := .int .b 32,
      addr := ⟨.reg base 64, 0⟩, srcs := [.reg source]}⟩) {t : TState}
    (ht : At t pc [(base, b64 (l.localBase + kvLocalOffset array slot)), (source, b32 value)]) :
    out kernel Assumptions.all l g t = .ev (.write
      {loc := ⟨.local, g, l.localBase + kvLocalOffset array slot⟩, size := 4}
      (b32 value).toBytes (next t)) := by
  have hBound := hp.localMemory.2.1
  have hLocal : l.localBase + kvLocalOffset array slot < 2 ^ 64 := by
    have hOffset := kvLocalOffset_bound array slot (byte := 0) (by rw [ite_eq_right hArray]; decide)
    omega
  have hAlign : (l.localBase + kvLocalOffset array slot) % 4 = 0 := by
    simpa only [ite_eq_right hArray] using kvLocalOffset_aligned array slot hp.localMemory.1
  have hAddr := ht.2.2.2.2.1
  have hVal := ht.2.2.2.2.2.1
  rw [loaderOutCore (by rw [ht.1]; exact hRange.1) (by rw [ht.1]; exact hRange.2)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact hCode) rfl rfl]
  change Out.ev (accessTmpl [] l g t {
    kind := .store, space := some .local, sem := .weak, elem := .int .b 32,
    addr := ⟨.reg base 64, 0⟩, srcs := [.reg source] }) = _
  simp [accessTmpl, accessAcc, accessLoc, elemAcc, wrapAddr, readBits, readValue, readReg, hAddr,
    hVal, hAlign, ht.2.1, b64, storeValue_of_bytes (show (b32 value).bytes = 32 / 8 from rfl),
    next, afterStore, Loc.at, MemAccess.strongLocOk, MemAccess.semAcc, CacheHints.globalOnly,
    DType.width, truncBits_ofNat hLocal (by decide), toNat_ofNat_lt hLocal,
    bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g index page row : Nat} (site : Fin 2) (slot : Fin 2) (hRow : row < 2 ^ 31)
include hp site slot hRow

/-- The page word and decoded row remainder are consecutive events in the actual lane
trace. Both stores are confined to the corresponding 4-byte slots of its private stack. -/
theorem recurringPageStoresObservedWithDemand {s : TState} {F : List (Nat × Value)}
    (hPageKeep : ((kernel.code.drop (pageRefreshPc site - 2)).take 2).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hRowKeep : ((kernel.code.drop (pageRefreshPc site + 1)).take 3).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hs : At s (pageRefreshPc site - 2) (recurringPageStoreInput l site slot page row ++ F))
    {o : Option TState} (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) o)
    (hPage : (X.tr g).drop index ≠ [])
    (hRowSeen : ∀ u, X.get (g, index) =
      some ⟨pageRefreshPc site, .wr (pageRefreshAccess l g site false slot) (b32 page).toBytes⟩ →
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 1)) o →
      (X.tr g).drop (index + 1) ≠ []) :
    X.get (g, index) =
      some ⟨pageRefreshPc site, .wr (pageRefreshAccess l g site false slot) (b32 page).toBytes⟩ ∧
    X.get (g, index + 1) = some ⟨rowRefreshPc site,
      .wr (pageRefreshAccess l g site true slot) (b32 (row % 16)).toBytes⟩ ∧
    ∃ t, At t (rowRefreshPc site + 1) F ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (index + 2)) o := by
  let q := recurringPageStoreSite site
  let pVal := (recurringPageSite site).physicalPage
  have ⟨hsCore, hsF⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨u, hu, hU⟩ := pageRefreshPrepCore hp (g := g) site slot s (hs.mono hsCore)
  have hLo : 174 ≤ pageRefreshPc site - 2 := by fin_cases site <;> decide
  have hHi : pageRefreshPc site - 2 + 2 ≤ 1906 := by fin_cases site <;> decide
  have hSeq : ((kernel.code.drop (pageRefreshPc site - 2)).take 1).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := F.map Prod.fst) hLo hHi hs.1 hPageKeep hSeq hu
  have huF := Epilogue.holdsSchedulerFrame hsF huFrame (fun _ hm => List.mem_map_of_mem hm)
  have hPageCode : kernel.code[pageRefreshPc site]? = some ⟨none, .mem {
      kind := .store, space := some .local, sem := .weak, elem := .int .b 32,
      addr := ⟨.reg q.pageAddress 64, 0⟩, srcs := [.reg pVal]}⟩ := by
    fin_cases site
    · exact Flow.code_949
    · exact Flow.code_1419
  have hPAccess : pageRefreshAccess l g site false slot =
      {loc := ⟨.local, g, l.localBase + kvLocalOffset 3 slot⟩, size := 4} := by
    fin_cases site <;> rfl
  have hNext : Next kernel Assumptions.all l g s u
      (.write (pageRefreshAccess l g site false slot) (b32 page).toBytes (next u)) := by
    refine ⟨run_rtg huA, ?_⟩
    rw [hPAccess]
    exact refreshStoreTemplate hp 3 (by decide) slot (by fin_cases site <;> decide) hPageCode
      (hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, trivial⟩)
  obtain ⟨_, _, hpEvent, ⟨rfl, hPostPage⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hRun hPage
  obtain rfl := Option.some.inj hPostPage
  have hUP := (hU.mono hU.2.2.2.2.2.2).next
  obtain ⟨v, hv, hV⟩ := rowRefreshPrepCore hp (g := g) hRow site slot _ hUP
  have hRowLo : 174 ≤ pageRefreshPc site + 1 := by fin_cases site <;> decide
  have hRowHi : pageRefreshPc site + 1 + 3 ≤ 1906 := by fin_cases site <;> decide
  have hRowSeq : ((kernel.code.drop (pageRefreshPc site + 1)).take 2).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := F.map Prod.fst) hRowLo hRowHi hUP.1
    hRowKeep hRowSeq hv
  have hvF := Epilogue.holdsSchedulerFrame (show Holds (next u).regs F from huF) hvFrame
    (fun _ hm => List.mem_map_of_mem hm)
  have hRowCode : kernel.code[rowRefreshPc site]? = some ⟨none, .mem {
      kind := .store, space := some .local, sem := .weak, elem := .int .b 32,
      addr := ⟨.reg q.rowAddress 64, 0⟩, srcs := [.reg q.rowValue]}⟩ := by
    fin_cases site
    · exact Flow.code_953
    · exact Flow.code_1423
  have hRAccess : pageRefreshAccess l g site true slot =
      {loc := ⟨.local, g, l.localBase + kvLocalOffset 2 slot⟩, size := 4} := by
    fin_cases site <;> rfl
  have hNextRow : Next kernel Assumptions.all l g (next u) v
      (.write (pageRefreshAccess l g site true slot) (b32 (row % 16)).toBytes (next v)) := by
    refine ⟨run_rtg hvA, ?_⟩
    rw [hRAccess]
    exact refreshStoreTemplate hp 2 (by decide) slot (by fin_cases site <;> decide) hRowCode hV
  have hpEvent' : X.get (g, index) =
      some ⟨pageRefreshPc site, .wr (pageRefreshAccess l g site false slot) (b32 page).toBytes⟩ :=
    by simpa only [hU.1] using hpEvent
  obtain ⟨_, _, hrEvent, ⟨rfl, hPostRow⟩, hRest⟩ := hNextRow.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hTail (hRowSeen _ hpEvent' hTail)
  obtain rfl := Option.some.inj hPostRow
  exact ⟨by simpa only [hU.1] using hpEvent, by simpa only [hV.1] using hrEvent,
    _, (hV.mono hvF).next, by simpa only [Nat.add_assoc] using hRest⟩

/-- The page word and decoded row remainder are consecutive events in the actual lane
trace. Both stores are confined to the corresponding 4-byte slots of its private stack. -/
theorem recurringPageStoresObservedInPrefixWithFrame {s : TState} {F : List (Nat × Value)}
    (hPageKeep : ((kernel.code.drop (pageRefreshPc site - 2)).take 2).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hRowKeep : ((kernel.code.drop (pageRefreshPc site + 1)).take 3).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hs : At s (pageRefreshPc site - 2) (recurringPageStoreInput l site slot page row ++ F))
    {o : Option TState} (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) o)
    (hSeen : PrefixDemand X g index (rowRefreshPc site) o) :
    X.get (g, index) =
      some ⟨pageRefreshPc site, .wr (pageRefreshAccess l g site false slot) (b32 page).toBytes⟩ ∧
    X.get (g, index + 1) = some ⟨rowRefreshPc site,
      .wr (pageRefreshAccess l g site true slot) (b32 (row % 16)).toBytes⟩ ∧
    ∃ t, At t (rowRefreshPc site + 1) F ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (index + 2)) o := by
  have hOrder : pageRefreshPc site ≤ rowRefreshPc site := by fin_cases site <;> decide
  exact recurringPageStoresObservedWithDemand hp site slot hRow hPageKeep hRowKeep hs hRun
    (hSeen.nonempty hRun) (fun _ he hr => (hSeen.advance he hOrder).nonempty hr)

end
end PTX.Kernels.TmlFa4Fwd.Loader
