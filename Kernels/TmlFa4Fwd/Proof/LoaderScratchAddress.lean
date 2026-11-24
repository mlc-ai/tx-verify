-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderScratchRows
public import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

structure SourceScratchSite where
  pc : Nat
  page : Nat
  row : Nat
  pageStride : Nat
  rowStride : Nat
  headBase : Nat
  index : Nat
  slot : Nat
  source : Nat

/-- K and V share the decoded arithmetic, with independent layout and scratch registers. -/
def sourceScratchSite : Fin 2 → SourceScratchSite
  | 0 => ⟨528, 7537, 7539, 7495, 7493, 7300, 9535, 7545, 7543⟩
  | 1 => ⟨793, 7601, 7603, 7499, 7497, 7301, 9536, 7609, 7607⟩

def sourceScratchAccess (l : Launch) (g : Nat) (entry : Fin 2) : Acc :=
  {loc := ⟨.local, g, l.localBase + kvLocalOffset 0 entry⟩, size := 8}

def sourceScratchInputs (l : Launch) (site : Fin 2) (entry : Fin 2)
    (page row pageStride rowStride headBase : Nat) : List (Nat × Value) :=
  let s := sourceScratchSite site
  [(s.page, b64 page), (s.row, b64 row), (s.pageStride, b64 pageStride),
   (s.rowStride, b64 rowStride), (s.headBase, b64 headBase),
   (s.index, b64 entry.val), (7292, b64 l.localBase)]

def sourceScratchPayload (page row pageStride rowStride headBase : Nat) : Nat :=
  headBase + 2 * (page * pageStride + row * rowStride)

/-- The decoded local instructions form the selected page and in-page row's byte
address, then reach the lane's eight-byte source-address scratch store. -/
theorem sourceScratchAddress {l : Launch} {g page row ps rs base : Nat}
    (site : Fin 2) (entry : Fin 2) (hStack : l.localBase + 128 ≤ 2 ^ 32)
    (hPage : page < 2 ^ 64) (hRow : row < 2 ^ 64) (hPS : ps < 2 ^ 64) (hRS : rs < 2 ^ 64)
    (hFit : sourceScratchPayload page row ps rs base < 2 ^ 64) :
    Seg kernel [] l g 6 (sourceScratchSite site).pc
      (sourceScratchInputs l site entry page row ps rs base) ((sourceScratchSite site).pc + 6)
      [((sourceScratchSite site).slot, b64 (l.localBase + kvLocalOffset 0 entry)),
       ((sourceScratchSite site).source, b64 (sourceScratchPayload page row ps rs base))] := by
  have hTotal : base + 2 * (page * ps + row * rs) < 2 ^ 64 := hFit
  have hBase : base < 2 ^ 64 := by omega
  have hPProd : page * ps < 2 ^ 64 := by omega
  have hJoin : page * ps + row * rs < 2 ^ 64 := by omega
  have hTwice : 2 * (page * ps + row * rs) < 2 ^ 64 := by omega
  have hPageMul : ps * page = page * ps := Nat.mul_comm ..
  have hRowMul : rs * row = row * rs := Nat.mul_comm ..
  have hFour : (truncBits 32 (BitVec.ofInt 64 1)).toNat = 1 := rfl
  have hEight : (truncBits 32 (BitVec.ofInt 64 3)).toNat = 3 := rfl
  have hShift : BitVec.ofNat 64 (page * ps + row * rs) <<< 1 =
      BitVec.ofNat 64 (2 * (page * ps + row * rs)) := by
    rw [nf_shl, Nat.mul_comm]
    rfl
  have hShiftEntry : BitVec.ofNat 64 entry.val <<< 3 = BitVec.ofNat 64 (8 * entry.val) := by
    rw [nf_shl, Nat.mul_comm]
    rfl
  have hEntry : entry.val < 2 ^ 64 := by omega
  have hOff : 8 * entry.val < 2 ^ 64 := by omega
  have hLocal : l.localBase < 2 ^ 64 := by omega
  have hLoc : l.localBase + 8 * entry.val < 2 ^ 64 := by omega
  have hEntryOff : kvLocalOffset 0 entry = 8 * entry.val := by simp [kvLocalOffset]
  fin_cases site <;> intro t ht <;> simp only [sourceScratchInputs, sourceScratchSite] at ht ⊢ <;>
    seg_fp ht using
      simp only [b64, hFour, hEight, show ¬1 ≥ 64 by decide, show ¬3 ≥ 64 by decide,
        ↓reduceIte, hShiftEntry, hEntryOff, truncBits_ofNat hEntry (by decide),
        truncBits_ofNat hOff (by decide), truncBits_ofNat hLocal (by decide),
        truncBits_ofNat hLoc (by decide), ← BitVec.ofNat_add,
        truncBits_ofNat hBase (by decide), truncBits_ofNat hPage (by decide),
        truncBits_ofNat hRow (by decide), truncBits_ofNat hPS (by decide),
        truncBits_ofNat hRS (by decide), ← BitVec.ofNat_mul, hPageMul, hRowMul,
        truncBits_ofNat hPProd (by decide),
        truncBits_ofNat hJoin (by decide), hShift, truncBits_ofNat hTwice (by decide),
        truncBits_ofNat hTotal (by decide), sourceScratchPayload, Nat.add_comm]

private theorem sourceStoreCode (site : Fin 2) :
    kernel.code[(sourceScratchSite site).pc + 6]? = some ⟨none, .mem
      { kind := .store, space := some .local, sem := .weak, elem := .int .b 64,
        addr := ⟨.reg (sourceScratchSite site).slot 64, 0⟩,
        srcs := [.reg (sourceScratchSite site).source] }⟩ := by
  fin_cases site
  · exact Flow.code_534
  · exact Flow.code_799

private theorem sourceStoreTemplate {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g address : Nat} (site : Fin 2) (entry : Fin 2) {t : TState}
    (ht : At t ((sourceScratchSite site).pc + 6)
      [((sourceScratchSite site).slot, b64 (l.localBase + kvLocalOffset 0 entry)),
       ((sourceScratchSite site).source, b64 address)]) :
    out kernel Assumptions.all l g t = .ev
      (.write (sourceScratchAccess l g entry) (b64 address).toBytes (next t)) := by
  have hLocal : l.localBase + kvLocalOffset 0 entry < 2 ^ 64 := by
    have hBound := hp.localMemory.2.1
    have hOff := kvLocalOffset_bound 0 entry (byte := 0) (by decide)
    omega
  have hAlign : (l.localBase + kvLocalOffset 0 entry) % 8 = 0 :=
    kvLocalOffset_aligned 0 entry hp.localMemory.1
  have hPc : 174 ≤ (sourceScratchSite site).pc + 6 ∧
      (sourceScratchSite site).pc + 6 < 1906 := by fin_cases site <;> decide
  have hAddr := ht.2.2.2.2.1
  have hVal := ht.2.2.2.2.2.1
  rw [loaderOutCore (by rw [ht.1]; exact hPc.1) (by rw [ht.1]; exact hPc.2)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact sourceStoreCode site) rfl rfl]
  change Out.ev (accessTmpl [] l g t {
    kind := .store, space := some .local, sem := .weak, elem := .int .b 64,
    addr := ⟨.reg (sourceScratchSite site).slot 64, 0⟩,
    srcs := [.reg (sourceScratchSite site).source] }) = _
  simp [accessTmpl, accessAcc, accessLoc, elemAcc, wrapAddr, readBits, readValue, readReg, hAddr,
    hVal, hAlign, ht.2.1, b64, storeValue, Value.bytes,
    next, afterStore, Loc.at, MemAccess.strongLocOk, MemAccess.semAcc, CacheHints.globalOnly,
    DType.width, truncBits_ofNat hLocal (by decide), toNat_ofNat_lt hLocal,
    bind, Except.bind, Functor.map, Except.map, pure, Except.pure, sourceScratchAccess]

variable {p : Params} {l : Launch} {m : Mem0}

/-- Prepare the K or V pointer save and retain the decoded register frame. -/
theorem sourceScratchStoreNext (hp : Pre p l m) {g page row ps rs base : Nat} (site : Fin 2)
    (entry : Fin 2) (hPage : page < 2 ^ 64) (hRow : row < 2 ^ 64) (hPS : ps < 2 ^ 64)
    (hRS : rs < 2 ^ 64) (hFit : sourceScratchPayload page row ps rs base < 2 ^ 64) {t : TState}
    {F : List (Nat × Value)}
    (hf : ((kernel.code.drop (sourceScratchSite site).pc).take 6).all
      (fun ins => (F.map Prod.fst).all (fun reg => !(writesRegs ins.op).contains reg)) = true)
    (ht : At t (sourceScratchSite site).pc
      (sourceScratchInputs l site entry page row ps rs base ++ F)) :
    let address := sourceScratchPayload page row ps rs base
    ∃ v, v.pc = (sourceScratchSite site).pc + 6 ∧
      At (next v) ((sourceScratchSite site).pc + 7)
        (((sourceScratchSite site).source, b64 address) :: F) ∧
      Next kernel Assumptions.all l g t v
        (.write (sourceScratchAccess l g entry) (b64 address).toBytes (next v)) := by
  dsimp only
  obtain ⟨v, hv, hV⟩ := sourceScratchAddress site entry hp.localMemory.2.1 hPage hRow hPS hRS
    hFit t (ht.mono ((holds_append ..).mp ht.2.2.2.2).1)
  have hLo : 174 ≤ (sourceScratchSite site).pc := by fin_cases site <;> decide
  have hHi : (sourceScratchSite site).pc + 6 ≤ 1906 := by fin_cases site <;> decide
  obtain ⟨hvA, hFrame⟩ := loaderLinear (regs := F.map Prod.fst) hLo hHi ht.1 hf
    (by fin_cases site <;> set_option maxRecDepth 100000 in kernel_rfl) hv
  let word := b64 (sourceScratchPayload page row ps rs base)
  have hn : Next kernel Assumptions.all l g t v
      (.write (sourceScratchAccess l g entry) word.toBytes (next v)) :=
    ⟨run_rtg hvA, sourceStoreTemplate hp site entry hV⟩
  have hKeep := Epilogue.holdsSchedulerFrame ((holds_append ..).mp ht.2.2.2.2).2 hFrame
    (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨v,hV.1,hV.next.mono ⟨hV.2.2.2.2.2.1,hKeep⟩,hn⟩

section
variable {X : Execution} (hp : Pre p l m) {g i page row ps rs base : Nat} (site : Fin 2)
    (entry : Fin 2) (hPage : page < 2 ^ 64) (hRow : row < 2 ^ 64) (hPS : ps < 2 ^ 64)
    (hRS : rs < 2 ^ 64) (hFit : sourceScratchPayload page row ps rs base < 2 ^ 64) {t : TState}
    {F : List (Nat × Value)}
    (hf : ((kernel.code.drop (sourceScratchSite site).pc).take 6).all
      (fun ins => (F.map Prod.fst).all (fun reg => !(writesRegs ins.op).contains reg)) = true)
    (ht : At t (sourceScratchSite site).pc
      (sourceScratchInputs l site entry page row ps rs base ++ F))
include hp site entry hPage hRow hPS hRS hFit hf ht

/-- The packed source-address scratch slot is written by the decoded K or V preparatory
iteration and the witnessed write is followed by the actual loader continuation. -/
theorem sourceScratchObservedFrameInPrefix {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending) (hMore : (X.tr g).drop i ≠ [])
    :
    let address := sourceScratchPayload page row ps rs base
    ∃ u, X.get (g, i) = some ⟨(sourceScratchSite site).pc + 6,
        .wr (sourceScratchAccess l g entry) (b64 address).toBytes⟩ ∧
      At u ((sourceScratchSite site).pc + 7)
        (((sourceScratchSite site).source, b64 address) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) ending := by
  dsimp only
  obtain ⟨v,hPc,hV,hn⟩ := sourceScratchStoreNext (g := g) hp site entry hPage hRow hPS hRS
    hFit hf ht
  obtain ⟨_, _, he, ⟨rfl, hu⟩, hTail⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hu
  exact ⟨_,by simpa only [hPc] using he,hV,hTail⟩

end

/-- A stored source address with a live row is the zero-column physical cache address. -/
theorem sourceScratchPayload_live (hp : Pre p l m) (site : Fin 2) {page row head : Nat}
    (hPage : page < p.pages) (hRow : row < 16) (hHead : head < p.kvHeads) :
    let layout := if site.val = 0 then p.kLayout else p.vLayout
    let headBase := layout.base + 2 * (head * layout.headStride)
    let src := sourceScratchPayload page row layout.pageStride layout.rowStride headBase
    src = (layout.loc page head row 0).addr ∧ src < 2 ^ 64 ∧ src % 16 = 0 := by
  dsimp only
  let layout := if site.val = 0 then p.kLayout else p.vLayout
  let headBase := layout.base + 2 * (head * layout.headStride)
  let src := sourceScratchPayload page row layout.pageStride layout.rowStride headBase
  have hEq : src = (layout.loc page head row 0).addr := by
    simp [src, headBase, sourceScratchPayload, CacheLayout.loc, globalLoc]
    omega
  refine ⟨hEq, ?_, ?_⟩
  · have hRegion := CacheLayout.loc_copy_in_region (c := layout) hPage hHead hRow
      (d := 0) (byte := 0) (by decide)
    have hMem : layout.region p.pages p.kvHeads ∈ p.inputRegions := by
      fin_cases site <;> simp [layout, Params.inputRegions]
    have hRange := hp.ranges (layout.region p.pages p.kvHeads) (by simp [hMem])
    change src < 2 ^ 64
    rw [hEq]
    have hAddr := hRegion.2.2.2
    change (layout.loc page head row 0).addr <
        (layout.region p.pages p.kvHeads).base + (layout.region p.pages p.kvHeads).bytes at hAddr
    omega
  · change src % 16 = 0
    rw [hEq]
    fin_cases site
    · exact CacheLayout.loc_aligned hp.alignment.1 hp.alignment.2.2.2.2.1
        hp.alignment.2.2.2.1 hp.alignment.2.2.1 (by decide)
    · exact CacheLayout.loc_aligned hp.alignment.2.1 hp.alignment.2.2.2.2.2.2.2.1
        hp.alignment.2.2.2.2.2.2.1 hp.alignment.2.2.2.2.2.1 (by decide)

end
end PTX.Kernels.TmlFa4Fwd.Loader
