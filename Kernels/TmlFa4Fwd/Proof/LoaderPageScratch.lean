-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEntry
public import Kernels.TmlFa4Fwd.Proof.PagedKvGeometry
public import Kernels.TmlFa4Fwd.Proof.EpilogueLocalRun
public import Kernels.TmlFa4Fwd.Flow.Code.Part007

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The address of a valid page-table word of the selected request. -/
def pageWordAddress (p : Params) (batch pageIndex : Nat) : Nat :=
  p.pageTableBase + 4 * (batch * p.pageTableStride + pageIndex)

private theorem pageAddressBound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b index : Nat} (hb : b < p.batch) (hi : index < (p.kLength b + 15) / 16) :
    pageWordAddress p b index + 4 ≤ 2 ^ 64 := by
  have hStride := (hp.pageTable b hb).1
  have hRange := hp.ranges ⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩
    (by simp [Params.inputRegions])
  change p.pageTableBase + 4 * p.batch * p.pageTableStride ≤ 2 ^ 64 at hRange
  have hBatch := Nat.mul_le_mul_right p.pageTableStride (show b + 1 ≤ p.batch by omega)
  rw [Nat.add_mul, Nat.one_mul] at hBatch
  rw [Nat.mul_assoc] at hRange
  unfold pageWordAddress
  omega

theorem pageReadAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g b index : Nat} (hb : b < p.batch) (hi : index < (p.kLength b + 15) / 16) :
    Seg kernel [] l g 2 501 [(1097, b32 index),
      (7299, b64 (p.pageTableBase + 4 * (b * p.pageTableStride)))] 503
      [(7531, b64 (pageWordAddress p b index))] := by
  intro t ht
  have hKey := (hp.lengths b hb).2.2
  have h31 : index < 2 ^ 31 := by omega
  have h32 : index < 2 ^ 32 := by omega
  have hBound := pageAddressBound hp hb hi
  have hBase : p.pageTableBase + 4 * (b * p.pageTableStride) < 2 ^ 64 := by
    dsimp [pageWordAddress] at hBound; omega
  have hOff : 4 * index < 2 ^ 64 := by dsimp [pageWordAddress] at hBound; omega
  have hAddress : pageWordAddress p b index < 2 ^ 64 := by omega
  have hSigned : toSigned 32 (BitVec.ofNat 64 index) = (index : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show index < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt h32, ite_eq_left h31]
  have hI4 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hMul : (index : Int) * 4 = ((4 * index : Nat) : Int) := by push_cast; omega
  have hAdd : p.pageTableBase + 4 * (b * p.pageTableStride) + 4 * index =
      pageWordAddress p b index := by simp [pageWordAddress, Nat.mul_add, Nat.add_assoc]
  seg_fp ht using simp only [b64, kind_s_beq_s, ↓reduceIte, hI4, hSigned,
    truncBits_ofNat h32 (by decide), truncBits_ofNat hOff (by decide),
    truncBits_ofNat hBase (by decide), hMul, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    hAdd, truncBits_ofNat hAddress (by decide)]

theorem pageReadTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g b index : Nat} (hb : b < p.batch) (hi : index < (p.kLength b + 15) / 16) {t : TState}
    (ht : At t 503 [(7531, b64 (pageWordAddress p b index))]) :
    out kernel Assumptions.all l g t = .ev (.read
      {loc := globalLoc (pageWordAddress p b index), size := 4} (afterLoad t [7173])) := by
  have hBound := pageAddressBound hp hb hi
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.2.2.1
  have hAddr : pageWordAddress p b index % 4 = 0 := by dsimp [pageWordAddress]; omega
  rw [loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_503) rfl rfl]
  change Out.ev (loadTmpl [] l g t .global false 32 [7173] 7531 0) = _
  exact congrArg Out.ev (loadTmpl_global ht.2.1 ht.2.2.2.2.1 (by omega) (by decide) hAddr)

theorem pageScratchAddress {l : Launch} {g : Nat} (entry : Fin 2)
    (hLocal : l.localBase + 128 ≤ 2 ^ 32) :
    Seg kernel [] l g 2 504 [(7172, b32 entry.val), (7295, b64 (l.localBase + 96))] 506
      [(7533, b64 (l.localBase + kvLocalOffset 3 entry)), (7532, b64 (entry.val * 4))] := by
  intro t ht
  have hEntry : entry.val < 2 ^ 32 := by have := entry.isLt; omega
  have hOffset : entry.val * 4 < 2 ^ 64 := by have := entry.isLt; omega
  have hBase : l.localBase + 96 < 2 ^ 64 := by omega
  have hSum : l.localBase + (96 + entry.val * 4) < 2 ^ 64 := by have := entry.isLt; omega
  have hEntry64 : entry.val < 2 ^ 64 := by omega
  have hI4 : (truncBits 32 (BitVec.ofInt 64 4)).toNat = 4 := rfl
  have hLocalOff : kvLocalOffset 3 entry = 96 + entry.val * 4 := by
    change 96 + 4 * entry.val = 96 + entry.val * 4
    rw [Nat.mul_comm]
  seg_fp ht using simp only [b64, kind_u_beq_s, Bool.false_eq_true, ↓reduceIte,
    toNat_ofNat_lt hEntry64, hI4, truncBits_ofNat hEntry (by decide),
    truncBits_ofNat hOffset (by decide), truncBits_ofNat hBase (by decide), ← BitVec.ofNat_add,
    truncBits_ofNat hSum (by decide), hLocalOff, Nat.add_assoc]

theorem pageScratchTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g page : Nat} (entry : Fin 2) {t : TState}
    (ht : At t 506 [(7533, b64 (l.localBase + kvLocalOffset 3 entry)), (7173, b32 page)]) :
    out kernel Assumptions.all l g t = .ev (.write
      {loc := ⟨.local, g, l.localBase + kvLocalOffset 3 entry⟩, size := 4}
      (b32 page).toBytes (next t)) := by
  have hBound := hp.localMemory.2.1
  have hLocal : l.localBase + kvLocalOffset 3 entry < 2 ^ 64 := by
    have hOffset : kvLocalOffset 3 entry < 128 :=
      kvLocalOffset_bound 3 entry (byte := 0) (by decide)
    omega
  have hAlign : (l.localBase + kvLocalOffset 3 entry) % 4 = 0 :=
    kvLocalOffset_aligned 3 entry hp.localMemory.1
  have hVal := ht.2.2.2.2.2.1
  have hAddr := ht.2.2.2.2.1
  rw [loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_506) rfl rfl]
  change Out.ev (accessTmpl [] l g t {
    kind := .store, space := some .local, sem := .weak, elem := .int .b 32,
    addr := ⟨.reg 7533 64, 0⟩, srcs := [.reg 7173] }) = _
  simp [accessTmpl, accessAcc, accessLoc, elemAcc, wrapAddr, readBits, readValue, readReg, hAddr,
    hVal, hAlign, ht.2.1, b64, storeValue_of_bytes (show (b32 page).bytes = 32 / 8 from rfl),
    next, afterStore, Loc.at, MemAccess.strongLocOk, MemAccess.semAcc, CacheHints.globalOnly,
    DType.width, truncBits_ofNat hLocal (by decide), toNat_ofNat_lt hLocal,
    bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

end
end PTX.Kernels.TmlFa4Fwd.Loader
