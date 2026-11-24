-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPageScratch
public import Kernels.TmlFa4Fwd.Flow.Code.Part007

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The row-in-page field uses a separate four-byte scratch word. -/
def rowScratchAccess (l : Launch) (g : Nat) (entry : Fin 2) : Acc :=
  {loc := ⟨.local, g, l.localBase + kvLocalOffset 2 entry⟩, size := 4}

theorem scratchRowSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (entry : Fin 2) {row : Nat} (hRow : row < 2 ^ 31) :
    Seg kernel [] l g 4 507
      [(7294, b64 (l.localBase + 64)), (7532, b64 (4 * entry.val)),
        (7296, b64 16), (1096, b32 row), (1097, b32 (row / 16))]
      511 [(7534, b64 (l.localBase + kvLocalOffset 2 entry)), (1847, b32 (row % 16))] := by
  have hBase := hp.localMemory.2.1
  have hAddr : l.localBase + 64 + 4 * entry.val < 2 ^ 64 := by
    have hn := entry.isLt
    omega
  have hShift : kvLocalOffset 2 entry = 64 + 4 * entry.val := by
    simp [kvLocalOffset]
  have hOff : 4 * entry.val < 2 ^ 64 := by have := entry.isLt; omega
  have hb : l.localBase + 64 < 2 ^ 64 := by omega
  intro t ht
  seg_fp ht using norm_bits [hShift, Nat.add_assoc, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hOff,
    Nat.mod_eq_of_lt hAddr]

theorem scratchRowStoreTemplate {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g n : Nat} (entry : Fin 2) {t : TState}
    (ht : At t 511 [(7534, b64 (l.localBase + kvLocalOffset 2 entry)), (1847, b32 n)]) :
    out kernel Assumptions.all l g t = .ev
      (.write (rowScratchAccess l g entry) (b32 n).toBytes (next t)) := by
  have hBound := hp.localMemory.2.1
  have hLocal : l.localBase + kvLocalOffset 2 entry < 2 ^ 64 := by
    have hOffset := kvLocalOffset_bound 2 entry (byte := 0) (by decide)
    omega
  have hAlign : (l.localBase + kvLocalOffset 2 entry) % 4 = 0 :=
    kvLocalOffset_aligned 2 entry hp.localMemory.1
  have hPtr := ht.2.2.2.2.1
  have hWord := ht.2.2.2.2.2.1
  rw [loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_511) rfl rfl]
  change Out.ev (accessTmpl [] l g t {
    kind := .store, space := some .local, sem := .weak, elem := .int .b 32,
    addr := ⟨.reg 7534 64, 0⟩, srcs := [.reg 1847] }) = _
  simp [accessTmpl, accessAcc, accessLoc, elemAcc, wrapAddr, readBits, readValue, readReg, hPtr,
    hWord, hAlign, ht.2.1, b64, storeValue_of_bytes (show (b32 n).bytes = 32 / 8 from rfl),
    next, afterStore, Loc.at, MemAccess.strongLocOk, MemAccess.semAcc, CacheHints.globalOnly,
    DType.width, truncBits_ofNat hLocal (by decide), toNat_ofNat_lt hLocal,
    bind, Except.bind, Functor.map, Except.map, pure, Except.pure, rowScratchAccess]

end
end PTX.Kernels.TmlFa4Fwd.Loader
