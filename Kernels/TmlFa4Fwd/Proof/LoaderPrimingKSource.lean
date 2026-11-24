-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderFirstCopyPrep
public import Kernels.TmlFa4Fwd.Proof.LoaderPointerRow
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def primingKSourceFrame (p : Params) (l : Launch)
    (batch tile warp lane : Nat) : List (Nat × Value) :=
  let tid := 32 * warp + lane
  [(1082, b32 (kvCopyColumn tid false)),
   (124, .pred (decide (kvCopyRow tile tid 0 < p.kLength batch))),
   (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),
   (1852, b32 ((p.kLength batch + 2 ^ 32 - kvCopyRow tile tid 0) % 2 ^ 32)),
   (7292, b64 l.localBase)]

/-- The first K pair starts with the packed pointer loaded by this lane. Its
siblings in the eight-lane subgroup can select it through the actual shuffles. -/
def primingKSourceInputs (p : Params) (l : Launch) (batch tile warp : Nat)
    (bases : Nat → Nat) (lane : Nat) : List (Nat × Value) :=
  [(1853, b32 (bases lane % 2 ^ 32)), (1854, b32 (bases lane / 2 ^ 32))] ++
    primingKSourceFrame p l batch tile warp lane

def primingKShflSrc (word : Fin 2) : Nat := 1853 + word.val
def primingKShflDst (word : Fin 2) : Nat := 1855 + word.val

/-- The two-word pointer broadcast uses an eight-lane subgroup of the full warp. -/
theorem primingPointerWordTemplate {l : Launch} {g value src dst select : Nat}
    {s : TState} (hBlock : l.block % 32 = 0) (hSelect : select < 8)
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906) (hClean : s.fault = none)
    (hCode : kernel.code[s.pc]? = some ⟨none, .warp {
      kind := .shfl .idx, ty := some (.int .b 32), dsts := [some dst],
      srcs := [.reg src, .imm select, .imm 6175], mask := some (.imm (-1)) }⟩)
    (hWord : s.regs src = some (b32 value)) :
    out kernel Assumptions.all l g s = .ev (.shfl .idx (b32 value) select 6175
      (fun v _ => next (setReg s dst v))) := by
  rw [loaderOutCore hLo hHi, out_event hClean hCode rfl rfl]
  change Out.ev (shflTmpl l g s .idx dst none (.reg src) (.imm select) (.imm 6175) (.imm (-1))) = _
  have hSelect32 : select < 2 ^ 32 := by omega
  have hSelect64 : select < 2 ^ 64 := by omega
  have hMask : (truncBits 32 18446744073709551615#64).toNat = 4294967295 := by decide
  have hMode : (truncBits 32 6175#64).toNat = 6175 := by decide
  simp [shflTmpl, readValue, readReg, hWord, Value.bytes, b32, readBits, pure, Except.pure,
    hBlock, hMask, hMode, BitVec.ofInt_natCast, truncBits_ofNat hSelect32 (by decide),
    toNat_ofNat_lt hSelect64]

theorem primingKShuffleTemplate {l : Launch} {g value : Nat} (hBlock : l.block % 32 = 0)
    (word : Fin 2) {s : TState} {F : List (Nat × Value)}
    (hs : At s (544 + word.val) F)
    (hWord : s.regs (primingKShflSrc word) = some (b32 value)) :
    out kernel Assumptions.all l g s = .ev (.shfl .idx (b32 value) 0 6175
      (fun v _ => next (setReg s (primingKShflDst word) v))) := by
  apply primingPointerWordTemplate hBlock (by decide) (by rw [hs.1]; omega)
    (by rw [hs.1]; have := word.isLt; omega) hs.2.2.2.1 _ hWord
  rw [hs.1]
  fin_cases word
  · exact Flow.code_544
  · exact Flow.code_545

variable {p : Params} {l : Launch} {m : Mem0}

theorem primingKCopySourceLoc (hp : Pre p l m) {page head row tid g bytes : Nat}
    (hPage : page < p.pages) (hh : head < p.kvHeads) (pair : Fin 16) (upper : Bool) :
    let base := (p.kLayout.loc page head (row % 16) 0).addr
    let src := (base + 2 * kvCopyColumn tid false) % 2 ^ 64
    (kCopySpec l g 0 tid src bytes pair upper).src.loc =
      p.kLayout.loc page head (row % 16) (kvCopyColumn tid upper) := by
  dsimp only
  let base := (p.kLayout.loc page head (row % 16) 0).addr
  let col := kvCopyColumn tid upper
  let loc := p.kLayout.loc page head (row % 16) col
  have hCol : col < 128 := by
    have h := kvCopyColumn_byte_lt (lane := tid) upper (byte := 0) (by decide)
    change kvCopyColumn tid upper < 128
    omega
  have hMem := hp.ranges (p.kLayout.region p.pages p.kvHeads) (by simp [Params.inputRegions])
  have hRegion := CacheLayout.loc_copy_in_region (c := p.kLayout) hPage hh
    (Nat.mod_lt row (by decide : 0 < 16)) (d := col) (byte := 0) (by omega)
  have hAddr : loc.addr < 2 ^ 64 := by
    simpa [loc, Loc.at] using hRegion.2.2.2.trans_le hMem
  have hSum : base + 2 * kvCopyColumn tid false + (if upper then 128 else 0) = loc.addr := by
    cases upper <;> simp [base, loc, col, CacheLayout.loc, kvCopyColumn, globalLoc] <;> omega
  have hLower : base + 2 * kvCopyColumn tid false < 2 ^ 64 := by omega
  change globalLoc (((base + 2 * kvCopyColumn tid false) % 2 ^ 64 +
    (if upper then 128 else 0)) % 2 ^ 64) = loc
  rw [Nat.mod_eq_of_lt hLower, hSum, Nat.mod_eq_of_lt hAddr]
  rfl

/-- The saved first-slot K pointer for this lane, including the decoded
zero-page fallback of an out-of-range row. -/
def primingKRowPointer (p : Params) (batch head row : Nat) : Nat :=
  (p.kLayout.loc (primingScratchPage p batch row) head (row % 16) 0).addr

theorem primingScratchPageBound (hp : Pre p l m) {batch row : Nat} (hb : batch < p.batch) :
    primingScratchPage p batch row < p.pages := by
  simp only [primingScratchPage]
  split
  · exact ((hp.pageTable batch hb).2 (row / 16) (by omega)).1
  · exact hp.shape.2.2.2.1

/-- Prepare the actual packed K page pointer store, preserving the caller's frame. -/
theorem primingKRowPointerStoreNext (hp : Pre p l m) {g batch head row : Nat} (hb : batch < p.batch)
    (hh : head < p.kvHeads) (slot : Fin 2) {s : TState} {F : List (Nat × Value)}
    (hf : ((kernel.code.drop 528).take 6).all
      (fun ins => (F.map Prod.fst).all (fun reg => !(writesRegs ins.op).contains reg)) = true)
    (hs : At s 528 (sourceScratchInputs l 0 slot (primingScratchPage p batch row) (row % 16)
      p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base + 2 * (head * p.kLayout.headStride)) ++ F)) :
    ∃ v, v.pc = 534 ∧ At (next v) 535 ((7543,b64 (primingKRowPointer p batch head row)) :: F) ∧
      Next kernel Assumptions.all l g s v
        (.write (sourceScratchAccess l g slot) (b64 (primingKRowPointer p batch head row)).toBytes
          (next v)) := by
  let page := primingScratchPage p batch row
  have hPage := primingScratchPageBound hp (row := row) hb
  have hPageBits : page < 2 ^ 64 := by
    dsimp only [page]
    unfold primingScratchPage
    split
    · have h := ((hp.pageTable batch hb).2 (row / 16) (by omega)).2
      omega
    · decide
  have hRow : row % 16 < 16 := Nat.mod_lt _ (by decide)
  have hPS := (hp.objectBytes 1 40 8 p.kLayout.pageStride (by simp [Params.objectWords])).1
  have hRS := (hp.objectBytes 1 24 8 p.kLayout.rowStride (by simp [Params.objectWords])).1
  obtain ⟨hEq, hBound, _⟩ := sourceScratchPayload_live hp 0 hPage hRow hh
  change sourceScratchPayload page (row % 16) p.kLayout.pageStride p.kLayout.rowStride
    (p.kLayout.base + 2 * (head * p.kLayout.headStride)) =
      primingKRowPointer p batch head row at hEq
  obtain ⟨v,hPC,hV,hNext⟩ := sourceScratchStoreNext (g := g) hp
    (base := p.kLayout.base + 2 * (head * p.kLayout.headStride)) 0 slot hPageBits (by omega)
    hPS hRS hBound hf hs
  rw [hEq] at hV hNext
  exact ⟨v,hPC,hV,hNext⟩

section
variable {X : Execution} (hp : Pre p l m) {g index batch head row : Nat} (hb : batch < p.batch)
    (hh : head < p.kvHeads) (slot : Fin 2) {s : TState} {F : List (Nat × Value)}
    (hf : ((kernel.code.drop 528).take 6).all
      (fun ins => (F.map Prod.fst).all (fun reg => !(writesRegs ins.op).contains reg)) = true)
    (hs : At s 528 (sourceScratchInputs l 0 slot (primingScratchPage p batch row) (row % 16)
      p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base + 2 * (head * p.kLayout.headStride)) ++ F))
include hp hb hh slot hf hs

/-- Given the actual scratch reload values, the decoded K source preparation
stores the exact paged row pointer in the lane's selected pointer cell. -/
theorem primingKRowPointerSavedFrameInPrefix {ending : Option TState}
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hMore : (X.tr g).drop index ≠ []) :
    ∃ u, X.get (g, index) =
        some ⟨534, .wr (sourceScratchAccess l g slot)
          (b64 (primingKRowPointer p batch head row)).toBytes⟩ ∧
      At u 535 ((7543, b64 (primingKRowPointer p batch head row)) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 1)) ending := by
  obtain ⟨v,hPC,hV,hNext⟩ := primingKRowPointerStoreNext (g := g) hp hb hh slot hf hs
  obtain ⟨_,_,he,⟨rfl,hRet⟩,hTail⟩ := hNext.continuing_at_nonempty (by
    rintro _ ⟨_,hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hRet
  exact ⟨_,by simpa only [hPC] using he,hV,hTail⟩

end

/-- The register frame kept across the copy pairs of the first half of the priming K packet. -/
def primingKPacketFrame (p : Params) (l : Launch) (batch tile warp : Nat)
    (bases : Nat → Nat) (lane : Nat) : List (Nat × Value) :=
  (7547, b64 (2 * kvCopyColumn (32 * warp + lane) false)) ::
    primingKSourceInputs p l batch tile warp bases lane

end
end PTX.Kernels.TmlFa4Fwd.Loader
