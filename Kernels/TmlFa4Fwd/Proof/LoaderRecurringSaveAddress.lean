-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPointerStore
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchAddress
public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixDemand

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

structure RecurringSaveInputs where
  page : Nat
  row : Nat
  pageStride : Nat
  rowStride : Nat
  headBase : Nat
  slot : Nat

/-- The recurring K and V pointer saves read their separate decoded register fields. -/
def recurringSaveInputs : Fin 4 → RecurringSaveInputs
  | 0 => ⟨7656, 7658, 7495, 7493, 7300, 9537⟩
  | 1 => ⟨7710, 7712, 7499, 7497, 7301, 9538⟩
  | 2 => ⟨7771, 7773, 7495, 7493, 7300, 9539⟩
  | 3 => ⟨7815, 7817, 7499, 7497, 7301, 9540⟩

def recurringSaveAddressPc (i : Fin 4) : Nat := pointerSavePc i - 6

def recurringSaveAddressFacts (l : Launch) (i : Fin 4) (slot : Fin 2)
    (page row ps rs headBase : Nat) : List (Nat × Value) :=
  let input := recurringSaveInputs i
  [(input.page, b64 page), (input.row, b64 row), (input.pageStride, b64 ps),
   (input.rowStride, b64 rs), (input.headBase, b64 headBase), (input.slot, b64 slot.val),
   (pointerReloadBase i, b64 (pointerReloadAddress l i))]

private theorem recurringAddressCore {l : Launch} {g page row ps rs base : Nat}
    (i : Fin 4) (slot : Fin 2) (hStack : l.localBase + 128 ≤ 2 ^ 32)
    (hPage : page < 2 ^ 64) (hRow : row < 2 ^ 64) (hPS : ps < 2 ^ 64) (hRS : rs < 2 ^ 64)
    (hFit : sourceScratchPayload page row ps rs base < 2 ^ 64) :
    Seg kernel [] l g 6 (recurringSaveAddressPc i)
      (recurringSaveAddressFacts l i slot page row ps rs base) (pointerSavePc i)
      (pointerSaveFacts l i slot (sourceScratchPayload page row ps rs base)) := by
  have hTotal : base + 2 * (page * ps + row * rs) < 2 ^ 64 := hFit
  have hBase : base < 2 ^ 64 := by omega
  have hPProd : page * ps < 2 ^ 64 := by omega
  have hJoin : page * ps + row * rs < 2 ^ 64 := by omega
  have hTwice : 2 * (page * ps + row * rs) < 2 ^ 64 := by omega
  have hPageMul : ps * page = page * ps := Nat.mul_comm ..
  have hRowMul : rs * row = row * rs := Nat.mul_comm ..
  have hOne : (truncBits 32 (BitVec.ofInt 64 1)).toNat = 1 := rfl
  have hThree : (truncBits 32 (BitVec.ofInt 64 3)).toNat = 3 := rfl
  have hShift : BitVec.ofNat 64 (page * ps + row * rs) <<< 1 =
      BitVec.ofNat 64 (2 * (page * ps + row * rs)) := by
    rw [nf_shl, Nat.mul_comm]
    rfl
  have hShiftSlot : BitVec.ofNat 64 slot.val <<< 3 = BitVec.ofNat 64 (8 * slot.val) := by
    rw [nf_shl, Nat.mul_comm]
    rfl
  have hSlot : slot.val < 2 ^ 64 := by omega
  have hOff : 8 * slot.val < 2 ^ 64 := by omega
  have hLocal : pointerReloadAddress l i < 2 ^ 64 := by
    unfold pointerReloadAddress
    split <;> omega
  have hLoc : 8 * slot.val + pointerReloadAddress l i < 2 ^ 64 := by
    have hSlot := slot.isLt
    unfold pointerReloadAddress
    split <;> omega
  fin_cases i <;> intro s hs <;>
    simp only [recurringSaveAddressFacts, recurringSaveInputs, recurringSaveAddressPc,
      pointerSavePc, pointerSaveFacts, pointerSaveRegs, pointerReloadBase] at hs ⊢ <;>
    seg_fp hs using
      simp only [b64, hOne, hThree, show ¬1 ≥ 64 by decide, show ¬3 ≥ 64 by decide,
        ↓reduceIte, hShiftSlot, truncBits_ofNat hSlot (by decide),
        truncBits_ofNat hOff (by decide), truncBits_ofNat hLocal (by decide),
        truncBits_ofNat hLoc (by decide), ← BitVec.ofNat_add,
        truncBits_ofNat hBase (by decide), truncBits_ofNat hPage (by decide),
        truncBits_ofNat hRow (by decide), truncBits_ofNat hPS (by decide),
        truncBits_ofNat hRS (by decide), ← BitVec.ofNat_mul, hPageMul, hRowMul,
        truncBits_ofNat hPProd (by decide), truncBits_ofNat hJoin (by decide), hShift,
        truncBits_ofNat hTwice (by decide), truncBits_ofNat hTotal (by decide),
        sourceScratchPayload, pointerSaveAddress, Nat.add_comm]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g index page row ps rs base : Nat} (i : Fin 4) (slot : Fin 2) (hPage : page < 2 ^ 64)
    (hRow : row < 2 ^ 64) (hPS : ps < 2 ^ 64) (hRS : rs < 2 ^ 64)
    (hFit : sourceScratchPayload page row ps rs base < 2 ^ 64)
include hp i slot hPage hRow hPS hRS hFit

/-- The recurring address calculation reaches the actual lane scratch write,
using the verified physical page, row stride and head base. -/
theorem recurringAddressSaveObservedWithFrame {s : TState} {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop (recurringSaveAddressPc i)).take 6).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s (recurringSaveAddressPc i)
      (recurringSaveAddressFacts l i slot page row ps rs base ++ F)) {ending : Option TState}
    (hw : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index (pointerSavePc i) ending) :
    X.get (g, index) = some ⟨pointerSavePc i,
      .wr (pointerSaveAccess l g i slot) (b64 (sourceScratchPayload page row ps rs base)).toBytes⟩ ∧
    ∃ u, At u (pointerSavePc i + 1) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 1)) ending := by
  have ⟨hCore, hF⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨t, ht, hT⟩ := recurringAddressCore (g := g) i slot hp.localMemory.2.1 hPage hRow hPS hRS
    hFit s (hs.mono hCore)
  have hLo : 174 ≤ recurringSaveAddressPc i := by fin_cases i <;> decide
  have hHi : recurringSaveAddressPc i + 6 ≤ 1906 := by fin_cases i <;> decide
  have hSeq : ((kernel.code.drop (recurringSaveAddressPc i)).take 5).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hRun, hFrame⟩ := loaderLinear (regs := F.map Prod.fst) hLo hHi hs.1 hKeep hSeq ht
  have hMore := hDemand.nonempty hw
  obtain ⟨he, hU, hTail⟩ := pointerSaveObservedInPrefix hp i slot hT
    (hw.after_local_nonempty (run_rtg hRun) hMore) hMore
  have hKeep := Epilogue.holdsSchedulerFrame hF hFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨he, _, hU.mono (show Holds (next t).regs F from hKeep), hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
