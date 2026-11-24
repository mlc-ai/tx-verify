-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPointerReload
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The four recurring writes of a computed K/V page pointer into lane scratch. -/
def pointerSavePc : Fin 4 → Nat
  | 0 => 977
  | 1 => 1223
  | 2 => 1447
  | 3 => 1628

def pointerSaveRegs : Fin 4 → Nat × Nat
  | 0 => (7664, 7662)
  | 1 => (7718, 7716)
  | 2 => (7779, 7777)
  | 3 => (7823, 7821)

def pointerSaveAddress (l : Launch) (i : Fin 4) (slot : Fin 2) : Nat :=
  pointerReloadAddress l i + 8 * slot.val

def pointerSaveAccess (l : Launch) (g : Nat) (i : Fin 4) (slot : Fin 2) : Acc :=
  {loc := ⟨.local, g, pointerSaveAddress l i slot⟩, size := 8}

def pointerSaveFacts (l : Launch) (i : Fin 4) (slot : Fin 2) (base : Nat) : List (Nat × Value) :=
  [((pointerSaveRegs i).1, b64 (pointerSaveAddress l i slot)),
   ((pointerSaveRegs i).2, b64 base)]

private def pointerSaveMem (i : Fin 4) : MemAccess :=
  {kind := .store, space := some .local, sem := .weak, elem := .int .b 64,
   addr := ⟨.reg (pointerSaveRegs i).1 64, 0⟩, srcs := [.reg (pointerSaveRegs i).2]}

private theorem pointerSaveCode (i : Fin 4) :
    kernel.code[pointerSavePc i]? = some ⟨none, .mem (pointerSaveMem i)⟩ := by
  fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem pointerSaveTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g base : Nat} (i : Fin 4) (slot : Fin 2) {s : TState}
    (hs : At s (pointerSavePc i) (pointerSaveFacts l i slot base)) :
    out kernel Assumptions.all l g s =
      .ev (.write (pointerSaveAccess l g i slot) (b64 base).toBytes (next s)) := by
  let addr := pointerSaveAddress l i slot
  have hSlot := slot.isLt
  have hBound : addr < 2 ^ 64 := by
    have hSize := hp.localMemory.2.1
    unfold addr pointerSaveAddress pointerReloadAddress
    split <;> omega
  have ha : addr % 8 = 0 := by
    have hAligned := hp.localMemory.1
    unfold addr pointerSaveAddress pointerReloadAddress
    split <;> omega
  have hDst : s.regs (pointerSaveRegs i).1 = some (b64 addr) := hs.2.2.2.2.1
  have hSrc : s.regs (pointerSaveRegs i).2 = some (b64 base) := hs.2.2.2.2.2.1
  have hb : readBits l g s 64 (.reg (pointerSaveRegs i).1) = .ok (BitVec.ofNat 64 addr) :=
    readBits_b64 hDst hBound
  have hLoc : accessLoc l g s (pointerSaveMem i) = .ok (pointerSaveAccess l g i slot).loc := by
    have hZero : BitVec.ofInt 64 0 = 0#64 := rfl
    simp only [accessLoc, pointerSaveMem, hb, bind, Except.bind, wrapAddr, hZero, BitVec.add_zero,
      truncBits_ofNat hBound (by decide), toNat_ofNat_lt hBound, pure, Except.pure,
      pointerSaveAccess]
    rfl
  have hAccess : accessAcc l g s (pointerSaveMem i) = .ok (pointerSaveAccess l g i slot) := by
    rw [accessAcc_of_weak (a := pointerSaveMem i) rfl, hLoc]
    simp [pointerSaveMem, CacheHints.globalOnly, DType.width, hs.2.1, bind, Except.bind,
      elemAcc, ha, addr, pointerSaveAccess, Loc.at, pure, Except.pure]
  have hLo : 174 ≤ s.pc := by rw [hs.1]; fin_cases i <;> decide
  have hHi : s.pc < 1906 := by rw [hs.1]; fin_cases i <;> decide
  rw [loaderOutCore hLo hHi, out_event hs.2.2.2.1 (by rw [hs.1]; exact pointerSaveCode i) rfl rfl]
  change Out.ev (memTmpl [] l g s (pointerSaveMem i)) = _
  have hRule : (pointerSaveMem i).rule = some .threadAccess := rfl
  have hSpace : (pointerSaveMem i).locSpace? = none := rfl
  simp only [memTmpl, hRule, hSpace, ↓reduceIte, accessTmpl, hAccess]
  change Out.ev (match [Opnd.reg (pointerSaveRegs i).2][s.sub]? with
    | none => .ub .typeMismatch
    | some source => match readValue l g s 64 source >>= storeValue 64 with
      | .error f => .ub f
      | .ok v => .write (pointerSaveAccess l g i slot) v.toBytes
          (afterStore s [Opnd.reg (pointerSaveRegs i).2])) = _
  simp [hs.2.1, readValue, readReg, hSrc, storeValue, Value.bytes, b64, bind, Except.bind,
    pure, Except.pure, afterStore, next, hs.2.2.1]

/-- The decoded pointer save emits an eight-byte write owned by its issuing lane. -/
theorem pointerSaveObservedInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g index base : Nat} (i : Fin 4) (slot : Fin 2) {s : TState}
    (hs : At s (pointerSavePc i) (pointerSaveFacts l i slot base))
    {ending : Option TState}
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hMore : (X.tr g).drop index ≠ []) :
    X.get (g, index) = some ⟨pointerSavePc i,
      .wr (pointerSaveAccess l g i slot) (b64 base).toBytes⟩ ∧
    At (next s) (pointerSavePc i + 1) (pointerSaveFacts l i slot base) ∧
    Run kernel Assumptions.all l g (next s) ((X.tr g).drop (index + 1)) ending := by
  have hNext : Next kernel Assumptions.all l g s s
      (.write (pointerSaveAccess l g i slot) (b64 base).toBytes (next s)) :=
    ⟨.refl, pointerSaveTemplate hp i slot hs⟩
  obtain ⟨_, _, hEvent, ⟨rfl, hState⟩, hRest⟩ := hNext.continuing_at_nonempty (by
    rintro ev ⟨_, hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hState
  exact ⟨by simpa only [hs.1] using hEvent, hs.next, hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
