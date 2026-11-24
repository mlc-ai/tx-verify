-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputGeometry
public import Kernels.TmlFa4Fwd.Proof.CorrectionEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Lemmas.Flow.LoadShared
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Each of the two passes writes eight four-element vectors in each of four output subboxes. -/
def outputStorePc (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8) : Nat :=
  8492 + 296 * stage.val +
    if subbox.val = 0 then 19 * (chunk.val / 2) + 4 * (chunk.val % 2)
    else 75 + 68 * (subbox.val - 1) + 17 * (chunk.val / 2) + 3 * (chunk.val % 2)

def outputStoreAddrReg (stage : Fin 2) (chunk : Fin 8) : Nat :=
  if chunk.val = 0 then if stage.val = 0 then 6511 else 6508
  else 6515 + 280 * stage.val + 19 * (chunk.val / 2) + 13 * (chunk.val % 2)

def outputStoreValueReg (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8)
    (element : Fin 4) : Nat :=
  6524 + 280 * stage.val +
    (if subbox.val = 0 then 19 * (chunk.val / 2) + 5 * (chunk.val % 2)
      else 75 + 68 * (subbox.val - 1) + 17 * (chunk.val / 2) + 4 * (chunk.val % 2)) +
    (element.val + 2) % 4

def outputOperands (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8) : List Opnd :=
  List.ofFn fun element => .reg (outputStoreValueReg stage subbox chunk element)

/-- The decoded weak shared vector store at a correction staging site. -/
def outputStoreInstr (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8) : Instr :=
  { guard := none
    op := .mem {
      kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := 4
      addr := ⟨.reg (outputStoreAddrReg stage chunk) 32, (16384 * subbox.val : Nat)⟩
      srcs := outputOperands stage subbox chunk } }

private def memoryForm : Option Instr → Option (Option (Nat × Bool) × MemAccess)
  | some ⟨guard, .mem access⟩ => some (guard, access)
  | _ => none

/-- The finite staging-site table agrees exactly with the decoded kernel. -/
theorem outputStoreCode (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8) :
    kernel.code[outputStorePc stage subbox chunk]? =
      some (outputStoreInstr stage subbox chunk) := by
  have hCheck : ∀ (s : Fin 2) (b : Fin 4) (c : Fin 8),
      memoryForm (kernel.code[outputStorePc s b c]?) =
        memoryForm (some (outputStoreInstr s b c)) := by decide +kernel
  have h := hCheck stage subbox chunk
  cases hs : kernel.code[outputStorePc stage subbox chunk]? with
  | none => cases (hs ▸ h)
  | some ins =>
    obtain ⟨guard, op⟩ := ins
    rw [hs] at h
    cases op <;> cases h
    rfl

private theorem outputStoreModel {l : Launch} {g : Nat} {t : TState} (stage : Fin 2)
    (subbox : Fin 4) (chunk : Fin 8) (hpc : t.pc = outputStorePc stage subbox chunk) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (hpc.symm ▸ outputStoreCode stage subbox chunk) rfl
  all_goals
    rw [hpc]
    have hlo : 8492 ≤ outputStorePc stage subbox chunk := by unfold outputStorePc; omega
    simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites, Assumptions.delayedTmemSites,
      List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- One of the four events of a final correction vector store writes its actual register word
at the byte position used by the output TMA reader. -/
theorem outputStoreElementTemplate {p : Params} {l : Launch} {m : Mem0}
    {g : Nat} {t : TState} (hp : Pre p l m) (stage : Fin 2) (subbox : Fin 4)
    (chunk : Fin 8) (element : Fin 4) (value : Value) (hBytes : value.bytes = 4)
    (hPc : t.pc = outputStorePc stage subbox chunk) (hSub : t.sub = element.val)
    (hFault : t.fault = none)
    (hAddress : t.regs (outputStoreAddrReg stage chunk) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) chunk.val).addr))
    (hWord : t.regs (outputStoreValueReg stage subbox chunk element) = some value)
    : out kernel Assumptions.all l g t = .ev (.write {
      loc := (outputChunkLoc l g stage subbox (rowOf l g) chunk.val).at (4 * element.val)
      size := 4, elem := element.val } value.toBytes
      (afterStore t (outputOperands stage subbox chunk))) := by
  let base := (outputChunkLoc l g stage 0 (rowOf l g) chunk.val).addr
  let a : Acc :=
    { loc := (outputChunkLoc l g stage subbox (rowOf l g) chunk.val).at (4 * element.val)
      size := 4, elem := element.val }
  let srcs := outputOperands stage subbox chunk
  let storage := (⟨.shared, g / l.block, base + 16384 * subbox.val⟩ : Loc)
  have hOffset : (rowOf l g) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hXor : chunk.val ^^^ (rowOf l g) % 8 < 8 :=
    Nat.xor_lt_two_pow (n := 3) chunk.isLt hOffset
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hLimit := hp.shared.2.1
  have hs := stage.isLt
  have hb := subbox.isLt
  have hAddr : base + 16384 * subbox.val < 2 ^ 32 := by
    dsimp [base, outputChunkLoc, Epilogue.sharedSlot, Loc.at]
    omega
  have hAlign : (base + 16384 * subbox.val) % 16 = 0 := by
    have hShared := hp.shared.1
    dsimp [base, outputChunkLoc, Epilogue.sharedSlot, Loc.at]
    omega
  have hStore : storage.at (4 * element.val) = a.loc := by
    simp only [storage, a, base, outputChunkLoc, Epilogue.sharedSlot, Loc.at]
    congr 1
    omega
  have hElem : elemAcc storage (32 / 8) 4 t.sub = .ok a := by
    have ha : storage.addr % (4 * 4) = 0 := hAlign
    unfold elemAcc
    rw [show (32 / 8 : Nat) = 4 by decide]
    simp only [ha, Nat.reduceEqDiff, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
      hSub, hStore, pure, Except.pure]
    rfl
  have hNth : srcs[t.sub]? = some (.reg (outputStoreValueReg stage subbox chunk element)) := by
    change (List.ofFn fun j => Opnd.reg (outputStoreValueReg stage subbox chunk j))[t.sub]? = _
    rw [hSub, List.getElem?_ofFn, dite_eq_left element.isLt]
  have hLen : srcs.length = 4 := List.length_ofFn
  rw [outputStoreModel stage subbox chunk hPc]
  unfold out
  rw [hPc, hFault, outputStoreCode]
  change Out.ev (storeTmpl l g t .shared 32 (outputStoreAddrReg stage chunk)
    (16384 * subbox.val : Nat) srcs) = _
  have hEff : effAddr l g t .shared (outputStoreAddrReg stage chunk)
      (16384 * subbox.val : Nat) = .ok storage := effAddr_b32_off hAddress hAddr
  simp only [storeTmpl, hEff, bind, Except.bind, hLen, hElem, hNth, readValue, readReg,
    hWord, pure, Except.pure]
  rw [storeValue_of_bytes (show value.bytes = 32 / 8 from hBytes)]

theorem observeOutputStoreElement {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} (hp : Pre p l m) (stage : Fin 2) (subbox : Fin 4)
    (chunk : Fin 8) (element : Fin 4) (value : Value) (hBytes : value.bytes = 4)
    (hPc : t.pc = outputStorePc stage subbox chunk) (hSub : t.sub = element.val)
    (hFault : t.fault = none)
    (hAddress : t.regs (outputStoreAddrReg stage chunk) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) chunk.val).addr))
    (hWord : t.regs (outputStoreValueReg stage subbox chunk element) = some value)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    X.get (g, pos) = some ⟨outputStorePc stage subbox chunk,
      .wr {
        loc := (outputChunkLoc l g stage subbox (rowOf l g) chunk.val).at (4 * element.val)
        size := 4, elem := element.val } value.toBytes⟩ ∧
    Run kernel Assumptions.all l g (afterStore t (outputOperands stage subbox chunk))
      ((X.tr g).drop (pos + 1)) none := by
  let a : Acc :=
    {loc := (outputChunkLoc l g stage subbox (rowOf l g) chunk.val).at (4 * element.val)
     size := 4, elem := element.val}
  let srcs := outputOperands stage subbox chunk
  have hn : Next kernel Assumptions.all l g t t (.write a value.toBytes (afterStore t srcs)) :=
    ⟨.refl,outputStoreElementTemplate hp stage subbox chunk element value hBytes hPc hSub
      hFault hAddress hWord⟩
  obtain ⟨e, u, he, hFire, hRun⟩ := hn.continuing_at (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hr
  obtain ⟨rfl, hu⟩ := hFire
  obtain rfl := Option.some.inj hu
  exact ⟨hPc ▸ he, hRun⟩

/-- The complete correction vector store writes all four actual words and preserves the frame. -/
theorem observeOutputStoreChunk {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8) (value : Fin 4 → Value)
    (ht : At t (outputStorePc stage subbox chunk) F)
    (hAddress : t.regs (outputStoreAddrReg stage chunk) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) chunk.val).addr))
    (hValue : ∀ j, t.regs (outputStoreValueReg stage subbox chunk j) = some (value j))
    (hBytes : ∀ j, (value j).bytes = 4)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    (∀ j : Fin 4, X.get (g, pos + j.val) = some ⟨outputStorePc stage subbox chunk,
      .wr {
        loc := (outputChunkLoc l g stage subbox (rowOf l g) chunk.val).at (4 * j.val)
        size := 4, elem := j.val } (value j).toBytes⟩) ∧
    At (next t) (outputStorePc stage subbox chunk + 1) F ∧
    Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos + 4)) none := by
  let state (j : Nat) := if j < 4 then { t with sub := j } else next t
  have hState (j : Fin 4) : state j.val = { t with sub := j.val } := ite_eq_left j.isLt
  have hNext (j : Fin 4) :
      afterStore (state j.val) (outputOperands stage subbox chunk) = state (j.val + 1) := by
    have hLen : (outputOperands stage subbox chunk).length = 4 := List.length_ofFn
    rw [hState]
    simp only [afterStore, hLen, state]
    split
    · rfl
    · rw [next, ht.2.1]
  have step (j : Fin 4)
      (hRun : Run kernel Assumptions.all l g (state j.val) ((X.tr g).drop (pos + j.val)) none) :
      X.get (g, pos + j.val) = some ⟨outputStorePc stage subbox chunk,
        .wr {
          loc := (outputChunkLoc l g stage subbox (rowOf l g) chunk.val).at (4 * j.val)
          size := 4, elem := j.val } (value j).toBytes⟩ ∧
      Run kernel Assumptions.all l g (state (j.val + 1)) ((X.tr g).drop (pos + (j.val + 1)))
        none := by
    have h := observeOutputStoreElement hp stage subbox chunk j (value j) (hBytes j)
      (by rw [hState]; exact ht.1) (by rw [hState]) (by rw [hState]; exact ht.2.2.2.1)
      (by rw [hState]; exact hAddress) (by rw [hState]; exact hValue j) hRun
    simpa only [hNext, Nat.add_assoc] using h
  have hZero : state 0 = t := by
    change { t with sub := 0 } = t
    rw [← ht.2.1]
  have hRun0 : Run kernel Assumptions.all l g (state 0) ((X.tr g).drop (pos + 0)) none := by
    rw [hZero, Nat.add_zero]
    exact hr
  obtain ⟨h0, hRun1⟩ := step 0 hRun0
  obtain ⟨h1, hRun2⟩ := step 1 hRun1
  obtain ⟨h2, hRun3⟩ := step 2 hRun2
  obtain ⟨h3, hRun4⟩ := step 3 hRun3
  refine ⟨?_, ht.next, hRun4⟩
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end
end PTX.Kernels.TmlFa4Fwd.Correction
